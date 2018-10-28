import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;

public class CSPSudokuSolver {

    public static void initUnaryConsitentValues(SudokuNode node, String boardString) {
        int n = node.getState().getBoard().length;
        int k = 0;
        for (int i = 0; i < n; i++){
            for (int j = 0; j < n; j++){
                short v = (short)Character.getNumericValue(boardString.charAt(k++));
                if (v == 0) {
                    for (v = 1; v <= n; v++){
                        node.getGoodValues(i, j).add(v);
                    }
                } else {
                    node.getGoodValues(i, j).add(v);
                }
            }
        }
    }

    public static SudokuVar getUnassignedVar(SudokuNode node) {
        int n = node.getState().getBoard().length;
        if (MRV) {
            // [start:1]
//            throw new UnsupportedOperationException("MRV has not been implemented.");
            int minSize = n+1, row = -1, col = -1;
            for (int i=0; i<n; i++){
                for (int j=0; j<n; j++) {
                    if (node.getState().getBoard()[i][j] == 0) {
                        int currentSize = node.getGoodValues(i, j).size();
                        if (currentSize < minSize) {
                            minSize = currentSize;
                            row = i;
                            col = j;
                        }
                    }
                }
            }
            return new SudokuVar(row, col);
            // [end:1]
        } else {
            // return first unassigned variable
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if (node.getState().getBoard()[i][j] == 0){
                        return new SudokuVar(i, j);
                    }
                }
            }
        }
        return null;
    }

    public static ArrayList<Short> getDomainValues(SudokuNode node, SudokuVar var) {
        if (LCV) {
            throw new UnsupportedOperationException("LCV has not been implemented.");
        } else {
            // return order the the hashset
            ArrayList<Short> values = new ArrayList<>(node.getGoodValues(var.R(), var.C()));
            return values;
        }
    }

    public static HashSet<SudokuVar> getConnectedOpenVariables(SudokuNode node, SudokuVar var, int n){
        int m = (int) Math.sqrt(n);
        short[][] board = node.getState().getBoard();
        HashSet<SudokuVar> vars = new HashSet<>();
        for (int i=0; i<n; i++) {
            if (board[i][var.C()] == 0) {
                vars.add(new SudokuVar(i, var.C()));
            }
            if (board[var.R()][i] == 0){
                vars.add(new SudokuVar(var.R(), i));
            }
            vars.add(new SudokuVar(var.R(), i));
        }
        int boxRow = var.R() - var.R()%m;
        int boxCol = var.C() - var.C()%m;
        for (int i=0; i<m; i++) {
            for (int j=0; j<m; j++) {
                if (board[boxRow+i][boxCol+j] == 0) {
                    vars.add(new SudokuVar(boxRow+i, boxCol+j));
                }
            }
        }
        vars.remove(var);
        return vars;
    }

    public static boolean enforceAC(SudokuNode node, SudokuVar head, SudokuVar tail) {
        // enforce arc consistency, return true if modified available values of the tail
        boolean modified = false;
        // [start:2]

        Set<Short> headSet = node.getGoodValues(head.R(), head.C());
        Set<Short> tailSet = node.getGoodValues(tail.R(), tail.C());
        if (headSet.size() == 1){
            if (tailSet.containsAll(headSet)){
                tailSet.removeAll(headSet);
                modified = true;
            }
        }

        // [end:2]
        return modified;
    }

    public static boolean forwardCheck(SudokuNode node, SudokuVar var) {
        int n = node.getState().getBoard().length;
        // forward checking enforce immediate arcs and returns true if it is still solvable
        // [start:3]
//        throw new UnsupportedOperationException("Forward Checking has not been implemented.");

        boolean check = true;

        Set<SudokuVar> connections = getConnectedOpenVariables(node, var, n);
        for (SudokuVar tail: connections){
            boolean checkAC = enforceAC(node, var, tail);
            if (checkAC) {
                if (node.getGoodValues(tail.R(), tail.C()).size() == 0) check = false;
            }
        }

        return check;
        // [end:3]
    }

    public static boolean MAC(SudokuNode node, SudokuVar var){
        Queue<Arc> arcs = new LinkedList<Arc>();
        int n = node.getState().getBoard().length;
        // MAC enforces arcs and returns true if it is still solvable
        // [start:4]
//        throw new UnsupportedOperationException("MAC has not been implemented.");

        HashSet<SudokuVar> set = getConnectedOpenVariables(node, var, n);
        for (SudokuVar sudokuVar: set) {
            Arc arc = new Arc(var, sudokuVar);
            arcs.add(arc);
        }

        while (arcs.size()!=0) {
            Arc arc = arcs.remove();
            if (enforceAC(node, arc.head, arc.tail)) {
                if (node.getGoodValues(arc.tail.R(), arc.tail.C()).size() == 0) return false;
                HashSet<SudokuVar> new_set = getConnectedOpenVariables(node, arc.tail, n);
                for (SudokuVar sudokuVar: new_set) {
                    Arc new_arc = new Arc(arc.tail, sudokuVar);
                    arcs.add(new_arc);
                }
            }
        }
        return true;
        // [end:4]
    }

    public static boolean inference(SudokuNode node, SudokuVar var) {
        if (!INFER) {
            return true;
        }
        if (MAC) {
            return MAC(node, var);
        } else {
            return forwardCheck(node, var);
        }
    }

    public static SudokuNode backtrackSearch(SudokuNode node, int depth){
        // backtrack search
        // return null if not current node is not solvable
        // otherwise return solved node
        // useful code:
        // - node.getState().isFilled(): return true if completed assignment
        // - node.getState().isSolved(): return true if valid assignment
        // - node.copy(): return a new node.
        //                It is important to copy a node before you assign or recurse
        // - node.assign(row, col, value): assign value to a position. This also sets
        //                                 the possible values of the position to be the value.
        // - if (depth > LIMIT) {return null;}: useful to stop early
        // [start:0]
        if (depth > LIMIT) return null;
        if (node.getState().isFilled()){
            if (node.getState().isSolved()){
                return node;
            }
            return null;
        }
        SudokuVar var = getUnassignedVar(node);
        List<Short> valDomain = getDomainValues(node, var);
        for (Short val: valDomain){
            SudokuNode new_node = node.copy();
            new_node.assign(var.R(), var.C(), val);
            if (inference(new_node, var)){
                new_node = backtrackSearch(new_node, depth+1);
                if (new_node!=null) return new_node;
            }
        }
        // [end:0]
        return null;
    }

    public static SudokuState solve(String boardString) {
        int n = (int) Math.sqrt(boardString.length());
        SudokuNode root = new SudokuNode(new SudokuState(n));
        initUnaryConsitentValues(root, boardString);
        SudokuNode finalNode = backtrackSearch(root, 0);
        if (finalNode != null) return finalNode.getState();
        else return null;

    }

    public static void experiment(long studentId) {
        Random random = new Random(studentId);
        long max = 0;
        long min = Long.MAX_VALUE;
        long sum = 0;
        int count = 0;
        BufferedReader reader;
        ArrayList<String> boards = new ArrayList<>();
        try {
            reader = new BufferedReader(new FileReader("sudoku9.txt"));
            String line;
            while ((line=reader.readLine()) != null) {
                boards.add(line);
            }
            for (int i = 0; i < 50; i++){
                int index = random.nextInt(boards.size());
                String board = boards.get(index);
                System.out.println(boards.get(index).hashCode());   /** Print the selected board**/
                Date startTime = new Date();
                SudokuState solved = solve(board);
                Date endTime = new Date();
                if (solved != null){
                    long time = endTime.getTime() - startTime.getTime();
                    max = Math.max(max, time);
                    min = Math.min(min, time);
                    sum += time;
                    count += 1;
                }
            }
            System.out.println(
                "max: " + max + "ms, min: " + min + "ms avg: " + ((double)sum/(double)count));
        } catch (IOException e) {
            e.printStackTrace();
		}

    }

    public static int LIMIT = 9*9+1;  // helpful for debugging
    public static boolean MAC = true;
    public static boolean MRV = true;
    public static boolean INFER = true;
    public static boolean LCV = false;  // not required

    public static void main(String[] args) {
        long studentId = 5988222;
//        String testBoard = "0200000203404000";
//         String testBoard = "000020040008035000000070602031046970200000000000501203049000730000000010800004000";
//        Date startTime = new Date();
//        SudokuState solved = solve(testBoard);
//        Date endTime = new Date();
//        if (solved != null) {
//            System.out.println(solved);
//            System.out.println("Solved in " + (endTime.getTime() - startTime.getTime()) + "ms");
//        }
         experiment(studentId);
    }

}

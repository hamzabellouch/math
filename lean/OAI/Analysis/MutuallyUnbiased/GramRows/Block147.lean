import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15744 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1121, -2), (key1148, 6), (key994, -2), (key999, -2), (key1013, -2), (key1029, 2), (key1034, 2), (key1107, 2), (key1191, 2), (key1121, 2), (key1197, 2), (key1069, -2), (key1148, -2), (key1210, -2), (key999, 6), (key1034, -2), (key1112, -2), (key1191, -2)]

theorem rawRowCheck15744 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form1 = rawRow15744 := by decide +kernel

def row15744 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15744 : row15744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15744 := by decide +kernel

theorem rowEval15744 (x : Key → ℝ) : Integer.Sparse.eval row15744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15744, Integer.Sparse.eval_collectBalanced, rawRowCheck15744]

def rawRow15745 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1121, -2), (key1148, 6), (key999, -2), (key994, -2), (key1013, -2), (key1034, 2), (key1029, 2), (key1191, 2), (key1107, 2), (key1197, 2), (key1121, 2), (key1069, -2), (key1210, -2), (key1148, -2), (key999, 6), (key1034, -2), (key1191, -2), (key1112, -2)]

theorem rawRowCheck15745 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form1 = rawRow15745 := by decide +kernel

def row15745 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15745 : row15745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15745 := by decide +kernel

theorem rowEval15745 (x : Key → ℝ) : Integer.Sparse.eval row15745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15745, Integer.Sparse.eval_collectBalanced, rawRowCheck15745]

def rawRow15746 : Integer.Sparse Key := [(key1107, -2), (key1121, -2), (key1112, -2), (key1148, 6), (key994, -2), (key1013, -2), (key999, -2), (key1107, 2), (key1121, 2), (key1029, 2), (key1197, 2), (key1034, 2), (key1191, 2), (key1148, -2), (key1069, -2), (key1210, -2), (key999, 6), (key1112, -2), (key1034, -2), (key1191, -2)]

theorem rawRowCheck15746 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form1 = rawRow15746 := by decide +kernel

def row15746 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15746 : row15746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15746 := by decide +kernel

theorem rowEval15746 (x : Key → ℝ) : Integer.Sparse.eval row15746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15746, Integer.Sparse.eval_collectBalanced, rawRowCheck15746]

def rawRow15747 : Integer.Sparse Key := [(key1121, -2), (key1107, -2), (key1112, -2), (key1148, 6), (key1013, -2), (key994, -2), (key999, -2), (key1121, 2), (key1107, 2), (key1197, 2), (key1029, 2), (key1191, 2), (key1034, 2), (key1148, -2), (key1210, -2), (key1069, -2), (key999, 6), (key1112, -2), (key1191, -2), (key1034, -2)]

theorem rawRowCheck15747 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form1 = rawRow15747 := by decide +kernel

def row15747 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15747 : row15747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15747 := by decide +kernel

theorem rowEval15747 (x : Key → ℝ) : Integer.Sparse.eval row15747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15747, Integer.Sparse.eval_collectBalanced, rawRowCheck15747]

def rawRow15748 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1107, -2), (key1148, 6), (key999, -2), (key1013, -2), (key994, -2), (key1191, 2), (key1197, 2), (key1034, 2), (key1121, 2), (key1029, 2), (key1107, 2), (key1210, -2), (key1069, -2), (key1148, -2), (key999, 6), (key1191, -2), (key1034, -2), (key1112, -2)]

theorem rawRowCheck15748 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form1 = rawRow15748 := by decide +kernel

def row15748 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15748 : row15748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15748 := by decide +kernel

theorem rowEval15748 (x : Key → ℝ) : Integer.Sparse.eval row15748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15748, Integer.Sparse.eval_collectBalanced, rawRowCheck15748]

def rawRow15749 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1107, -2), (key1148, 6), (key1013, -2), (key999, -2), (key994, -2), (key1197, 2), (key1191, 2), (key1121, 2), (key1034, 2), (key1107, 2), (key1029, 2), (key1210, -2), (key1148, -2), (key1069, -2), (key999, 6), (key1191, -2), (key1112, -2), (key1034, -2)]

theorem rawRowCheck15749 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form1 = rawRow15749 := by decide +kernel

def row15749 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15749 : row15749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15749 := by decide +kernel

theorem rowEval15749 (x : Key → ℝ) : Integer.Sparse.eval row15749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15749, Integer.Sparse.eval_collectBalanced, rawRowCheck15749]

def rawRow15750 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1197, -2), (key1210, 6), (key999, -2), (key999, -2), (key1013, -2), (key1034, 2), (key1034, 2), (key1112, 2), (key1112, 2), (key1121, 2), (key1121, 2), (key1069, -2), (key1148, -2), (key1148, -2), (key994, 6), (key1029, -2), (key1107, -2), (key1107, -2)]

theorem rawRowCheck15750 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form1 = rawRow15750 := by decide +kernel

def row15750 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

theorem rowCheck15750 : row15750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15750 := by decide +kernel

theorem rowEval15750 (x : Key → ℝ) : Integer.Sparse.eval row15750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15750, Integer.Sparse.eval_collectBalanced, rawRowCheck15750]

def rawRow15751 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1191, -2), (key1210, 6), (key999, -2), (key1013, -2), (key999, -2), (key1112, 2), (key1121, 2), (key1034, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1148, -2), (key1069, -2), (key1148, -2), (key994, 6), (key1107, -2), (key1029, -2), (key1107, -2)]

theorem rawRowCheck15751 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form1 = rawRow15751 := by decide +kernel

def row15751 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

theorem rowCheck15751 : row15751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15751 := by decide +kernel

theorem rowEval15751 (x : Key → ℝ) : Integer.Sparse.eval row15751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15751, Integer.Sparse.eval_collectBalanced, rawRowCheck15751]

def rawRow15752 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1191, -2), (key1210, 6), (key1013, -2), (key999, -2), (key999, -2), (key1121, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1034, 2), (key1148, -2), (key1148, -2), (key1069, -2), (key994, 6), (key1107, -2), (key1107, -2), (key1029, -2)]

theorem rawRowCheck15752 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form1 = rawRow15752 := by decide +kernel

def row15752 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

theorem rowCheck15752 : row15752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15752 := by decide +kernel

theorem rowEval15752 (x : Key → ℝ) : Integer.Sparse.eval row15752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15752, Integer.Sparse.eval_collectBalanced, rawRowCheck15752]

def rawRow15753 : Integer.Sparse Key := [(key2371, -2), (key2375, -2), (key2387, -2), (key2375, 6), (key2465, -2), (key2469, -2), (key2477, -2), (key2399, 2), (key2403, 2), (key2465, 2), (key2536, 2), (key2477, 2), (key2541, 2), (key2403, -2), (key2469, -2), (key2536, -2), (key2500, 6), (key2434, -2), (key2500, -2), (key2552, -2)]

theorem rawRowCheck15753 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form2 = rawRow15753 := by decide +kernel

def row15753 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15753 : row15753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15753 := by decide +kernel

theorem rowEval15753 (x : Key → ℝ) : Integer.Sparse.eval row15753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15753, Integer.Sparse.eval_collectBalanced, rawRowCheck15753]

def rawRow15754 : Integer.Sparse Key := [(key2375, -2), (key2371, -2), (key2387, -2), (key2375, 6), (key2469, -2), (key2465, -2), (key2477, -2), (key2403, 2), (key2399, 2), (key2536, 2), (key2465, 2), (key2541, 2), (key2477, 2), (key2403, -2), (key2536, -2), (key2469, -2), (key2500, 6), (key2434, -2), (key2552, -2), (key2500, -2)]

theorem rawRowCheck15754 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form2 = rawRow15754 := by decide +kernel

def row15754 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15754 : row15754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15754 := by decide +kernel

theorem rowEval15754 (x : Key → ℝ) : Integer.Sparse.eval row15754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15754, Integer.Sparse.eval_collectBalanced, rawRowCheck15754]

def rawRow15755 : Integer.Sparse Key := [(key2371, -2), (key2387, -2), (key2375, -2), (key2375, 6), (key2465, -2), (key2477, -2), (key2469, -2), (key2465, 2), (key2477, 2), (key2399, 2), (key2541, 2), (key2403, 2), (key2536, 2), (key2469, -2), (key2403, -2), (key2536, -2), (key2500, 6), (key2500, -2), (key2434, -2), (key2552, -2)]

theorem rawRowCheck15755 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form2 = rawRow15755 := by decide +kernel

def row15755 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15755 : row15755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15755 := by decide +kernel

theorem rowEval15755 (x : Key → ℝ) : Integer.Sparse.eval row15755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15755, Integer.Sparse.eval_collectBalanced, rawRowCheck15755]

def rawRow15756 : Integer.Sparse Key := [(key2387, -2), (key2371, -2), (key2375, -2), (key2375, 6), (key2477, -2), (key2465, -2), (key2469, -2), (key2477, 2), (key2465, 2), (key2541, 2), (key2399, 2), (key2536, 2), (key2403, 2), (key2469, -2), (key2536, -2), (key2403, -2), (key2500, 6), (key2500, -2), (key2552, -2), (key2434, -2)]

theorem rawRowCheck15756 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form2 = rawRow15756 := by decide +kernel

def row15756 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15756 : row15756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15756 := by decide +kernel

theorem rowEval15756 (x : Key → ℝ) : Integer.Sparse.eval row15756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15756, Integer.Sparse.eval_collectBalanced, rawRowCheck15756]

def rawRow15757 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2371, -2), (key2375, 6), (key2469, -2), (key2477, -2), (key2465, -2), (key2536, 2), (key2541, 2), (key2403, 2), (key2477, 2), (key2399, 2), (key2465, 2), (key2536, -2), (key2403, -2), (key2469, -2), (key2500, 6), (key2552, -2), (key2434, -2), (key2500, -2)]

theorem rawRowCheck15757 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form2 = rawRow15757 := by decide +kernel

def row15757 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15757 : row15757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15757 := by decide +kernel

theorem rowEval15757 (x : Key → ℝ) : Integer.Sparse.eval row15757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15757, Integer.Sparse.eval_collectBalanced, rawRowCheck15757]

def rawRow15758 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2371, -2), (key2375, 6), (key2477, -2), (key2469, -2), (key2465, -2), (key2541, 2), (key2536, 2), (key2477, 2), (key2403, 2), (key2465, 2), (key2399, 2), (key2536, -2), (key2469, -2), (key2403, -2), (key2500, 6), (key2552, -2), (key2500, -2), (key2434, -2)]

theorem rawRowCheck15758 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form2 = rawRow15758 := by decide +kernel

def row15758 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15758 : row15758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15758 := by decide +kernel

theorem rowEval15758 (x : Key → ℝ) : Integer.Sparse.eval row15758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15758, Integer.Sparse.eval_collectBalanced, rawRowCheck15758]

def rawRow15759 : Integer.Sparse Key := [(key2375, -2), (key2375, -2), (key2387, -2), (key2371, 6), (key2536, -2), (key2536, -2), (key2541, -2), (key2403, 2), (key2403, 2), (key2469, 2), (key2469, 2), (key2477, 2), (key2477, 2), (key2399, -2), (key2465, -2), (key2465, -2), (key2552, 6), (key2434, -2), (key2500, -2), (key2500, -2)]

theorem rawRowCheck15759 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form2 = rawRow15759 := by decide +kernel

def row15759 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

theorem rowCheck15759 : row15759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15759 := by decide +kernel

theorem rowEval15759 (x : Key → ℝ) : Integer.Sparse.eval row15759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15759, Integer.Sparse.eval_collectBalanced, rawRowCheck15759]

def rawRow15760 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2375, -2), (key2371, 6), (key2536, -2), (key2541, -2), (key2536, -2), (key2469, 2), (key2477, 2), (key2403, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2465, -2), (key2399, -2), (key2465, -2), (key2552, 6), (key2500, -2), (key2434, -2), (key2500, -2)]

theorem rawRowCheck15760 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form2 = rawRow15760 := by decide +kernel

def row15760 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

theorem rowCheck15760 : row15760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15760 := by decide +kernel

theorem rowEval15760 (x : Key → ℝ) : Integer.Sparse.eval row15760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15760, Integer.Sparse.eval_collectBalanced, rawRowCheck15760]

def rawRow15761 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2375, -2), (key2371, 6), (key2541, -2), (key2536, -2), (key2536, -2), (key2477, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2403, 2), (key2465, -2), (key2465, -2), (key2399, -2), (key2552, 6), (key2500, -2), (key2500, -2), (key2434, -2)]

theorem rawRowCheck15761 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form2 = rawRow15761 := by decide +kernel

def row15761 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

theorem rowCheck15761 : row15761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15761 := by decide +kernel

theorem rowEval15761 (x : Key → ℝ) : Integer.Sparse.eval row15761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15761, Integer.Sparse.eval_collectBalanced, rawRowCheck15761]

def rawRow15762 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2477, -2), (key2500, 6), (key2371, -2), (key2375, -2), (key2387, -2), (key2399, 2), (key2403, 2), (key2465, 2), (key2536, 2), (key2477, 2), (key2541, 2), (key2434, -2), (key2500, -2), (key2552, -2), (key2375, 6), (key2403, -2), (key2469, -2), (key2536, -2)]

theorem rawRowCheck15762 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form2 = rawRow15762 := by decide +kernel

def row15762 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15762 : row15762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15762 := by decide +kernel

theorem rowEval15762 (x : Key → ℝ) : Integer.Sparse.eval row15762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15762, Integer.Sparse.eval_collectBalanced, rawRowCheck15762]

def rawRow15763 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2477, -2), (key2500, 6), (key2375, -2), (key2371, -2), (key2387, -2), (key2403, 2), (key2399, 2), (key2536, 2), (key2465, 2), (key2541, 2), (key2477, 2), (key2434, -2), (key2552, -2), (key2500, -2), (key2375, 6), (key2403, -2), (key2536, -2), (key2469, -2)]

theorem rawRowCheck15763 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form2 = rawRow15763 := by decide +kernel

def row15763 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15763 : row15763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15763 := by decide +kernel

theorem rowEval15763 (x : Key → ℝ) : Integer.Sparse.eval row15763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15763, Integer.Sparse.eval_collectBalanced, rawRowCheck15763]

def rawRow15764 : Integer.Sparse Key := [(key2465, -2), (key2477, -2), (key2469, -2), (key2500, 6), (key2371, -2), (key2387, -2), (key2375, -2), (key2465, 2), (key2477, 2), (key2399, 2), (key2541, 2), (key2403, 2), (key2536, 2), (key2500, -2), (key2434, -2), (key2552, -2), (key2375, 6), (key2469, -2), (key2403, -2), (key2536, -2)]

theorem rawRowCheck15764 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form2 = rawRow15764 := by decide +kernel

def row15764 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15764 : row15764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15764 := by decide +kernel

theorem rowEval15764 (x : Key → ℝ) : Integer.Sparse.eval row15764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15764, Integer.Sparse.eval_collectBalanced, rawRowCheck15764]

def rawRow15765 : Integer.Sparse Key := [(key2477, -2), (key2465, -2), (key2469, -2), (key2500, 6), (key2387, -2), (key2371, -2), (key2375, -2), (key2477, 2), (key2465, 2), (key2541, 2), (key2399, 2), (key2536, 2), (key2403, 2), (key2500, -2), (key2552, -2), (key2434, -2), (key2375, 6), (key2469, -2), (key2536, -2), (key2403, -2)]

theorem rawRowCheck15765 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form2 = rawRow15765 := by decide +kernel

def row15765 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15765 : row15765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15765 := by decide +kernel

theorem rowEval15765 (x : Key → ℝ) : Integer.Sparse.eval row15765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15765, Integer.Sparse.eval_collectBalanced, rawRowCheck15765]

def rawRow15766 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2465, -2), (key2500, 6), (key2375, -2), (key2387, -2), (key2371, -2), (key2536, 2), (key2541, 2), (key2403, 2), (key2477, 2), (key2399, 2), (key2465, 2), (key2552, -2), (key2434, -2), (key2500, -2), (key2375, 6), (key2536, -2), (key2403, -2), (key2469, -2)]

theorem rawRowCheck15766 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form2 = rawRow15766 := by decide +kernel

def row15766 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15766 : row15766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15766 := by decide +kernel

theorem rowEval15766 (x : Key → ℝ) : Integer.Sparse.eval row15766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15766, Integer.Sparse.eval_collectBalanced, rawRowCheck15766]

def rawRow15767 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2465, -2), (key2500, 6), (key2387, -2), (key2375, -2), (key2371, -2), (key2541, 2), (key2536, 2), (key2477, 2), (key2403, 2), (key2465, 2), (key2399, 2), (key2552, -2), (key2500, -2), (key2434, -2), (key2375, 6), (key2536, -2), (key2469, -2), (key2403, -2)]

theorem rawRowCheck15767 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form2 = rawRow15767 := by decide +kernel

def row15767 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

theorem rowCheck15767 : row15767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15767 := by decide +kernel

theorem rowEval15767 (x : Key → ℝ) : Integer.Sparse.eval row15767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15767, Integer.Sparse.eval_collectBalanced, rawRowCheck15767]

def rawRow15768 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2541, -2), (key2552, 6), (key2375, -2), (key2375, -2), (key2387, -2), (key2403, 2), (key2403, 2), (key2469, 2), (key2469, 2), (key2477, 2), (key2477, 2), (key2434, -2), (key2500, -2), (key2500, -2), (key2371, 6), (key2399, -2), (key2465, -2), (key2465, -2)]

theorem rawRowCheck15768 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form2 = rawRow15768 := by decide +kernel

def row15768 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

theorem rowCheck15768 : row15768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15768 := by decide +kernel

theorem rowEval15768 (x : Key → ℝ) : Integer.Sparse.eval row15768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15768, Integer.Sparse.eval_collectBalanced, rawRowCheck15768]

def rawRow15769 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2536, -2), (key2552, 6), (key2375, -2), (key2387, -2), (key2375, -2), (key2469, 2), (key2477, 2), (key2403, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2500, -2), (key2434, -2), (key2500, -2), (key2371, 6), (key2465, -2), (key2399, -2), (key2465, -2)]

theorem rawRowCheck15769 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form2 = rawRow15769 := by decide +kernel

def row15769 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

theorem rowCheck15769 : row15769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15769 := by decide +kernel

theorem rowEval15769 (x : Key → ℝ) : Integer.Sparse.eval row15769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15769, Integer.Sparse.eval_collectBalanced, rawRowCheck15769]

def rawRow15770 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2536, -2), (key2552, 6), (key2387, -2), (key2375, -2), (key2375, -2), (key2477, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2403, 2), (key2500, -2), (key2500, -2), (key2434, -2), (key2371, 6), (key2465, -2), (key2465, -2), (key2399, -2)]

theorem rawRowCheck15770 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form2 = rawRow15770 := by decide +kernel

def row15770 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

theorem rowCheck15770 : row15770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15770 := by decide +kernel

theorem rowEval15770 (x : Key → ℝ) : Integer.Sparse.eval row15770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15770, Integer.Sparse.eval_collectBalanced, rawRowCheck15770]

def rawRow15771 : Integer.Sparse Key := [(key2623, 6), (key2607, -2), (key2623, -2), (key2634, -2), (key2697, 6), (key2662, -2), (key2697, -2), (key2720, -2), (key2800, -2), (key2850, -2), (key2854, -2), (key2777, -2), (key2850, -2), (key2864, -2), (key2777, 2), (key2788, 2), (key2800, 2), (key2823, 2), (key2854, 2), (key2864, 2)]

theorem rawRowCheck15771 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form3 = rawRow15771 := by decide +kernel

def row15771 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15771 : row15771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15771 := by decide +kernel

theorem rowEval15771 (x : Key → ℝ) : Integer.Sparse.eval row15771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15771, Integer.Sparse.eval_collectBalanced, rawRowCheck15771]

def rawRow15772 : Integer.Sparse Key := [(key2623, 6), (key2607, -2), (key2634, -2), (key2623, -2), (key2697, 6), (key2662, -2), (key2720, -2), (key2697, -2), (key2800, -2), (key2854, -2), (key2850, -2), (key2777, -2), (key2864, -2), (key2850, -2), (key2788, 2), (key2777, 2), (key2823, 2), (key2800, 2), (key2864, 2), (key2854, 2)]

theorem rawRowCheck15772 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form3 = rawRow15772 := by decide +kernel

def row15772 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15772 : row15772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15772 := by decide +kernel

theorem rowEval15772 (x : Key → ℝ) : Integer.Sparse.eval row15772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15772, Integer.Sparse.eval_collectBalanced, rawRowCheck15772]

def rawRow15773 : Integer.Sparse Key := [(key2623, 6), (key2623, -2), (key2607, -2), (key2634, -2), (key2697, 6), (key2697, -2), (key2662, -2), (key2720, -2), (key2850, -2), (key2800, -2), (key2854, -2), (key2850, -2), (key2777, -2), (key2864, -2), (key2800, 2), (key2854, 2), (key2777, 2), (key2864, 2), (key2788, 2), (key2823, 2)]

theorem rawRowCheck15773 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form3 = rawRow15773 := by decide +kernel

def row15773 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15773 : row15773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15773 := by decide +kernel

theorem rowEval15773 (x : Key → ℝ) : Integer.Sparse.eval row15773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15773, Integer.Sparse.eval_collectBalanced, rawRowCheck15773]

def rawRow15774 : Integer.Sparse Key := [(key2623, 6), (key2623, -2), (key2634, -2), (key2607, -2), (key2697, 6), (key2697, -2), (key2720, -2), (key2662, -2), (key2850, -2), (key2854, -2), (key2800, -2), (key2850, -2), (key2864, -2), (key2777, -2), (key2854, 2), (key2800, 2), (key2864, 2), (key2777, 2), (key2823, 2), (key2788, 2)]

theorem rawRowCheck15774 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form3 = rawRow15774 := by decide +kernel

def row15774 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15774 : row15774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15774 := by decide +kernel

theorem rowEval15774 (x : Key → ℝ) : Integer.Sparse.eval row15774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15774, Integer.Sparse.eval_collectBalanced, rawRowCheck15774]

def rawRow15775 : Integer.Sparse Key := [(key2623, 6), (key2634, -2), (key2607, -2), (key2623, -2), (key2697, 6), (key2720, -2), (key2662, -2), (key2697, -2), (key2854, -2), (key2800, -2), (key2850, -2), (key2864, -2), (key2777, -2), (key2850, -2), (key2823, 2), (key2864, 2), (key2788, 2), (key2854, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck15775 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form3 = rawRow15775 := by decide +kernel

def row15775 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15775 : row15775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15775 := by decide +kernel

theorem rowEval15775 (x : Key → ℝ) : Integer.Sparse.eval row15775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15775, Integer.Sparse.eval_collectBalanced, rawRowCheck15775]

def rawRow15776 : Integer.Sparse Key := [(key2623, 6), (key2634, -2), (key2623, -2), (key2607, -2), (key2697, 6), (key2720, -2), (key2697, -2), (key2662, -2), (key2854, -2), (key2850, -2), (key2800, -2), (key2864, -2), (key2850, -2), (key2777, -2), (key2864, 2), (key2823, 2), (key2854, 2), (key2788, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck15776 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form3 = rawRow15776 := by decide +kernel

def row15776 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15776 : row15776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15776 := by decide +kernel

theorem rowEval15776 (x : Key → ℝ) : Integer.Sparse.eval row15776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15776, Integer.Sparse.eval_collectBalanced, rawRowCheck15776]

def rawRow15777 : Integer.Sparse Key := [(key2634, 6), (key2607, -2), (key2623, -2), (key2623, -2), (key2720, 6), (key2662, -2), (key2697, -2), (key2697, -2), (key2823, -2), (key2864, -2), (key2864, -2), (key2788, -2), (key2854, -2), (key2854, -2), (key2777, 2), (key2777, 2), (key2800, 2), (key2800, 2), (key2850, 2), (key2850, 2)]

theorem rawRowCheck15777 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form3 = rawRow15777 := by decide +kernel

def row15777 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck15777 : row15777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15777 := by decide +kernel

theorem rowEval15777 (x : Key → ℝ) : Integer.Sparse.eval row15777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15777, Integer.Sparse.eval_collectBalanced, rawRowCheck15777]

def rawRow15778 : Integer.Sparse Key := [(key2634, 6), (key2623, -2), (key2607, -2), (key2623, -2), (key2720, 6), (key2697, -2), (key2662, -2), (key2697, -2), (key2864, -2), (key2823, -2), (key2864, -2), (key2854, -2), (key2788, -2), (key2854, -2), (key2800, 2), (key2850, 2), (key2777, 2), (key2850, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck15778 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form3 = rawRow15778 := by decide +kernel

def row15778 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck15778 : row15778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15778 := by decide +kernel

theorem rowEval15778 (x : Key → ℝ) : Integer.Sparse.eval row15778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15778, Integer.Sparse.eval_collectBalanced, rawRowCheck15778]

def rawRow15779 : Integer.Sparse Key := [(key2634, 6), (key2623, -2), (key2623, -2), (key2607, -2), (key2720, 6), (key2697, -2), (key2697, -2), (key2662, -2), (key2864, -2), (key2864, -2), (key2823, -2), (key2854, -2), (key2854, -2), (key2788, -2), (key2850, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck15779 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form3 = rawRow15779 := by decide +kernel

def row15779 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck15779 : row15779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15779 := by decide +kernel

theorem rowEval15779 (x : Key → ℝ) : Integer.Sparse.eval row15779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15779, Integer.Sparse.eval_collectBalanced, rawRowCheck15779]

def rawRow15780 : Integer.Sparse Key := [(key2697, 6), (key2800, -2), (key2850, -2), (key2854, -2), (key2623, 6), (key2777, -2), (key2850, -2), (key2864, -2), (key2607, -2), (key2623, -2), (key2634, -2), (key2662, -2), (key2697, -2), (key2720, -2), (key2777, 2), (key2788, 2), (key2800, 2), (key2823, 2), (key2854, 2), (key2864, 2)]

theorem rawRowCheck15780 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form3 = rawRow15780 := by decide +kernel

def row15780 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15780 : row15780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15780 := by decide +kernel

theorem rowEval15780 (x : Key → ℝ) : Integer.Sparse.eval row15780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15780, Integer.Sparse.eval_collectBalanced, rawRowCheck15780]

def rawRow15781 : Integer.Sparse Key := [(key2697, 6), (key2800, -2), (key2854, -2), (key2850, -2), (key2623, 6), (key2777, -2), (key2864, -2), (key2850, -2), (key2607, -2), (key2634, -2), (key2623, -2), (key2662, -2), (key2720, -2), (key2697, -2), (key2788, 2), (key2777, 2), (key2823, 2), (key2800, 2), (key2864, 2), (key2854, 2)]

theorem rawRowCheck15781 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form3 = rawRow15781 := by decide +kernel

def row15781 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15781 : row15781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15781 := by decide +kernel

theorem rowEval15781 (x : Key → ℝ) : Integer.Sparse.eval row15781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15781, Integer.Sparse.eval_collectBalanced, rawRowCheck15781]

def rawRow15782 : Integer.Sparse Key := [(key2697, 6), (key2850, -2), (key2800, -2), (key2854, -2), (key2623, 6), (key2850, -2), (key2777, -2), (key2864, -2), (key2623, -2), (key2607, -2), (key2634, -2), (key2697, -2), (key2662, -2), (key2720, -2), (key2800, 2), (key2854, 2), (key2777, 2), (key2864, 2), (key2788, 2), (key2823, 2)]

theorem rawRowCheck15782 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form3 = rawRow15782 := by decide +kernel

def row15782 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15782 : row15782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15782 := by decide +kernel

theorem rowEval15782 (x : Key → ℝ) : Integer.Sparse.eval row15782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15782, Integer.Sparse.eval_collectBalanced, rawRowCheck15782]

def rawRow15783 : Integer.Sparse Key := [(key2697, 6), (key2850, -2), (key2854, -2), (key2800, -2), (key2623, 6), (key2850, -2), (key2864, -2), (key2777, -2), (key2623, -2), (key2634, -2), (key2607, -2), (key2697, -2), (key2720, -2), (key2662, -2), (key2854, 2), (key2800, 2), (key2864, 2), (key2777, 2), (key2823, 2), (key2788, 2)]

theorem rawRowCheck15783 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form3 = rawRow15783 := by decide +kernel

def row15783 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15783 : row15783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15783 := by decide +kernel

theorem rowEval15783 (x : Key → ℝ) : Integer.Sparse.eval row15783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15783, Integer.Sparse.eval_collectBalanced, rawRowCheck15783]

def rawRow15784 : Integer.Sparse Key := [(key2697, 6), (key2854, -2), (key2800, -2), (key2850, -2), (key2623, 6), (key2864, -2), (key2777, -2), (key2850, -2), (key2634, -2), (key2607, -2), (key2623, -2), (key2720, -2), (key2662, -2), (key2697, -2), (key2823, 2), (key2864, 2), (key2788, 2), (key2854, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck15784 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form3 = rawRow15784 := by decide +kernel

def row15784 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15784 : row15784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15784 := by decide +kernel

theorem rowEval15784 (x : Key → ℝ) : Integer.Sparse.eval row15784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15784, Integer.Sparse.eval_collectBalanced, rawRowCheck15784]

def rawRow15785 : Integer.Sparse Key := [(key2697, 6), (key2854, -2), (key2850, -2), (key2800, -2), (key2623, 6), (key2864, -2), (key2850, -2), (key2777, -2), (key2634, -2), (key2623, -2), (key2607, -2), (key2720, -2), (key2697, -2), (key2662, -2), (key2864, 2), (key2823, 2), (key2854, 2), (key2788, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck15785 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form3 = rawRow15785 := by decide +kernel

def row15785 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

theorem rowCheck15785 : row15785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15785 := by decide +kernel

theorem rowEval15785 (x : Key → ℝ) : Integer.Sparse.eval row15785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15785, Integer.Sparse.eval_collectBalanced, rawRowCheck15785]

def rawRow15786 : Integer.Sparse Key := [(key2720, 6), (key2823, -2), (key2864, -2), (key2864, -2), (key2634, 6), (key2788, -2), (key2854, -2), (key2854, -2), (key2607, -2), (key2623, -2), (key2623, -2), (key2662, -2), (key2697, -2), (key2697, -2), (key2777, 2), (key2777, 2), (key2800, 2), (key2800, 2), (key2850, 2), (key2850, 2)]

theorem rawRowCheck15786 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form3 = rawRow15786 := by decide +kernel

def row15786 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck15786 : row15786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15786 := by decide +kernel

theorem rowEval15786 (x : Key → ℝ) : Integer.Sparse.eval row15786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15786, Integer.Sparse.eval_collectBalanced, rawRowCheck15786]

def rawRow15787 : Integer.Sparse Key := [(key2720, 6), (key2864, -2), (key2823, -2), (key2864, -2), (key2634, 6), (key2854, -2), (key2788, -2), (key2854, -2), (key2623, -2), (key2607, -2), (key2623, -2), (key2697, -2), (key2662, -2), (key2697, -2), (key2800, 2), (key2850, 2), (key2777, 2), (key2850, 2), (key2777, 2), (key2800, 2)]

theorem rawRowCheck15787 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form3 = rawRow15787 := by decide +kernel

def row15787 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck15787 : row15787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15787 := by decide +kernel

theorem rowEval15787 (x : Key → ℝ) : Integer.Sparse.eval row15787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15787, Integer.Sparse.eval_collectBalanced, rawRowCheck15787]

def rawRow15788 : Integer.Sparse Key := [(key2720, 6), (key2864, -2), (key2864, -2), (key2823, -2), (key2634, 6), (key2854, -2), (key2854, -2), (key2788, -2), (key2623, -2), (key2623, -2), (key2607, -2), (key2697, -2), (key2697, -2), (key2662, -2), (key2850, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2800, 2), (key2777, 2)]

theorem rawRowCheck15788 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form3 = rawRow15788 := by decide +kernel

def row15788 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

theorem rowCheck15788 : row15788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15788 := by decide +kernel

theorem rowEval15788 (x : Key → ℝ) : Integer.Sparse.eval row15788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15788, Integer.Sparse.eval_collectBalanced, rawRowCheck15788]

def rawRow15789 : Integer.Sparse Key := [(key993, -2), (key997, -2), (key1012, -2), (key997, 6), (key1106, -2), (key1110, -2), (key1120, -2), (key1028, 2), (key1032, 2), (key1106, 2), (key1189, 2), (key1120, 2), (key1196, 2), (key1032, -2), (key1110, -2), (key1189, -2), (key1147, 6), (key1068, -2), (key1147, -2), (key1209, -2)]

theorem rawRowCheck15789 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form4 = rawRow15789 := by decide +kernel

def row15789 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15789 : row15789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15789 := by decide +kernel

theorem rowEval15789 (x : Key → ℝ) : Integer.Sparse.eval row15789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15789, Integer.Sparse.eval_collectBalanced, rawRowCheck15789]

def rawRow15790 : Integer.Sparse Key := [(key997, -2), (key993, -2), (key1012, -2), (key997, 6), (key1110, -2), (key1106, -2), (key1120, -2), (key1032, 2), (key1028, 2), (key1189, 2), (key1106, 2), (key1196, 2), (key1120, 2), (key1032, -2), (key1189, -2), (key1110, -2), (key1147, 6), (key1068, -2), (key1209, -2), (key1147, -2)]

theorem rawRowCheck15790 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form4 = rawRow15790 := by decide +kernel

def row15790 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15790 : row15790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15790 := by decide +kernel

theorem rowEval15790 (x : Key → ℝ) : Integer.Sparse.eval row15790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15790, Integer.Sparse.eval_collectBalanced, rawRowCheck15790]

def rawRow15791 : Integer.Sparse Key := [(key993, -2), (key1012, -2), (key997, -2), (key997, 6), (key1106, -2), (key1120, -2), (key1110, -2), (key1106, 2), (key1120, 2), (key1028, 2), (key1196, 2), (key1032, 2), (key1189, 2), (key1110, -2), (key1032, -2), (key1189, -2), (key1147, 6), (key1147, -2), (key1068, -2), (key1209, -2)]

theorem rawRowCheck15791 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form4 = rawRow15791 := by decide +kernel

def row15791 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15791 : row15791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15791 := by decide +kernel

theorem rowEval15791 (x : Key → ℝ) : Integer.Sparse.eval row15791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15791, Integer.Sparse.eval_collectBalanced, rawRowCheck15791]

def rawRow15792 : Integer.Sparse Key := [(key1012, -2), (key993, -2), (key997, -2), (key997, 6), (key1120, -2), (key1106, -2), (key1110, -2), (key1120, 2), (key1106, 2), (key1196, 2), (key1028, 2), (key1189, 2), (key1032, 2), (key1110, -2), (key1189, -2), (key1032, -2), (key1147, 6), (key1147, -2), (key1209, -2), (key1068, -2)]

theorem rawRowCheck15792 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form4 = rawRow15792 := by decide +kernel

def row15792 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15792 : row15792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15792 := by decide +kernel

theorem rowEval15792 (x : Key → ℝ) : Integer.Sparse.eval row15792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15792, Integer.Sparse.eval_collectBalanced, rawRowCheck15792]

def rawRow15793 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key993, -2), (key997, 6), (key1110, -2), (key1120, -2), (key1106, -2), (key1189, 2), (key1196, 2), (key1032, 2), (key1120, 2), (key1028, 2), (key1106, 2), (key1189, -2), (key1032, -2), (key1110, -2), (key1147, 6), (key1209, -2), (key1068, -2), (key1147, -2)]

theorem rawRowCheck15793 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form4 = rawRow15793 := by decide +kernel

def row15793 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15793 : row15793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15793 := by decide +kernel

theorem rowEval15793 (x : Key → ℝ) : Integer.Sparse.eval row15793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15793, Integer.Sparse.eval_collectBalanced, rawRowCheck15793]

def rawRow15794 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key993, -2), (key997, 6), (key1120, -2), (key1110, -2), (key1106, -2), (key1196, 2), (key1189, 2), (key1120, 2), (key1032, 2), (key1106, 2), (key1028, 2), (key1189, -2), (key1110, -2), (key1032, -2), (key1147, 6), (key1209, -2), (key1147, -2), (key1068, -2)]

theorem rawRowCheck15794 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form4 = rawRow15794 := by decide +kernel

def row15794 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15794 : row15794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15794 := by decide +kernel

theorem rowEval15794 (x : Key → ℝ) : Integer.Sparse.eval row15794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15794, Integer.Sparse.eval_collectBalanced, rawRowCheck15794]

def rawRow15795 : Integer.Sparse Key := [(key997, -2), (key997, -2), (key1012, -2), (key993, 6), (key1189, -2), (key1189, -2), (key1196, -2), (key1032, 2), (key1032, 2), (key1110, 2), (key1110, 2), (key1120, 2), (key1120, 2), (key1028, -2), (key1106, -2), (key1106, -2), (key1209, 6), (key1068, -2), (key1147, -2), (key1147, -2)]

theorem rawRowCheck15795 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form4 = rawRow15795 := by decide +kernel

def row15795 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

theorem rowCheck15795 : row15795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15795 := by decide +kernel

theorem rowEval15795 (x : Key → ℝ) : Integer.Sparse.eval row15795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15795, Integer.Sparse.eval_collectBalanced, rawRowCheck15795]

def rawRow15796 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key997, -2), (key993, 6), (key1189, -2), (key1196, -2), (key1189, -2), (key1110, 2), (key1120, 2), (key1032, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1106, -2), (key1028, -2), (key1106, -2), (key1209, 6), (key1147, -2), (key1068, -2), (key1147, -2)]

theorem rawRowCheck15796 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form4 = rawRow15796 := by decide +kernel

def row15796 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

theorem rowCheck15796 : row15796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15796 := by decide +kernel

theorem rowEval15796 (x : Key → ℝ) : Integer.Sparse.eval row15796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15796, Integer.Sparse.eval_collectBalanced, rawRowCheck15796]

def rawRow15797 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key997, -2), (key993, 6), (key1196, -2), (key1189, -2), (key1189, -2), (key1120, 2), (key1110, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1032, 2), (key1106, -2), (key1106, -2), (key1028, -2), (key1209, 6), (key1147, -2), (key1147, -2), (key1068, -2)]

theorem rawRowCheck15797 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form4 = rawRow15797 := by decide +kernel

def row15797 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

theorem rowCheck15797 : row15797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15797 := by decide +kernel

theorem rowEval15797 (x : Key → ℝ) : Integer.Sparse.eval row15797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15797, Integer.Sparse.eval_collectBalanced, rawRowCheck15797]

def rawRow15798 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1120, -2), (key1147, 6), (key993, -2), (key997, -2), (key1012, -2), (key1028, 2), (key1032, 2), (key1106, 2), (key1189, 2), (key1120, 2), (key1196, 2), (key1068, -2), (key1147, -2), (key1209, -2), (key997, 6), (key1032, -2), (key1110, -2), (key1189, -2)]

theorem rawRowCheck15798 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form4 = rawRow15798 := by decide +kernel

def row15798 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15798 : row15798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15798 := by decide +kernel

theorem rowEval15798 (x : Key → ℝ) : Integer.Sparse.eval row15798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15798, Integer.Sparse.eval_collectBalanced, rawRowCheck15798]

def rawRow15799 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1120, -2), (key1147, 6), (key997, -2), (key993, -2), (key1012, -2), (key1032, 2), (key1028, 2), (key1189, 2), (key1106, 2), (key1196, 2), (key1120, 2), (key1068, -2), (key1209, -2), (key1147, -2), (key997, 6), (key1032, -2), (key1189, -2), (key1110, -2)]

theorem rawRowCheck15799 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form4 = rawRow15799 := by decide +kernel

def row15799 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15799 : row15799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15799 := by decide +kernel

theorem rowEval15799 (x : Key → ℝ) : Integer.Sparse.eval row15799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15799, Integer.Sparse.eval_collectBalanced, rawRowCheck15799]

def rawRow15800 : Integer.Sparse Key := [(key1106, -2), (key1120, -2), (key1110, -2), (key1147, 6), (key993, -2), (key1012, -2), (key997, -2), (key1106, 2), (key1120, 2), (key1028, 2), (key1196, 2), (key1032, 2), (key1189, 2), (key1147, -2), (key1068, -2), (key1209, -2), (key997, 6), (key1110, -2), (key1032, -2), (key1189, -2)]

theorem rawRowCheck15800 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form4 = rawRow15800 := by decide +kernel

def row15800 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15800 : row15800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15800 := by decide +kernel

theorem rowEval15800 (x : Key → ℝ) : Integer.Sparse.eval row15800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15800, Integer.Sparse.eval_collectBalanced, rawRowCheck15800]

def rawRow15801 : Integer.Sparse Key := [(key1120, -2), (key1106, -2), (key1110, -2), (key1147, 6), (key1012, -2), (key993, -2), (key997, -2), (key1120, 2), (key1106, 2), (key1196, 2), (key1028, 2), (key1189, 2), (key1032, 2), (key1147, -2), (key1209, -2), (key1068, -2), (key997, 6), (key1110, -2), (key1189, -2), (key1032, -2)]

theorem rawRowCheck15801 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form4 = rawRow15801 := by decide +kernel

def row15801 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15801 : row15801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15801 := by decide +kernel

theorem rowEval15801 (x : Key → ℝ) : Integer.Sparse.eval row15801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15801, Integer.Sparse.eval_collectBalanced, rawRowCheck15801]

def rawRow15802 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1106, -2), (key1147, 6), (key997, -2), (key1012, -2), (key993, -2), (key1189, 2), (key1196, 2), (key1032, 2), (key1120, 2), (key1028, 2), (key1106, 2), (key1209, -2), (key1068, -2), (key1147, -2), (key997, 6), (key1189, -2), (key1032, -2), (key1110, -2)]

theorem rawRowCheck15802 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form4 = rawRow15802 := by decide +kernel

def row15802 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15802 : row15802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15802 := by decide +kernel

theorem rowEval15802 (x : Key → ℝ) : Integer.Sparse.eval row15802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15802, Integer.Sparse.eval_collectBalanced, rawRowCheck15802]

def rawRow15803 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1106, -2), (key1147, 6), (key1012, -2), (key997, -2), (key993, -2), (key1196, 2), (key1189, 2), (key1120, 2), (key1032, 2), (key1106, 2), (key1028, 2), (key1209, -2), (key1147, -2), (key1068, -2), (key997, 6), (key1189, -2), (key1110, -2), (key1032, -2)]

theorem rawRowCheck15803 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form4 = rawRow15803 := by decide +kernel

def row15803 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

theorem rowCheck15803 : row15803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15803 := by decide +kernel

theorem rowEval15803 (x : Key → ℝ) : Integer.Sparse.eval row15803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15803, Integer.Sparse.eval_collectBalanced, rawRowCheck15803]

def rawRow15804 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1196, -2), (key1209, 6), (key997, -2), (key997, -2), (key1012, -2), (key1032, 2), (key1032, 2), (key1110, 2), (key1110, 2), (key1120, 2), (key1120, 2), (key1068, -2), (key1147, -2), (key1147, -2), (key993, 6), (key1028, -2), (key1106, -2), (key1106, -2)]

theorem rawRowCheck15804 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form4 = rawRow15804 := by decide +kernel

def row15804 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

theorem rowCheck15804 : row15804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15804 := by decide +kernel

theorem rowEval15804 (x : Key → ℝ) : Integer.Sparse.eval row15804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15804, Integer.Sparse.eval_collectBalanced, rawRowCheck15804]

def rawRow15805 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1189, -2), (key1209, 6), (key997, -2), (key1012, -2), (key997, -2), (key1110, 2), (key1120, 2), (key1032, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1147, -2), (key1068, -2), (key1147, -2), (key993, 6), (key1106, -2), (key1028, -2), (key1106, -2)]

theorem rawRowCheck15805 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form4 = rawRow15805 := by decide +kernel

def row15805 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

theorem rowCheck15805 : row15805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15805 := by decide +kernel

theorem rowEval15805 (x : Key → ℝ) : Integer.Sparse.eval row15805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15805, Integer.Sparse.eval_collectBalanced, rawRowCheck15805]

def rawRow15806 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1189, -2), (key1209, 6), (key1012, -2), (key997, -2), (key997, -2), (key1120, 2), (key1110, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1032, 2), (key1147, -2), (key1147, -2), (key1068, -2), (key993, 6), (key1106, -2), (key1106, -2), (key1028, -2)]

theorem rawRowCheck15806 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form4 = rawRow15806 := by decide +kernel

def row15806 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

theorem rowCheck15806 : row15806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15806 := by decide +kernel

theorem rowEval15806 (x : Key → ℝ) : Integer.Sparse.eval row15806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15806, Integer.Sparse.eval_collectBalanced, rawRowCheck15806]

def rawRow15807 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1200, 4), (key1038, -2), (key1042, -2), (key1116, -2), (key1194, -2), (key1128, -2), (key1200, -2), (key1073, -2), (key1077, -2), (key1152, -2), (key1213, -2), (key1172, -2), (key1223, -2), (key1077, 4), (key1156, 4), (key1213, 4)]

theorem rawRowCheck15807 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form5 = rawRow15807 := by decide +kernel

def row15807 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15807 : row15807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15807 := by decide +kernel

theorem rowEval15807 (x : Key → ℝ) : Integer.Sparse.eval row15807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15807, Integer.Sparse.eval_collectBalanced, rawRowCheck15807]

def rawRow15808 : Integer.Sparse Key := [(key1038, 4), (key1200, 4), (key1125, 4), (key1042, -2), (key1038, -2), (key1194, -2), (key1116, -2), (key1200, -2), (key1128, -2), (key1077, -2), (key1073, -2), (key1213, -2), (key1152, -2), (key1223, -2), (key1172, -2), (key1077, 4), (key1213, 4), (key1156, 4)]

theorem rawRowCheck15808 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form5 = rawRow15808 := by decide +kernel

def row15808 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15808 : row15808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15808 := by decide +kernel

theorem rowEval15808 (x : Key → ℝ) : Integer.Sparse.eval row15808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15808, Integer.Sparse.eval_collectBalanced, rawRowCheck15808]

def rawRow15809 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1200, 4), (key1116, -2), (key1128, -2), (key1038, -2), (key1200, -2), (key1042, -2), (key1194, -2), (key1152, -2), (key1172, -2), (key1073, -2), (key1223, -2), (key1077, -2), (key1213, -2), (key1156, 4), (key1077, 4), (key1213, 4)]

theorem rawRowCheck15809 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form5 = rawRow15809 := by decide +kernel

def row15809 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15809 : row15809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15809 := by decide +kernel

theorem rowEval15809 (x : Key → ℝ) : Integer.Sparse.eval row15809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15809, Integer.Sparse.eval_collectBalanced, rawRowCheck15809]

def rawRow15810 : Integer.Sparse Key := [(key1125, 4), (key1200, 4), (key1038, 4), (key1128, -2), (key1116, -2), (key1200, -2), (key1038, -2), (key1194, -2), (key1042, -2), (key1172, -2), (key1152, -2), (key1223, -2), (key1073, -2), (key1213, -2), (key1077, -2), (key1156, 4), (key1213, 4), (key1077, 4)]

theorem rawRowCheck15810 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form5 = rawRow15810 := by decide +kernel

def row15810 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15810 : row15810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15810 := by decide +kernel

theorem rowEval15810 (x : Key → ℝ) : Integer.Sparse.eval row15810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15810, Integer.Sparse.eval_collectBalanced, rawRowCheck15810]

def rawRow15811 : Integer.Sparse Key := [(key1200, 4), (key1038, 4), (key1125, 4), (key1194, -2), (key1200, -2), (key1042, -2), (key1128, -2), (key1038, -2), (key1116, -2), (key1213, -2), (key1223, -2), (key1077, -2), (key1172, -2), (key1073, -2), (key1152, -2), (key1213, 4), (key1077, 4), (key1156, 4)]

theorem rawRowCheck15811 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form5 = rawRow15811 := by decide +kernel

def row15811 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15811 : row15811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15811 := by decide +kernel

theorem rowEval15811 (x : Key → ℝ) : Integer.Sparse.eval row15811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15811, Integer.Sparse.eval_collectBalanced, rawRowCheck15811]

def rawRow15812 : Integer.Sparse Key := [(key1200, 4), (key1125, 4), (key1038, 4), (key1200, -2), (key1194, -2), (key1128, -2), (key1042, -2), (key1116, -2), (key1038, -2), (key1223, -2), (key1213, -2), (key1172, -2), (key1077, -2), (key1152, -2), (key1073, -2), (key1213, 4), (key1156, 4), (key1077, 4)]

theorem rawRowCheck15812 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form5 = rawRow15812 := by decide +kernel

def row15812 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15812 : row15812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15812 := by decide +kernel

theorem rowEval15812 (x : Key → ℝ) : Integer.Sparse.eval row15812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15812, Integer.Sparse.eval_collectBalanced, rawRowCheck15812]

def rawRow15813 : Integer.Sparse Key := [(key1042, 4), (key1128, 4), (key1128, 4), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1077, -2), (key1077, -2), (key1156, -2), (key1156, -2), (key1172, -2), (key1172, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

theorem rawRowCheck15813 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form5 = rawRow15813 := by decide +kernel

def row15813 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

theorem rowCheck15813 : row15813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15813 := by decide +kernel

theorem rowEval15813 (x : Key → ℝ) : Integer.Sparse.eval row15813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15813, Integer.Sparse.eval_collectBalanced, rawRowCheck15813]

def rawRow15814 : Integer.Sparse Key := [(key1128, 4), (key1042, 4), (key1128, 4), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1156, -2), (key1172, -2), (key1077, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

theorem rawRowCheck15814 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form5 = rawRow15814 := by decide +kernel

def row15814 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

theorem rowCheck15814 : row15814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15814 := by decide +kernel

theorem rowEval15814 (x : Key → ℝ) : Integer.Sparse.eval row15814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15814, Integer.Sparse.eval_collectBalanced, rawRowCheck15814]

def rawRow15815 : Integer.Sparse Key := [(key1128, 4), (key1128, 4), (key1042, 4), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1172, -2), (key1156, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1077, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

theorem rawRowCheck15815 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form5 = rawRow15815 := by decide +kernel

def row15815 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

theorem rowCheck15815 : row15815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15815 := by decide +kernel

theorem rowEval15815 (x : Key → ℝ) : Integer.Sparse.eval row15815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15815, Integer.Sparse.eval_collectBalanced, rawRowCheck15815]

def rawRow15816 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1200, 4), (key1073, -2), (key1077, -2), (key1152, -2), (key1213, -2), (key1172, -2), (key1223, -2), (key1038, -2), (key1042, -2), (key1116, -2), (key1194, -2), (key1128, -2), (key1200, -2), (key1077, 4), (key1156, 4), (key1213, 4)]

theorem rawRowCheck15816 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form5 = rawRow15816 := by decide +kernel

def row15816 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15816 : row15816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15816 := by decide +kernel

theorem rowEval15816 (x : Key → ℝ) : Integer.Sparse.eval row15816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15816, Integer.Sparse.eval_collectBalanced, rawRowCheck15816]

def rawRow15817 : Integer.Sparse Key := [(key1038, 4), (key1200, 4), (key1125, 4), (key1077, -2), (key1073, -2), (key1213, -2), (key1152, -2), (key1223, -2), (key1172, -2), (key1042, -2), (key1038, -2), (key1194, -2), (key1116, -2), (key1200, -2), (key1128, -2), (key1077, 4), (key1213, 4), (key1156, 4)]

theorem rawRowCheck15817 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form5 = rawRow15817 := by decide +kernel

def row15817 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15817 : row15817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15817 := by decide +kernel

theorem rowEval15817 (x : Key → ℝ) : Integer.Sparse.eval row15817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15817, Integer.Sparse.eval_collectBalanced, rawRowCheck15817]

def rawRow15818 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1200, 4), (key1152, -2), (key1172, -2), (key1073, -2), (key1223, -2), (key1077, -2), (key1213, -2), (key1116, -2), (key1128, -2), (key1038, -2), (key1200, -2), (key1042, -2), (key1194, -2), (key1156, 4), (key1077, 4), (key1213, 4)]

theorem rawRowCheck15818 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form5 = rawRow15818 := by decide +kernel

def row15818 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15818 : row15818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15818 := by decide +kernel

theorem rowEval15818 (x : Key → ℝ) : Integer.Sparse.eval row15818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15818, Integer.Sparse.eval_collectBalanced, rawRowCheck15818]

def rawRow15819 : Integer.Sparse Key := [(key1125, 4), (key1200, 4), (key1038, 4), (key1172, -2), (key1152, -2), (key1223, -2), (key1073, -2), (key1213, -2), (key1077, -2), (key1128, -2), (key1116, -2), (key1200, -2), (key1038, -2), (key1194, -2), (key1042, -2), (key1156, 4), (key1213, 4), (key1077, 4)]

theorem rawRowCheck15819 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form5 = rawRow15819 := by decide +kernel

def row15819 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15819 : row15819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15819 := by decide +kernel

theorem rowEval15819 (x : Key → ℝ) : Integer.Sparse.eval row15819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15819, Integer.Sparse.eval_collectBalanced, rawRowCheck15819]

def rawRow15820 : Integer.Sparse Key := [(key1200, 4), (key1038, 4), (key1125, 4), (key1213, -2), (key1223, -2), (key1077, -2), (key1172, -2), (key1073, -2), (key1152, -2), (key1194, -2), (key1200, -2), (key1042, -2), (key1128, -2), (key1038, -2), (key1116, -2), (key1213, 4), (key1077, 4), (key1156, 4)]

theorem rawRowCheck15820 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form5 = rawRow15820 := by decide +kernel

def row15820 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15820 : row15820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15820 := by decide +kernel

theorem rowEval15820 (x : Key → ℝ) : Integer.Sparse.eval row15820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15820, Integer.Sparse.eval_collectBalanced, rawRowCheck15820]

def rawRow15821 : Integer.Sparse Key := [(key1200, 4), (key1125, 4), (key1038, 4), (key1223, -2), (key1213, -2), (key1172, -2), (key1077, -2), (key1152, -2), (key1073, -2), (key1200, -2), (key1194, -2), (key1128, -2), (key1042, -2), (key1116, -2), (key1038, -2), (key1213, 4), (key1156, 4), (key1077, 4)]

theorem rawRowCheck15821 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form5 = rawRow15821 := by decide +kernel

def row15821 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

theorem rowCheck15821 : row15821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15821 := by decide +kernel

theorem rowEval15821 (x : Key → ℝ) : Integer.Sparse.eval row15821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15821, Integer.Sparse.eval_collectBalanced, rawRowCheck15821]

def rawRow15822 : Integer.Sparse Key := [(key1042, 4), (key1128, 4), (key1128, 4), (key1077, -2), (key1077, -2), (key1156, -2), (key1156, -2), (key1172, -2), (key1172, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

theorem rawRowCheck15822 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form5 = rawRow15822 := by decide +kernel

def row15822 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

theorem rowCheck15822 : row15822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15822 := by decide +kernel

theorem rowEval15822 (x : Key → ℝ) : Integer.Sparse.eval row15822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15822, Integer.Sparse.eval_collectBalanced, rawRowCheck15822]

def rawRow15823 : Integer.Sparse Key := [(key1128, 4), (key1042, 4), (key1128, 4), (key1156, -2), (key1172, -2), (key1077, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

theorem rawRowCheck15823 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form5 = rawRow15823 := by decide +kernel

def row15823 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

theorem rowCheck15823 : row15823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15823 := by decide +kernel

theorem rowEval15823 (x : Key → ℝ) : Integer.Sparse.eval row15823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15823, Integer.Sparse.eval_collectBalanced, rawRowCheck15823]

def rawRow15824 : Integer.Sparse Key := [(key1128, 4), (key1128, 4), (key1042, 4), (key1172, -2), (key1156, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1077, -2), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

theorem rawRowCheck15824 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form5 = rawRow15824 := by decide +kernel

def row15824 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

theorem rowCheck15824 : row15824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15824 := by decide +kernel

theorem rowEval15824 (x : Key → ℝ) : Integer.Sparse.eval row15824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15824, Integer.Sparse.eval_collectBalanced, rawRowCheck15824]

def rawRow15825 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2668, 2), (key2783, 2), (key2937, 2), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2), (key2703, -1), (key2736, -1), (key2806, -1), (key2949, -1), (key2894, -1), (key2973, -1), (key2723, 2), (key2867, 2), (key2982, 2), (key2723, -1), (key2746, -1), (key2826, -1), (key2959, -1), (key2903, -1), (key2982, -1)]

theorem rawRowCheck15825 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form6 = rawRow15825 := by decide +kernel

def row15825 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15825 : row15825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15825 := by decide +kernel

theorem rowEval15825 (x : Key → ℝ) : Integer.Sparse.eval row15825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15825, Integer.Sparse.eval_collectBalanced, rawRowCheck15825]

def rawRow15826 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2668, 2), (key2937, 2), (key2783, 2), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2), (key2736, -1), (key2703, -1), (key2949, -1), (key2806, -1), (key2973, -1), (key2894, -1), (key2723, 2), (key2982, 2), (key2867, 2), (key2746, -1), (key2723, -1), (key2959, -1), (key2826, -1), (key2982, -1), (key2903, -1)]

theorem rawRowCheck15826 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form6 = rawRow15826 := by decide +kernel

def row15826 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15826 : row15826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15826 := by decide +kernel

theorem rowEval15826 (x : Key → ℝ) : Integer.Sparse.eval row15826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15826, Integer.Sparse.eval_collectBalanced, rawRowCheck15826]

def rawRow15827 : Integer.Sparse Key := [(key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2783, 2), (key2668, 2), (key2937, 2), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2), (key2806, -1), (key2894, -1), (key2703, -1), (key2973, -1), (key2736, -1), (key2949, -1), (key2867, 2), (key2723, 2), (key2982, 2), (key2826, -1), (key2903, -1), (key2723, -1), (key2982, -1), (key2746, -1), (key2959, -1)]

theorem rawRowCheck15827 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form6 = rawRow15827 := by decide +kernel

def row15827 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15827 : row15827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15827 := by decide +kernel

theorem rowEval15827 (x : Key → ℝ) : Integer.Sparse.eval row15827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15827, Integer.Sparse.eval_collectBalanced, rawRowCheck15827]

def rawRow15828 : Integer.Sparse Key := [(key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2783, 2), (key2937, 2), (key2668, 2), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2), (key2894, -1), (key2806, -1), (key2973, -1), (key2703, -1), (key2949, -1), (key2736, -1), (key2867, 2), (key2982, 2), (key2723, 2), (key2903, -1), (key2826, -1), (key2982, -1), (key2723, -1), (key2959, -1), (key2746, -1)]

theorem rawRowCheck15828 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form6 = rawRow15828 := by decide +kernel

def row15828 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15828 : row15828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15828 := by decide +kernel

theorem rowEval15828 (x : Key → ℝ) : Integer.Sparse.eval row15828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15828, Integer.Sparse.eval_collectBalanced, rawRowCheck15828]

def rawRow15829 : Integer.Sparse Key := [(key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2937, 2), (key2668, 2), (key2783, 2), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2), (key2949, -1), (key2973, -1), (key2736, -1), (key2894, -1), (key2703, -1), (key2806, -1), (key2982, 2), (key2723, 2), (key2867, 2), (key2959, -1), (key2982, -1), (key2746, -1), (key2903, -1), (key2723, -1), (key2826, -1)]

theorem rawRowCheck15829 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form6 = rawRow15829 := by decide +kernel

def row15829 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15829 : row15829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15829 := by decide +kernel

theorem rowEval15829 (x : Key → ℝ) : Integer.Sparse.eval row15829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15829, Integer.Sparse.eval_collectBalanced, rawRowCheck15829]

def rawRow15830 : Integer.Sparse Key := [(key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2937, 2), (key2783, 2), (key2668, 2), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2), (key2973, -1), (key2949, -1), (key2894, -1), (key2736, -1), (key2806, -1), (key2703, -1), (key2982, 2), (key2867, 2), (key2723, 2), (key2982, -1), (key2959, -1), (key2903, -1), (key2746, -1), (key2826, -1), (key2723, -1)]

theorem rawRowCheck15830 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form6 = rawRow15830 := by decide +kernel

def row15830 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15830 : row15830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15830 := by decide +kernel

theorem rowEval15830 (x : Key → ℝ) : Integer.Sparse.eval row15830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15830, Integer.Sparse.eval_collectBalanced, rawRowCheck15830]

def rawRow15831 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2664, 2), (key2779, 2), (key2779, 2), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2), (key2699, -1), (key2699, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1), (key2746, 2), (key2903, 2), (key2903, 2), (key2723, -1), (key2723, -1), (key2826, -1), (key2826, -1), (key2867, -1), (key2867, -1)]

theorem rawRowCheck15831 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form6 = rawRow15831 := by decide +kernel

def row15831 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

theorem rowCheck15831 : row15831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15831 := by decide +kernel

theorem rowEval15831 (x : Key → ℝ) : Integer.Sparse.eval row15831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15831, Integer.Sparse.eval_collectBalanced, rawRowCheck15831]

def rawRow15832 : Integer.Sparse Key := [(key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2779, 2), (key2664, 2), (key2779, 2), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2802, -1), (key2852, -1), (key2699, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2903, 2), (key2746, 2), (key2903, 2), (key2826, -1), (key2867, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2826, -1)]

theorem rawRowCheck15832 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form6 = rawRow15832 := by decide +kernel

def row15832 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

theorem rowCheck15832 : row15832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15832 := by decide +kernel

theorem rowEval15832 (x : Key → ℝ) : Integer.Sparse.eval row15832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15832, Integer.Sparse.eval_collectBalanced, rawRowCheck15832]

def rawRow15833 : Integer.Sparse Key := [(key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2779, 2), (key2779, 2), (key2664, 2), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2699, -1), (key2903, 2), (key2903, 2), (key2746, 2), (key2867, -1), (key2826, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2723, -1)]

theorem rawRowCheck15833 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form6 = rawRow15833 := by decide +kernel

def row15833 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

theorem rowCheck15833 : row15833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15833 := by decide +kernel

theorem rowEval15833 (x : Key → ℝ) : Integer.Sparse.eval row15833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15833, Integer.Sparse.eval_collectBalanced, rawRowCheck15833]

def rawRow15834 : Integer.Sparse Key := [(key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2723, 2), (key2867, 2), (key2982, 2), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2), (key2723, -1), (key2746, -1), (key2826, -1), (key2959, -1), (key2903, -1), (key2982, -1), (key2668, 2), (key2783, 2), (key2937, 2), (key2703, -1), (key2736, -1), (key2806, -1), (key2949, -1), (key2894, -1), (key2973, -1)]

theorem rawRowCheck15834 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form6 = rawRow15834 := by decide +kernel

def row15834 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15834 : row15834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15834 := by decide +kernel

theorem rowEval15834 (x : Key → ℝ) : Integer.Sparse.eval row15834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15834, Integer.Sparse.eval_collectBalanced, rawRowCheck15834]

def rawRow15835 : Integer.Sparse Key := [(key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2723, 2), (key2982, 2), (key2867, 2), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2), (key2746, -1), (key2723, -1), (key2959, -1), (key2826, -1), (key2982, -1), (key2903, -1), (key2668, 2), (key2937, 2), (key2783, 2), (key2736, -1), (key2703, -1), (key2949, -1), (key2806, -1), (key2973, -1), (key2894, -1)]

theorem rawRowCheck15835 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form6 = rawRow15835 := by decide +kernel

def row15835 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15835 : row15835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15835 := by decide +kernel

theorem rowEval15835 (x : Key → ℝ) : Integer.Sparse.eval row15835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15835, Integer.Sparse.eval_collectBalanced, rawRowCheck15835]

def rawRow15836 : Integer.Sparse Key := [(key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2867, 2), (key2723, 2), (key2982, 2), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2), (key2826, -1), (key2903, -1), (key2723, -1), (key2982, -1), (key2746, -1), (key2959, -1), (key2783, 2), (key2668, 2), (key2937, 2), (key2806, -1), (key2894, -1), (key2703, -1), (key2973, -1), (key2736, -1), (key2949, -1)]

theorem rawRowCheck15836 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form6 = rawRow15836 := by decide +kernel

def row15836 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15836 : row15836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15836 := by decide +kernel

theorem rowEval15836 (x : Key → ℝ) : Integer.Sparse.eval row15836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15836, Integer.Sparse.eval_collectBalanced, rawRowCheck15836]

def rawRow15837 : Integer.Sparse Key := [(key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2867, 2), (key2982, 2), (key2723, 2), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2), (key2903, -1), (key2826, -1), (key2982, -1), (key2723, -1), (key2959, -1), (key2746, -1), (key2783, 2), (key2937, 2), (key2668, 2), (key2894, -1), (key2806, -1), (key2973, -1), (key2703, -1), (key2949, -1), (key2736, -1)]

theorem rawRowCheck15837 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form6 = rawRow15837 := by decide +kernel

def row15837 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15837 : row15837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15837 := by decide +kernel

theorem rowEval15837 (x : Key → ℝ) : Integer.Sparse.eval row15837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15837, Integer.Sparse.eval_collectBalanced, rawRowCheck15837]

def rawRow15838 : Integer.Sparse Key := [(key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2982, 2), (key2723, 2), (key2867, 2), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2), (key2959, -1), (key2982, -1), (key2746, -1), (key2903, -1), (key2723, -1), (key2826, -1), (key2937, 2), (key2668, 2), (key2783, 2), (key2949, -1), (key2973, -1), (key2736, -1), (key2894, -1), (key2703, -1), (key2806, -1)]

theorem rawRowCheck15838 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form6 = rawRow15838 := by decide +kernel

def row15838 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15838 : row15838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15838 := by decide +kernel

theorem rowEval15838 (x : Key → ℝ) : Integer.Sparse.eval row15838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15838, Integer.Sparse.eval_collectBalanced, rawRowCheck15838]

def rawRow15839 : Integer.Sparse Key := [(key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2982, 2), (key2867, 2), (key2723, 2), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2), (key2982, -1), (key2959, -1), (key2903, -1), (key2746, -1), (key2826, -1), (key2723, -1), (key2937, 2), (key2783, 2), (key2668, 2), (key2973, -1), (key2949, -1), (key2894, -1), (key2736, -1), (key2806, -1), (key2703, -1)]

theorem rawRowCheck15839 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form6 = rawRow15839 := by decide +kernel

def row15839 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck15839 : row15839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15839 := by decide +kernel

theorem rowEval15839 (x : Key → ℝ) : Integer.Sparse.eval row15839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15839, Integer.Sparse.eval_collectBalanced, rawRowCheck15839]

def rawRow15840 : Integer.Sparse Key := [(key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2746, 2), (key2903, 2), (key2903, 2), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2), (key2723, -1), (key2723, -1), (key2826, -1), (key2826, -1), (key2867, -1), (key2867, -1), (key2664, 2), (key2779, 2), (key2779, 2), (key2699, -1), (key2699, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1)]

theorem rawRowCheck15840 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form6 = rawRow15840 := by decide +kernel

def row15840 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

theorem rowCheck15840 : row15840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15840 := by decide +kernel

theorem rowEval15840 (x : Key → ℝ) : Integer.Sparse.eval row15840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15840, Integer.Sparse.eval_collectBalanced, rawRowCheck15840]

def rawRow15841 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2903, 2), (key2746, 2), (key2903, 2), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2826, -1), (key2867, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2779, 2), (key2664, 2), (key2779, 2), (key2802, -1), (key2852, -1), (key2699, -1), (key2852, -1), (key2699, -1), (key2802, -1)]

theorem rawRowCheck15841 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form6 = rawRow15841 := by decide +kernel

def row15841 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

theorem rowCheck15841 : row15841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15841 := by decide +kernel

theorem rowEval15841 (x : Key → ℝ) : Integer.Sparse.eval row15841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15841, Integer.Sparse.eval_collectBalanced, rawRowCheck15841]

def rawRow15842 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2903, 2), (key2903, 2), (key2746, 2), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2), (key2867, -1), (key2826, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2723, -1), (key2779, 2), (key2779, 2), (key2664, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2699, -1)]

theorem rawRowCheck15842 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form6 = rawRow15842 := by decide +kernel

def row15842 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

theorem rowCheck15842 : row15842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15842 := by decide +kernel

theorem rowEval15842 (x : Key → ℝ) : Integer.Sparse.eval row15842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15842, Integer.Sparse.eval_collectBalanced, rawRowCheck15842]

def rawRow15843 : Integer.Sparse Key := [(key2678, 4), (key2709, 4), (key2713, 4), (key2678, -4), (key2687, -4), (key2713, -4), (key2812, -4), (key2816, -4), (key2862, -4), (key2816, 12)]

theorem rawRowCheck15843 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form7 = rawRow15843 := by decide +kernel

def row15843 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15843 : row15843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15843 := by decide +kernel

theorem rowEval15843 (x : Key → ℝ) : Integer.Sparse.eval row15843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15843, Integer.Sparse.eval_collectBalanced, rawRowCheck15843]

def rawRow15844 : Integer.Sparse Key := [(key2678, 4), (key2713, 4), (key2709, 4), (key2687, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2812, -4), (key2862, -4), (key2816, 12)]

theorem rawRowCheck15844 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form7 = rawRow15844 := by decide +kernel

def row15844 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15844 : row15844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15844 := by decide +kernel

theorem rowEval15844 (x : Key → ℝ) : Integer.Sparse.eval row15844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15844, Integer.Sparse.eval_collectBalanced, rawRowCheck15844]

def rawRow15845 : Integer.Sparse Key := [(key2709, 4), (key2678, 4), (key2713, 4), (key2678, -4), (key2713, -4), (key2687, -4), (key2812, -4), (key2862, -4), (key2816, -4), (key2816, 12)]

theorem rawRowCheck15845 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form7 = rawRow15845 := by decide +kernel

def row15845 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15845 : row15845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15845 := by decide +kernel

theorem rowEval15845 (x : Key → ℝ) : Integer.Sparse.eval row15845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15845, Integer.Sparse.eval_collectBalanced, rawRowCheck15845]

def rawRow15846 : Integer.Sparse Key := [(key2709, 4), (key2713, 4), (key2678, 4), (key2713, -4), (key2678, -4), (key2687, -4), (key2862, -4), (key2812, -4), (key2816, -4), (key2816, 12)]

theorem rawRowCheck15846 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form7 = rawRow15846 := by decide +kernel

def row15846 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15846 : row15846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15846 := by decide +kernel

theorem rowEval15846 (x : Key → ℝ) : Integer.Sparse.eval row15846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15846, Integer.Sparse.eval_collectBalanced, rawRowCheck15846]

def rawRow15847 : Integer.Sparse Key := [(key2713, 4), (key2678, 4), (key2709, 4), (key2687, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2862, -4), (key2812, -4), (key2816, 12)]

theorem rawRowCheck15847 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form7 = rawRow15847 := by decide +kernel

def row15847 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15847 : row15847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15847 := by decide +kernel

theorem rowEval15847 (x : Key → ℝ) : Integer.Sparse.eval row15847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15847, Integer.Sparse.eval_collectBalanced, rawRowCheck15847]

def rawRow15848 : Integer.Sparse Key := [(key2713, 4), (key2709, 4), (key2678, 4), (key2713, -4), (key2687, -4), (key2678, -4), (key2862, -4), (key2816, -4), (key2812, -4), (key2816, 12)]

theorem rawRowCheck15848 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form7 = rawRow15848 := by decide +kernel

def row15848 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15848 : row15848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15848 := by decide +kernel

theorem rowEval15848 (x : Key → ℝ) : Integer.Sparse.eval row15848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15848, Integer.Sparse.eval_collectBalanced, rawRowCheck15848]

def rawRow15849 : Integer.Sparse Key := [(key2687, 4), (key2713, 4), (key2713, 4), (key2678, -4), (key2678, -4), (key2709, -4), (key2816, -4), (key2816, -4), (key2862, -4), (key2812, 12)]

theorem rawRowCheck15849 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form7 = rawRow15849 := by decide +kernel

def row15849 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

theorem rowCheck15849 : row15849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15849 := by decide +kernel

theorem rowEval15849 (x : Key → ℝ) : Integer.Sparse.eval row15849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15849, Integer.Sparse.eval_collectBalanced, rawRowCheck15849]

def rawRow15850 : Integer.Sparse Key := [(key2713, 4), (key2687, 4), (key2713, 4), (key2678, -4), (key2709, -4), (key2678, -4), (key2816, -4), (key2862, -4), (key2816, -4), (key2812, 12)]

theorem rawRowCheck15850 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form7 = rawRow15850 := by decide +kernel

def row15850 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

theorem rowCheck15850 : row15850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15850 := by decide +kernel

theorem rowEval15850 (x : Key → ℝ) : Integer.Sparse.eval row15850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15850, Integer.Sparse.eval_collectBalanced, rawRowCheck15850]

def rawRow15851 : Integer.Sparse Key := [(key2713, 4), (key2713, 4), (key2687, 4), (key2709, -4), (key2678, -4), (key2678, -4), (key2862, -4), (key2816, -4), (key2816, -4), (key2812, 12)]

theorem rawRowCheck15851 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form7 = rawRow15851 := by decide +kernel

def row15851 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

theorem rowCheck15851 : row15851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15851 := by decide +kernel

theorem rowEval15851 (x : Key → ℝ) : Integer.Sparse.eval row15851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15851, Integer.Sparse.eval_collectBalanced, rawRowCheck15851]

def rawRow15852 : Integer.Sparse Key := [(key2678, 4), (key2709, 4), (key2713, 4), (key2812, -4), (key2816, -4), (key2862, -4), (key2678, -4), (key2687, -4), (key2713, -4), (key2816, 12)]

theorem rawRowCheck15852 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form7 = rawRow15852 := by decide +kernel

def row15852 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15852 : row15852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15852 := by decide +kernel

theorem rowEval15852 (x : Key → ℝ) : Integer.Sparse.eval row15852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15852, Integer.Sparse.eval_collectBalanced, rawRowCheck15852]

def rawRow15853 : Integer.Sparse Key := [(key2678, 4), (key2713, 4), (key2709, 4), (key2816, -4), (key2812, -4), (key2862, -4), (key2687, -4), (key2678, -4), (key2713, -4), (key2816, 12)]

theorem rawRowCheck15853 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form7 = rawRow15853 := by decide +kernel

def row15853 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15853 : row15853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15853 := by decide +kernel

theorem rowEval15853 (x : Key → ℝ) : Integer.Sparse.eval row15853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15853, Integer.Sparse.eval_collectBalanced, rawRowCheck15853]

def rawRow15854 : Integer.Sparse Key := [(key2709, 4), (key2678, 4), (key2713, 4), (key2812, -4), (key2862, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2687, -4), (key2816, 12)]

theorem rawRowCheck15854 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form7 = rawRow15854 := by decide +kernel

def row15854 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15854 : row15854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15854 := by decide +kernel

theorem rowEval15854 (x : Key → ℝ) : Integer.Sparse.eval row15854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15854, Integer.Sparse.eval_collectBalanced, rawRowCheck15854]

def rawRow15855 : Integer.Sparse Key := [(key2709, 4), (key2713, 4), (key2678, 4), (key2862, -4), (key2812, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2687, -4), (key2816, 12)]

theorem rawRowCheck15855 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form7 = rawRow15855 := by decide +kernel

def row15855 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15855 : row15855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15855 := by decide +kernel

theorem rowEval15855 (x : Key → ℝ) : Integer.Sparse.eval row15855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15855, Integer.Sparse.eval_collectBalanced, rawRowCheck15855]

def rawRow15856 : Integer.Sparse Key := [(key2713, 4), (key2678, 4), (key2709, 4), (key2816, -4), (key2862, -4), (key2812, -4), (key2687, -4), (key2713, -4), (key2678, -4), (key2816, 12)]

theorem rawRowCheck15856 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form7 = rawRow15856 := by decide +kernel

def row15856 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15856 : row15856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15856 := by decide +kernel

theorem rowEval15856 (x : Key → ℝ) : Integer.Sparse.eval row15856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15856, Integer.Sparse.eval_collectBalanced, rawRowCheck15856]

def rawRow15857 : Integer.Sparse Key := [(key2713, 4), (key2709, 4), (key2678, 4), (key2862, -4), (key2816, -4), (key2812, -4), (key2713, -4), (key2687, -4), (key2678, -4), (key2816, 12)]

theorem rawRowCheck15857 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form7 = rawRow15857 := by decide +kernel

def row15857 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck15857 : row15857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15857 := by decide +kernel

theorem rowEval15857 (x : Key → ℝ) : Integer.Sparse.eval row15857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15857, Integer.Sparse.eval_collectBalanced, rawRowCheck15857]

def rawRow15858 : Integer.Sparse Key := [(key2687, 4), (key2713, 4), (key2713, 4), (key2816, -4), (key2816, -4), (key2862, -4), (key2678, -4), (key2678, -4), (key2709, -4), (key2812, 12)]

theorem rawRowCheck15858 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form7 = rawRow15858 := by decide +kernel

def row15858 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

theorem rowCheck15858 : row15858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15858 := by decide +kernel

theorem rowEval15858 (x : Key → ℝ) : Integer.Sparse.eval row15858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15858, Integer.Sparse.eval_collectBalanced, rawRowCheck15858]

def rawRow15859 : Integer.Sparse Key := [(key2713, 4), (key2687, 4), (key2713, 4), (key2816, -4), (key2862, -4), (key2816, -4), (key2678, -4), (key2709, -4), (key2678, -4), (key2812, 12)]

theorem rawRowCheck15859 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form7 = rawRow15859 := by decide +kernel

def row15859 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

theorem rowCheck15859 : row15859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15859 := by decide +kernel

theorem rowEval15859 (x : Key → ℝ) : Integer.Sparse.eval row15859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15859, Integer.Sparse.eval_collectBalanced, rawRowCheck15859]

def rawRow15860 : Integer.Sparse Key := [(key2713, 4), (key2713, 4), (key2687, 4), (key2862, -4), (key2816, -4), (key2816, -4), (key2709, -4), (key2678, -4), (key2678, -4), (key2812, 12)]

theorem rawRowCheck15860 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form7 = rawRow15860 := by decide +kernel

def row15860 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

theorem rowCheck15860 : row15860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15860 := by decide +kernel

theorem rowEval15860 (x : Key → ℝ) : Integer.Sparse.eval row15860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15860, Integer.Sparse.eval_collectBalanced, rawRowCheck15860]

def rawRow15861 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2373, 6), (key2839, -2), (key2842, -2), (key2886, -2), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2765, -2), (key2842, -2), (key2874, -2), (key2965, 6), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rawRowCheck15861 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form8 = rawRow15861 := by decide +kernel

def row15861 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

theorem rowCheck15861 : row15861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15861 := by decide +kernel

theorem rowEval15861 (x : Key → ℝ) : Integer.Sparse.eval row15861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15861, Integer.Sparse.eval_collectBalanced, rawRowCheck15861]

def rawRow15862 : Integer.Sparse Key := [(key2373, -2), (key2370, -2), (key2386, -2), (key2373, 6), (key2842, -2), (key2839, -2), (key2886, -2), (key2765, 2), (key2762, 2), (key2874, 2), (key2839, 2), (key2908, 2), (key2886, 2), (key2765, -2), (key2874, -2), (key2842, -2), (key2965, 6), (key2928, -2), (key2987, -2), (key2965, -2)]

theorem rawRowCheck15862 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form8 = rawRow15862 := by decide +kernel

def row15862 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

theorem rowCheck15862 : row15862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15862 := by decide +kernel

theorem rowEval15862 (x : Key → ℝ) : Integer.Sparse.eval row15862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15862, Integer.Sparse.eval_collectBalanced, rawRowCheck15862]

def rawRow15863 : Integer.Sparse Key := [(key2370, -2), (key2386, -2), (key2373, -2), (key2373, 6), (key2839, -2), (key2886, -2), (key2842, -2), (key2839, 2), (key2886, 2), (key2762, 2), (key2908, 2), (key2765, 2), (key2874, 2), (key2842, -2), (key2765, -2), (key2874, -2), (key2965, 6), (key2965, -2), (key2928, -2), (key2987, -2)]

theorem rawRowCheck15863 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form8 = rawRow15863 := by decide +kernel

def row15863 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

theorem rowCheck15863 : row15863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15863 := by decide +kernel

theorem rowEval15863 (x : Key → ℝ) : Integer.Sparse.eval row15863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15863, Integer.Sparse.eval_collectBalanced, rawRowCheck15863]

def rawRow15864 : Integer.Sparse Key := [(key2386, -2), (key2370, -2), (key2373, -2), (key2373, 6), (key2886, -2), (key2839, -2), (key2842, -2), (key2886, 2), (key2839, 2), (key2908, 2), (key2762, 2), (key2874, 2), (key2765, 2), (key2842, -2), (key2874, -2), (key2765, -2), (key2965, 6), (key2965, -2), (key2987, -2), (key2928, -2)]

theorem rawRowCheck15864 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form8 = rawRow15864 := by decide +kernel

def row15864 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

theorem rowCheck15864 : row15864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15864 := by decide +kernel

theorem rowEval15864 (x : Key → ℝ) : Integer.Sparse.eval row15864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15864, Integer.Sparse.eval_collectBalanced, rawRowCheck15864]

def rawRow15865 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2370, -2), (key2373, 6), (key2842, -2), (key2886, -2), (key2839, -2), (key2874, 2), (key2908, 2), (key2765, 2), (key2886, 2), (key2762, 2), (key2839, 2), (key2874, -2), (key2765, -2), (key2842, -2), (key2965, 6), (key2987, -2), (key2928, -2), (key2965, -2)]

theorem rawRowCheck15865 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form8 = rawRow15865 := by decide +kernel

def row15865 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

theorem rowCheck15865 : row15865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15865 := by decide +kernel

theorem rowEval15865 (x : Key → ℝ) : Integer.Sparse.eval row15865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15865, Integer.Sparse.eval_collectBalanced, rawRowCheck15865]

def rawRow15866 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2370, -2), (key2373, 6), (key2886, -2), (key2842, -2), (key2839, -2), (key2908, 2), (key2874, 2), (key2886, 2), (key2765, 2), (key2839, 2), (key2762, 2), (key2874, -2), (key2842, -2), (key2765, -2), (key2965, 6), (key2987, -2), (key2965, -2), (key2928, -2)]

theorem rawRowCheck15866 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form8 = rawRow15866 := by decide +kernel

def row15866 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

theorem rowCheck15866 : row15866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15866 := by decide +kernel

theorem rowEval15866 (x : Key → ℝ) : Integer.Sparse.eval row15866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15866, Integer.Sparse.eval_collectBalanced, rawRowCheck15866]

def rawRow15867 : Integer.Sparse Key := [(key2373, -2), (key2373, -2), (key2386, -2), (key2370, 6), (key2874, -2), (key2874, -2), (key2908, -2), (key2765, 2), (key2765, 2), (key2842, 2), (key2842, 2), (key2886, 2), (key2886, 2), (key2762, -2), (key2839, -2), (key2839, -2), (key2987, 6), (key2928, -2), (key2965, -2), (key2965, -2)]

theorem rawRowCheck15867 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form8 = rawRow15867 := by decide +kernel

def row15867 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2765, 4), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, 4), (key2908, -2), (key2928, -2), (key2965, -4), (key2987, 6)]

theorem rowCheck15867 : row15867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15867 := by decide +kernel

theorem rowEval15867 (x : Key → ℝ) : Integer.Sparse.eval row15867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15867, Integer.Sparse.eval_collectBalanced, rawRowCheck15867]

def rawRow15868 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2373, -2), (key2370, 6), (key2874, -2), (key2908, -2), (key2874, -2), (key2842, 2), (key2886, 2), (key2765, 2), (key2886, 2), (key2765, 2), (key2842, 2), (key2839, -2), (key2762, -2), (key2839, -2), (key2987, 6), (key2965, -2), (key2928, -2), (key2965, -2)]

theorem rawRowCheck15868 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form8 = rawRow15868 := by decide +kernel

def row15868 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2765, 4), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, 4), (key2908, -2), (key2928, -2), (key2965, -4), (key2987, 6)]

theorem rowCheck15868 : row15868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15868 := by decide +kernel

theorem rowEval15868 (x : Key → ℝ) : Integer.Sparse.eval row15868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15868, Integer.Sparse.eval_collectBalanced, rawRowCheck15868]

def rawRow15869 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2373, -2), (key2370, 6), (key2908, -2), (key2874, -2), (key2874, -2), (key2886, 2), (key2842, 2), (key2886, 2), (key2765, 2), (key2842, 2), (key2765, 2), (key2839, -2), (key2839, -2), (key2762, -2), (key2987, 6), (key2965, -2), (key2965, -2), (key2928, -2)]

theorem rawRowCheck15869 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form8 = rawRow15869 := by decide +kernel

def row15869 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2765, 4), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, 4), (key2908, -2), (key2928, -2), (key2965, -4), (key2987, 6)]

theorem rowCheck15869 : row15869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15869 := by decide +kernel

theorem rowEval15869 (x : Key → ℝ) : Integer.Sparse.eval row15869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15869, Integer.Sparse.eval_collectBalanced, rawRowCheck15869]

def rawRow15870 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2370, -2), (key2373, -2), (key2386, -2), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2), (key2586, 6), (key2765, -2), (key2842, -2), (key2874, -2)]

theorem rawRowCheck15870 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form8 = rawRow15870 := by decide +kernel

def row15870 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck15870 : row15870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15870 := by decide +kernel

theorem rowEval15870 (x : Key → ℝ) : Integer.Sparse.eval row15870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15870, Integer.Sparse.eval_collectBalanced, rawRowCheck15870]

def rawRow15871 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2476, -2), (key2499, 6), (key2373, -2), (key2370, -2), (key2386, -2), (key2765, 2), (key2762, 2), (key2874, 2), (key2839, 2), (key2908, 2), (key2886, 2), (key2928, -2), (key2987, -2), (key2965, -2), (key2586, 6), (key2765, -2), (key2874, -2), (key2842, -2)]

theorem rawRowCheck15871 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form8 = rawRow15871 := by decide +kernel

def row15871 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck15871 : row15871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15871 := by decide +kernel

theorem rowEval15871 (x : Key → ℝ) : Integer.Sparse.eval row15871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15871, Integer.Sparse.eval_collectBalanced, rawRowCheck15871]

end MUB6.Certificate.GramRows

end OAI

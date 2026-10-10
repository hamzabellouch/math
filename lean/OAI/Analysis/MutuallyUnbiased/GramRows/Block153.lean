import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16512 : Integer.Sparse Key := [(key1879, -2), (key1860, -2), (key1864, -2), (key1869, 6), (key1518, -2), (key1489, -2), (key1495, -2), (key1746, 2), (key1715, 2), (key1879, 2), (key1363, 2), (key1864, 2), (key1369, 2), (key1727, -2), (key1869, -2), (key1378, -2), (key1489, 6), (key1715, -2), (key1860, -2), (key1363, -2)]

theorem rawRowCheck16512 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form11 = rawRow16512 := by decide +kernel

def row16512 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16512 : row16512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16512 := by decide +kernel

theorem rowEval16512 (x : Key → ℝ) : Integer.Sparse.eval row16512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16512, Integer.Sparse.eval_collectBalanced, rawRowCheck16512]

def rawRow16513 : Integer.Sparse Key := [(key1864, -2), (key1879, -2), (key1860, -2), (key1869, 6), (key1495, -2), (key1518, -2), (key1489, -2), (key1864, 2), (key1879, 2), (key1369, 2), (key1746, 2), (key1363, 2), (key1715, 2), (key1869, -2), (key1378, -2), (key1727, -2), (key1489, 6), (key1860, -2), (key1363, -2), (key1715, -2)]

theorem rawRowCheck16513 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form11 = rawRow16513 := by decide +kernel

def row16513 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16513 : row16513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16513 := by decide +kernel

theorem rowEval16513 (x : Key → ℝ) : Integer.Sparse.eval row16513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16513, Integer.Sparse.eval_collectBalanced, rawRowCheck16513]

def rawRow16514 : Integer.Sparse Key := [(key1879, -2), (key1864, -2), (key1860, -2), (key1869, 6), (key1518, -2), (key1495, -2), (key1489, -2), (key1879, 2), (key1864, 2), (key1746, 2), (key1369, 2), (key1715, 2), (key1363, 2), (key1869, -2), (key1727, -2), (key1378, -2), (key1489, 6), (key1860, -2), (key1715, -2), (key1363, -2)]

theorem rawRowCheck16514 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form11 = rawRow16514 := by decide +kernel

def row16514 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16514 : row16514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16514 := by decide +kernel

theorem rowEval16514 (x : Key → ℝ) : Integer.Sparse.eval row16514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16514, Integer.Sparse.eval_collectBalanced, rawRowCheck16514]

def rawRow16515 : Integer.Sparse Key := [(key1860, -2), (key1869, -2), (key1879, -2), (key1864, 6), (key1715, -2), (key1727, -2), (key1746, -2), (key1363, 2), (key1378, 2), (key1489, 2), (key1869, 2), (key1518, 2), (key1879, 2), (key1369, -2), (key1495, -2), (key1864, -2), (key1715, 6), (key1363, -2), (key1489, -2), (key1860, -2)]

theorem rawRowCheck16515 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form11 = rawRow16515 := by decide +kernel

def row16515 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16515 : row16515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16515 := by decide +kernel

theorem rowEval16515 (x : Key → ℝ) : Integer.Sparse.eval row16515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16515, Integer.Sparse.eval_collectBalanced, rawRowCheck16515]

def rawRow16516 : Integer.Sparse Key := [(key1869, -2), (key1860, -2), (key1879, -2), (key1864, 6), (key1727, -2), (key1715, -2), (key1746, -2), (key1378, 2), (key1363, 2), (key1869, 2), (key1489, 2), (key1879, 2), (key1518, 2), (key1369, -2), (key1864, -2), (key1495, -2), (key1715, 6), (key1363, -2), (key1860, -2), (key1489, -2)]

theorem rawRowCheck16516 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form11 = rawRow16516 := by decide +kernel

def row16516 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16516 : row16516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16516 := by decide +kernel

theorem rowEval16516 (x : Key → ℝ) : Integer.Sparse.eval row16516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16516, Integer.Sparse.eval_collectBalanced, rawRowCheck16516]

def rawRow16517 : Integer.Sparse Key := [(key1860, -2), (key1879, -2), (key1869, -2), (key1864, 6), (key1715, -2), (key1746, -2), (key1727, -2), (key1489, 2), (key1518, 2), (key1363, 2), (key1879, 2), (key1378, 2), (key1869, 2), (key1495, -2), (key1369, -2), (key1864, -2), (key1715, 6), (key1489, -2), (key1363, -2), (key1860, -2)]

theorem rawRowCheck16517 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form11 = rawRow16517 := by decide +kernel

def row16517 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16517 : row16517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16517 := by decide +kernel

theorem rowEval16517 (x : Key → ℝ) : Integer.Sparse.eval row16517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16517, Integer.Sparse.eval_collectBalanced, rawRowCheck16517]

def rawRow16518 : Integer.Sparse Key := [(key1879, -2), (key1860, -2), (key1869, -2), (key1864, 6), (key1746, -2), (key1715, -2), (key1727, -2), (key1518, 2), (key1489, 2), (key1879, 2), (key1363, 2), (key1869, 2), (key1378, 2), (key1495, -2), (key1864, -2), (key1369, -2), (key1715, 6), (key1489, -2), (key1860, -2), (key1363, -2)]

theorem rawRowCheck16518 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form11 = rawRow16518 := by decide +kernel

def row16518 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16518 : row16518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16518 := by decide +kernel

theorem rowEval16518 (x : Key → ℝ) : Integer.Sparse.eval row16518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16518, Integer.Sparse.eval_collectBalanced, rawRowCheck16518]

def rawRow16519 : Integer.Sparse Key := [(key1869, -2), (key1879, -2), (key1860, -2), (key1864, 6), (key1727, -2), (key1746, -2), (key1715, -2), (key1869, 2), (key1879, 2), (key1378, 2), (key1518, 2), (key1363, 2), (key1489, 2), (key1864, -2), (key1369, -2), (key1495, -2), (key1715, 6), (key1860, -2), (key1363, -2), (key1489, -2)]

theorem rawRowCheck16519 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form11 = rawRow16519 := by decide +kernel

def row16519 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16519 : row16519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16519 := by decide +kernel

theorem rowEval16519 (x : Key → ℝ) : Integer.Sparse.eval row16519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16519, Integer.Sparse.eval_collectBalanced, rawRowCheck16519]

def rawRow16520 : Integer.Sparse Key := [(key1879, -2), (key1869, -2), (key1860, -2), (key1864, 6), (key1746, -2), (key1727, -2), (key1715, -2), (key1879, 2), (key1869, 2), (key1518, 2), (key1378, 2), (key1489, 2), (key1363, 2), (key1864, -2), (key1495, -2), (key1369, -2), (key1715, 6), (key1860, -2), (key1489, -2), (key1363, -2)]

theorem rawRowCheck16520 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form11 = rawRow16520 := by decide +kernel

def row16520 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16520 : row16520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16520 := by decide +kernel

theorem rowEval16520 (x : Key → ℝ) : Integer.Sparse.eval row16520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16520, Integer.Sparse.eval_collectBalanced, rawRowCheck16520]

def rawRow16521 : Integer.Sparse Key := [(key1864, -2), (key1869, -2), (key1879, -2), (key1860, 6), (key1864, -2), (key1869, -2), (key1879, -2), (key1369, 2), (key1378, 2), (key1495, 2), (key1727, 2), (key1518, 2), (key1746, 2), (key1363, -2), (key1489, -2), (key1715, -2), (key1860, 6), (key1363, -2), (key1489, -2), (key1715, -2)]

theorem rawRowCheck16521 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form11 = rawRow16521 := by decide +kernel

def row16521 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

theorem rowCheck16521 : row16521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16521 := by decide +kernel

theorem rowEval16521 (x : Key → ℝ) : Integer.Sparse.eval row16521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16521, Integer.Sparse.eval_collectBalanced, rawRowCheck16521]

def rawRow16522 : Integer.Sparse Key := [(key1869, -2), (key1864, -2), (key1879, -2), (key1860, 6), (key1869, -2), (key1864, -2), (key1879, -2), (key1378, 2), (key1369, 2), (key1727, 2), (key1495, 2), (key1746, 2), (key1518, 2), (key1363, -2), (key1715, -2), (key1489, -2), (key1860, 6), (key1363, -2), (key1715, -2), (key1489, -2)]

theorem rawRowCheck16522 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form11 = rawRow16522 := by decide +kernel

def row16522 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

theorem rowCheck16522 : row16522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16522 := by decide +kernel

theorem rowEval16522 (x : Key → ℝ) : Integer.Sparse.eval row16522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16522, Integer.Sparse.eval_collectBalanced, rawRowCheck16522]

def rawRow16523 : Integer.Sparse Key := [(key1864, -2), (key1879, -2), (key1869, -2), (key1860, 6), (key1864, -2), (key1879, -2), (key1869, -2), (key1495, 2), (key1518, 2), (key1369, 2), (key1746, 2), (key1378, 2), (key1727, 2), (key1489, -2), (key1363, -2), (key1715, -2), (key1860, 6), (key1489, -2), (key1363, -2), (key1715, -2)]

theorem rawRowCheck16523 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form11 = rawRow16523 := by decide +kernel

def row16523 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

theorem rowCheck16523 : row16523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16523 := by decide +kernel

theorem rowEval16523 (x : Key → ℝ) : Integer.Sparse.eval row16523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16523, Integer.Sparse.eval_collectBalanced, rawRowCheck16523]

def rawRow16524 : Integer.Sparse Key := [(key1879, -2), (key1864, -2), (key1869, -2), (key1860, 6), (key1879, -2), (key1864, -2), (key1869, -2), (key1518, 2), (key1495, 2), (key1746, 2), (key1369, 2), (key1727, 2), (key1378, 2), (key1489, -2), (key1715, -2), (key1363, -2), (key1860, 6), (key1489, -2), (key1715, -2), (key1363, -2)]

theorem rawRowCheck16524 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form11 = rawRow16524 := by decide +kernel

def row16524 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

theorem rowCheck16524 : row16524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16524 := by decide +kernel

theorem rowEval16524 (x : Key → ℝ) : Integer.Sparse.eval row16524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16524, Integer.Sparse.eval_collectBalanced, rawRowCheck16524]

def rawRow16525 : Integer.Sparse Key := [(key1869, -2), (key1879, -2), (key1864, -2), (key1860, 6), (key1869, -2), (key1879, -2), (key1864, -2), (key1727, 2), (key1746, 2), (key1378, 2), (key1518, 2), (key1369, 2), (key1495, 2), (key1715, -2), (key1363, -2), (key1489, -2), (key1860, 6), (key1715, -2), (key1363, -2), (key1489, -2)]

theorem rawRowCheck16525 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form11 = rawRow16525 := by decide +kernel

def row16525 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

theorem rowCheck16525 : row16525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16525 := by decide +kernel

theorem rowEval16525 (x : Key → ℝ) : Integer.Sparse.eval row16525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16525, Integer.Sparse.eval_collectBalanced, rawRowCheck16525]

def rawRow16526 : Integer.Sparse Key := [(key1879, -2), (key1869, -2), (key1864, -2), (key1860, 6), (key1879, -2), (key1869, -2), (key1864, -2), (key1746, 2), (key1727, 2), (key1518, 2), (key1378, 2), (key1495, 2), (key1369, 2), (key1715, -2), (key1489, -2), (key1363, -2), (key1860, 6), (key1715, -2), (key1489, -2), (key1363, -2)]

theorem rawRowCheck16526 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form11 = rawRow16526 := by decide +kernel

def row16526 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

theorem rowCheck16526 : row16526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16526 := by decide +kernel

theorem rowEval16526 (x : Key → ℝ) : Integer.Sparse.eval row16526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16526, Integer.Sparse.eval_collectBalanced, rawRowCheck16526]

def rawRow16527 : Integer.Sparse Key := [(key2407, 2), (key2441, 2), (key2441, 2), (key2410, -2), (key2410, -2), (key2445, -2), (key2848, 2), (key2970, 2), (key2970, 2), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, -1), (key2993, -1), (key2891, -2), (key2891, -2), (key2996, -2), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, -1), (key3003, -1), (key2603, 4), (key2914, 4), (key2914, 4)]

theorem rawRowCheck16527 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form12 = rawRow16527 := by decide +kernel

def row16527 : Integer.Sparse Key := [(key2407, 2), (key2410, -4), (key2441, 4), (key2445, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, -2), (key2914, 8), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, -2)]

theorem rowCheck16527 : row16527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16527 := by decide +kernel

theorem rowEval16527 (x : Key → ℝ) : Integer.Sparse.eval row16527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16527, Integer.Sparse.eval_collectBalanced, rawRowCheck16527]

def rawRow16528 : Integer.Sparse Key := [(key2441, 2), (key2407, 2), (key2441, 2), (key2410, -2), (key2445, -2), (key2410, -2), (key2970, 2), (key2848, 2), (key2970, 2), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2891, -2), (key2996, -2), (key2891, -2), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2914, 4), (key2603, 4), (key2914, 4)]

theorem rawRowCheck16528 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form12 = rawRow16528 := by decide +kernel

def row16528 : Integer.Sparse Key := [(key2407, 2), (key2410, -4), (key2441, 4), (key2445, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, -2), (key2914, 8), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, -2)]

theorem rowCheck16528 : row16528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16528 := by decide +kernel

theorem rowEval16528 (x : Key → ℝ) : Integer.Sparse.eval row16528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16528, Integer.Sparse.eval_collectBalanced, rawRowCheck16528]

def rawRow16529 : Integer.Sparse Key := [(key2441, 2), (key2441, 2), (key2407, 2), (key2445, -2), (key2410, -2), (key2410, -2), (key2970, 2), (key2970, 2), (key2848, 2), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2595, -1), (key2996, -2), (key2891, -2), (key2891, -2), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2602, -1), (key2914, 4), (key2914, 4), (key2603, 4)]

theorem rawRowCheck16529 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form12 = rawRow16529 := by decide +kernel

def row16529 : Integer.Sparse Key := [(key2407, 2), (key2410, -4), (key2441, 4), (key2445, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, -2), (key2914, 8), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, -2)]

theorem rowCheck16529 : row16529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16529 := by decide +kernel

theorem rowEval16529 (x : Key → ℝ) : Integer.Sparse.eval row16529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16529, Integer.Sparse.eval_collectBalanced, rawRowCheck16529]

def rawRow16530 : Integer.Sparse Key := [(key2410, 2), (key2441, 2), (key2445, 2), (key2407, -2), (key2410, -2), (key2441, -2), (key2882, 2), (key2991, 2), (key2993, 2), (key2592, -1), (key2595, -1), (key2848, -1), (key2882, -1), (key2970, -1), (key2991, -1), (key2912, -2), (key2914, -2), (key3003, -2), (key2602, -1), (key2603, -1), (key2891, -1), (key2914, -1), (key2996, -1), (key3003, -1), (key2602, 4), (key2891, 4), (key2912, 4)]

theorem rawRowCheck16530 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form12 = rawRow16530 := by decide +kernel

def row16530 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

theorem rowCheck16530 : row16530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16530 := by decide +kernel

theorem rowEval16530 (x : Key → ℝ) : Integer.Sparse.eval row16530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16530, Integer.Sparse.eval_collectBalanced, rawRowCheck16530]

def rawRow16531 : Integer.Sparse Key := [(key2410, 2), (key2445, 2), (key2441, 2), (key2410, -2), (key2407, -2), (key2441, -2), (key2882, 2), (key2993, 2), (key2991, 2), (key2595, -1), (key2592, -1), (key2882, -1), (key2848, -1), (key2991, -1), (key2970, -1), (key2914, -2), (key2912, -2), (key3003, -2), (key2603, -1), (key2602, -1), (key2914, -1), (key2891, -1), (key3003, -1), (key2996, -1), (key2602, 4), (key2912, 4), (key2891, 4)]

theorem rawRowCheck16531 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form12 = rawRow16531 := by decide +kernel

def row16531 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

theorem rowCheck16531 : row16531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16531 := by decide +kernel

theorem rowEval16531 (x : Key → ℝ) : Integer.Sparse.eval row16531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16531, Integer.Sparse.eval_collectBalanced, rawRowCheck16531]

def rawRow16532 : Integer.Sparse Key := [(key2441, 2), (key2410, 2), (key2445, 2), (key2407, -2), (key2441, -2), (key2410, -2), (key2991, 2), (key2882, 2), (key2993, 2), (key2848, -1), (key2970, -1), (key2592, -1), (key2991, -1), (key2595, -1), (key2882, -1), (key2912, -2), (key3003, -2), (key2914, -2), (key2891, -1), (key2996, -1), (key2602, -1), (key3003, -1), (key2603, -1), (key2914, -1), (key2891, 4), (key2602, 4), (key2912, 4)]

theorem rawRowCheck16532 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form12 = rawRow16532 := by decide +kernel

def row16532 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

theorem rowCheck16532 : row16532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16532 := by decide +kernel

theorem rowEval16532 (x : Key → ℝ) : Integer.Sparse.eval row16532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16532, Integer.Sparse.eval_collectBalanced, rawRowCheck16532]

def rawRow16533 : Integer.Sparse Key := [(key2441, 2), (key2445, 2), (key2410, 2), (key2441, -2), (key2407, -2), (key2410, -2), (key2991, 2), (key2993, 2), (key2882, 2), (key2970, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2882, -1), (key2595, -1), (key3003, -2), (key2912, -2), (key2914, -2), (key2996, -1), (key2891, -1), (key3003, -1), (key2602, -1), (key2914, -1), (key2603, -1), (key2891, 4), (key2912, 4), (key2602, 4)]

theorem rawRowCheck16533 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form12 = rawRow16533 := by decide +kernel

def row16533 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

theorem rowCheck16533 : row16533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16533 := by decide +kernel

theorem rowEval16533 (x : Key → ℝ) : Integer.Sparse.eval row16533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16533, Integer.Sparse.eval_collectBalanced, rawRowCheck16533]

def rawRow16534 : Integer.Sparse Key := [(key2445, 2), (key2410, 2), (key2441, 2), (key2410, -2), (key2441, -2), (key2407, -2), (key2993, 2), (key2882, 2), (key2991, 2), (key2882, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2592, -1), (key2848, -1), (key2914, -2), (key3003, -2), (key2912, -2), (key2914, -1), (key3003, -1), (key2603, -1), (key2996, -1), (key2602, -1), (key2891, -1), (key2912, 4), (key2602, 4), (key2891, 4)]

theorem rawRowCheck16534 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form12 = rawRow16534 := by decide +kernel

def row16534 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

theorem rowCheck16534 : row16534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16534 := by decide +kernel

theorem rowEval16534 (x : Key → ℝ) : Integer.Sparse.eval row16534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16534, Integer.Sparse.eval_collectBalanced, rawRowCheck16534]

def rawRow16535 : Integer.Sparse Key := [(key2445, 2), (key2441, 2), (key2410, 2), (key2441, -2), (key2410, -2), (key2407, -2), (key2993, 2), (key2991, 2), (key2882, 2), (key2991, -1), (key2882, -1), (key2970, -1), (key2595, -1), (key2848, -1), (key2592, -1), (key3003, -2), (key2914, -2), (key2912, -2), (key3003, -1), (key2914, -1), (key2996, -1), (key2603, -1), (key2891, -1), (key2602, -1), (key2912, 4), (key2891, 4), (key2602, 4)]

theorem rawRowCheck16535 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form12 = rawRow16535 := by decide +kernel

def row16535 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

theorem rowCheck16535 : row16535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16535 := by decide +kernel

theorem rowEval16535 (x : Key → ℝ) : Integer.Sparse.eval row16535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16535, Integer.Sparse.eval_collectBalanced, rawRowCheck16535]

def rawRow16536 : Integer.Sparse Key := [(key2473, 2), (key2507, 2), (key2507, 2), (key2483, -2), (key2483, -2), (key2526, -2), (key2407, 2), (key2441, 2), (key2441, 2), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, -1), (key3003, -1), (key2774, -2), (key2774, -2), (key2934, -2), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, -1), (key2993, -1), (key2603, 4), (key2914, 4), (key2914, 4)]

theorem rawRowCheck16536 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form12 = rawRow16536 := by decide +kernel

def row16536 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, 2), (key2483, -4), (key2507, 4), (key2526, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2774, -4), (key2882, -2), (key2912, -2), (key2914, 8), (key2934, -2), (key2993, -2), (key3003, -2)]

theorem rowCheck16536 : row16536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16536 := by decide +kernel

theorem rowEval16536 (x : Key → ℝ) : Integer.Sparse.eval row16536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16536, Integer.Sparse.eval_collectBalanced, rawRowCheck16536]

def rawRow16537 : Integer.Sparse Key := [(key2507, 2), (key2473, 2), (key2507, 2), (key2483, -2), (key2526, -2), (key2483, -2), (key2441, 2), (key2407, 2), (key2441, 2), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2774, -2), (key2934, -2), (key2774, -2), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2914, 4), (key2603, 4), (key2914, 4)]

theorem rawRowCheck16537 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form12 = rawRow16537 := by decide +kernel

def row16537 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, 2), (key2483, -4), (key2507, 4), (key2526, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2774, -4), (key2882, -2), (key2912, -2), (key2914, 8), (key2934, -2), (key2993, -2), (key3003, -2)]

theorem rowCheck16537 : row16537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16537 := by decide +kernel

theorem rowEval16537 (x : Key → ℝ) : Integer.Sparse.eval row16537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16537, Integer.Sparse.eval_collectBalanced, rawRowCheck16537]

def rawRow16538 : Integer.Sparse Key := [(key2507, 2), (key2507, 2), (key2473, 2), (key2526, -2), (key2483, -2), (key2483, -2), (key2441, 2), (key2441, 2), (key2407, 2), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2602, -1), (key2934, -2), (key2774, -2), (key2774, -2), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2595, -1), (key2914, 4), (key2914, 4), (key2603, 4)]

theorem rawRowCheck16538 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form12 = rawRow16538 := by decide +kernel

def row16538 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, 2), (key2483, -4), (key2507, 4), (key2526, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2774, -4), (key2882, -2), (key2912, -2), (key2914, 8), (key2934, -2), (key2993, -2), (key3003, -2)]

theorem rowCheck16538 : row16538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16538 := by decide +kernel

theorem rowEval16538 (x : Key → ℝ) : Integer.Sparse.eval row16538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16538, Integer.Sparse.eval_collectBalanced, rawRowCheck16538]

def rawRow16539 : Integer.Sparse Key := [(key2483, 2), (key2507, 2), (key2526, 2), (key2473, -2), (key2483, -2), (key2507, -2), (key2544, 2), (key2555, 2), (key2565, 2), (key2379, -1), (key2393, -1), (key2771, -1), (key2912, -1), (key2933, -1), (key2991, -1), (key2882, -2), (key2914, -2), (key2993, -2), (key2595, -1), (key2603, -1), (key2774, -1), (key2914, -1), (key2934, -1), (key2993, -1), (key2595, 4), (key2774, 4), (key2882, 4)]

theorem rawRowCheck16539 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form12 = rawRow16539 := by decide +kernel

def row16539 : Integer.Sparse Key := [(key2379, -1), (key2393, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2595, 3), (key2603, -1), (key2771, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2933, -1), (key2934, -1), (key2991, -1), (key2993, -3)]

theorem rowCheck16539 : row16539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16539 := by decide +kernel

theorem rowEval16539 (x : Key → ℝ) : Integer.Sparse.eval row16539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16539, Integer.Sparse.eval_collectBalanced, rawRowCheck16539]

def rawRow16540 : Integer.Sparse Key := [(key2483, 2), (key2526, 2), (key2507, 2), (key2483, -2), (key2473, -2), (key2507, -2), (key2544, 2), (key2565, 2), (key2555, 2), (key2393, -1), (key2379, -1), (key2912, -1), (key2771, -1), (key2991, -1), (key2933, -1), (key2914, -2), (key2882, -2), (key2993, -2), (key2603, -1), (key2595, -1), (key2914, -1), (key2774, -1), (key2993, -1), (key2934, -1), (key2595, 4), (key2882, 4), (key2774, 4)]

theorem rawRowCheck16540 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form12 = rawRow16540 := by decide +kernel

def row16540 : Integer.Sparse Key := [(key2379, -1), (key2393, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2595, 3), (key2603, -1), (key2771, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2933, -1), (key2934, -1), (key2991, -1), (key2993, -3)]

theorem rowCheck16540 : row16540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16540 := by decide +kernel

theorem rowEval16540 (x : Key → ℝ) : Integer.Sparse.eval row16540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16540, Integer.Sparse.eval_collectBalanced, rawRowCheck16540]

def rawRow16541 : Integer.Sparse Key := [(key2507, 2), (key2483, 2), (key2526, 2), (key2473, -2), (key2507, -2), (key2483, -2), (key2555, 2), (key2544, 2), (key2565, 2), (key2407, -1), (key2441, -1), (key2592, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2882, -2), (key2993, -2), (key2914, -2), (key2774, -1), (key2934, -1), (key2595, -1), (key2993, -1), (key2603, -1), (key2914, -1), (key2774, 4), (key2595, 4), (key2882, 4)]

theorem rawRowCheck16541 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form12 = rawRow16541 := by decide +kernel

def row16541 : Integer.Sparse Key := [(key2407, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2592, -1), (key2595, 3), (key2602, -1), (key2603, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2934, -1), (key2991, -1), (key2993, -3)]

theorem rowCheck16541 : row16541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16541 := by decide +kernel

theorem rowEval16541 (x : Key → ℝ) : Integer.Sparse.eval row16541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16541, Integer.Sparse.eval_collectBalanced, rawRowCheck16541]

def rawRow16542 : Integer.Sparse Key := [(key2507, 2), (key2526, 2), (key2483, 2), (key2507, -2), (key2473, -2), (key2483, -2), (key2555, 2), (key2565, 2), (key2544, 2), (key2441, -1), (key2407, -1), (key2991, -1), (key2592, -1), (key2912, -1), (key2602, -1), (key2993, -2), (key2882, -2), (key2914, -2), (key2934, -1), (key2774, -1), (key2993, -1), (key2595, -1), (key2914, -1), (key2603, -1), (key2774, 4), (key2882, 4), (key2595, 4)]

theorem rawRowCheck16542 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form12 = rawRow16542 := by decide +kernel

def row16542 : Integer.Sparse Key := [(key2407, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2592, -1), (key2595, 3), (key2602, -1), (key2603, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2934, -1), (key2991, -1), (key2993, -3)]

theorem rowCheck16542 : row16542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16542 := by decide +kernel

theorem rowEval16542 (x : Key → ℝ) : Integer.Sparse.eval row16542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16542, Integer.Sparse.eval_collectBalanced, rawRowCheck16542]

def rawRow16543 : Integer.Sparse Key := [(key2526, 2), (key2483, 2), (key2507, 2), (key2483, -2), (key2507, -2), (key2473, -2), (key2565, 2), (key2544, 2), (key2555, 2), (key2544, -1), (key2555, -1), (key2393, -1), (key2441, -1), (key2379, -1), (key2771, -1), (key2914, -2), (key2993, -2), (key2882, -2), (key2914, -1), (key2993, -1), (key2603, -1), (key2934, -1), (key2595, -1), (key2774, -1), (key2882, 4), (key2595, 4), (key2774, 4)]

theorem rawRowCheck16543 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form12 = rawRow16543 := by decide +kernel

def row16543 : Integer.Sparse Key := [(key2379, -1), (key2393, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 1), (key2555, 1), (key2565, 2), (key2595, 3), (key2603, -1), (key2771, -1), (key2774, 3), (key2882, 2), (key2914, -3), (key2934, -1), (key2993, -3)]

theorem rowCheck16543 : row16543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16543 := by decide +kernel

theorem rowEval16543 (x : Key → ℝ) : Integer.Sparse.eval row16543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16543, Integer.Sparse.eval_collectBalanced, rawRowCheck16543]

def rawRow16544 : Integer.Sparse Key := [(key2526, 2), (key2507, 2), (key2483, 2), (key2507, -2), (key2483, -2), (key2473, -2), (key2565, 2), (key2555, 2), (key2544, 2), (key2555, -1), (key2544, -1), (key2441, -1), (key2393, -1), (key2407, -1), (key2592, -1), (key2993, -2), (key2914, -2), (key2882, -2), (key2993, -1), (key2914, -1), (key2934, -1), (key2603, -1), (key2774, -1), (key2595, -1), (key2882, 4), (key2774, 4), (key2595, 4)]

theorem rawRowCheck16544 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form12 = rawRow16544 := by decide +kernel

def row16544 : Integer.Sparse Key := [(key2393, -1), (key2407, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 1), (key2555, 1), (key2565, 2), (key2592, -1), (key2595, 3), (key2603, -1), (key2774, 3), (key2882, 2), (key2914, -3), (key2934, -1), (key2993, -3)]

theorem rowCheck16544 : row16544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16544 := by decide +kernel

theorem rowEval16544 (x : Key → ℝ) : Integer.Sparse.eval row16544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16544, Integer.Sparse.eval_collectBalanced, rawRowCheck16544]

def rawRow16545 : Integer.Sparse Key := [(key2539, 2), (key2555, 2), (key2557, 2), (key2544, -2), (key2545, -2), (key2565, -2), (key2410, 2), (key2441, 2), (key2445, 2), (key2393, -1), (key2395, -1), (key2483, -1), (key2545, -1), (key2526, -1), (key2565, -1), (key2407, -2), (key2410, -2), (key2441, -2), (key2592, -1), (key2595, -1), (key2848, -1), (key2882, -1), (key2970, -1), (key2991, -1), (key2602, 4), (key2891, 4), (key2912, 4)]

theorem rawRowCheck16545 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form12 = rawRow16545 := by decide +kernel

def row16545 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

theorem rowCheck16545 : row16545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16545 := by decide +kernel

theorem rowEval16545 (x : Key → ℝ) : Integer.Sparse.eval row16545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16545, Integer.Sparse.eval_collectBalanced, rawRowCheck16545]

def rawRow16546 : Integer.Sparse Key := [(key2539, 2), (key2557, 2), (key2555, 2), (key2545, -2), (key2544, -2), (key2565, -2), (key2410, 2), (key2445, 2), (key2441, 2), (key2395, -1), (key2393, -1), (key2545, -1), (key2483, -1), (key2565, -1), (key2526, -1), (key2410, -2), (key2407, -2), (key2441, -2), (key2595, -1), (key2592, -1), (key2882, -1), (key2848, -1), (key2991, -1), (key2970, -1), (key2602, 4), (key2912, 4), (key2891, 4)]

theorem rawRowCheck16546 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form12 = rawRow16546 := by decide +kernel

def row16546 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

theorem rowCheck16546 : row16546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16546 := by decide +kernel

theorem rowEval16546 (x : Key → ℝ) : Integer.Sparse.eval row16546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16546, Integer.Sparse.eval_collectBalanced, rawRowCheck16546]

def rawRow16547 : Integer.Sparse Key := [(key2555, 2), (key2539, 2), (key2557, 2), (key2544, -2), (key2565, -2), (key2545, -2), (key2441, 2), (key2410, 2), (key2445, 2), (key2483, -1), (key2526, -1), (key2393, -1), (key2565, -1), (key2395, -1), (key2545, -1), (key2407, -2), (key2441, -2), (key2410, -2), (key2848, -1), (key2970, -1), (key2592, -1), (key2991, -1), (key2595, -1), (key2882, -1), (key2891, 4), (key2602, 4), (key2912, 4)]

theorem rawRowCheck16547 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form12 = rawRow16547 := by decide +kernel

def row16547 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

theorem rowCheck16547 : row16547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16547 := by decide +kernel

theorem rowEval16547 (x : Key → ℝ) : Integer.Sparse.eval row16547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16547, Integer.Sparse.eval_collectBalanced, rawRowCheck16547]

def rawRow16548 : Integer.Sparse Key := [(key2555, 2), (key2557, 2), (key2539, 2), (key2565, -2), (key2544, -2), (key2545, -2), (key2441, 2), (key2445, 2), (key2410, 2), (key2526, -1), (key2483, -1), (key2565, -1), (key2393, -1), (key2545, -1), (key2395, -1), (key2441, -2), (key2407, -2), (key2410, -2), (key2970, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2882, -1), (key2595, -1), (key2891, 4), (key2912, 4), (key2602, 4)]

theorem rawRowCheck16548 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form12 = rawRow16548 := by decide +kernel

def row16548 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

theorem rowCheck16548 : row16548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16548 := by decide +kernel

theorem rowEval16548 (x : Key → ℝ) : Integer.Sparse.eval row16548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16548, Integer.Sparse.eval_collectBalanced, rawRowCheck16548]

def rawRow16549 : Integer.Sparse Key := [(key2557, 2), (key2539, 2), (key2555, 2), (key2545, -2), (key2565, -2), (key2544, -2), (key2445, 2), (key2410, 2), (key2441, 2), (key2545, -1), (key2565, -1), (key2395, -1), (key2526, -1), (key2393, -1), (key2483, -1), (key2410, -2), (key2441, -2), (key2407, -2), (key2882, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2592, -1), (key2848, -1), (key2912, 4), (key2602, 4), (key2891, 4)]

theorem rawRowCheck16549 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form12 = rawRow16549 := by decide +kernel

def row16549 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

theorem rowCheck16549 : row16549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16549 := by decide +kernel

theorem rowEval16549 (x : Key → ℝ) : Integer.Sparse.eval row16549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16549, Integer.Sparse.eval_collectBalanced, rawRowCheck16549]

def rawRow16550 : Integer.Sparse Key := [(key2557, 2), (key2555, 2), (key2539, 2), (key2565, -2), (key2545, -2), (key2544, -2), (key2445, 2), (key2441, 2), (key2410, 2), (key2565, -1), (key2545, -1), (key2526, -1), (key2395, -1), (key2483, -1), (key2393, -1), (key2441, -2), (key2410, -2), (key2407, -2), (key2991, -1), (key2882, -1), (key2970, -1), (key2595, -1), (key2848, -1), (key2592, -1), (key2912, 4), (key2891, 4), (key2602, 4)]

theorem rawRowCheck16550 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form12 = rawRow16550 := by decide +kernel

def row16550 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

theorem rowCheck16550 : row16550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16550 := by decide +kernel

theorem rowEval16550 (x : Key → ℝ) : Integer.Sparse.eval row16550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16550, Integer.Sparse.eval_collectBalanced, rawRowCheck16550]

def rawRow16551 : Integer.Sparse Key := [(key2544, 2), (key2555, 2), (key2565, 2), (key2539, -2), (key2545, -2), (key2557, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2382, -1), (key2395, -1), (key2410, -1), (key2545, -1), (key2445, -1), (key2557, -1), (key2473, -2), (key2483, -2), (key2507, -2), (key2379, -1), (key2393, -1), (key2771, -1), (key2912, -1), (key2933, -1), (key2991, -1), (key2595, 4), (key2774, 4), (key2882, 4)]

theorem rawRowCheck16551 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form12 = rawRow16551 := by decide +kernel

def row16551 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, -1), (key2395, -1), (key2410, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2595, 4), (key2771, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2933, -1), (key2991, -1)]

theorem rowCheck16551 : row16551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16551 := by decide +kernel

theorem rowEval16551 (x : Key → ℝ) : Integer.Sparse.eval row16551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16551, Integer.Sparse.eval_collectBalanced, rawRowCheck16551]

def rawRow16552 : Integer.Sparse Key := [(key2544, 2), (key2565, 2), (key2555, 2), (key2545, -2), (key2539, -2), (key2557, -2), (key2483, 2), (key2526, 2), (key2507, 2), (key2395, -1), (key2382, -1), (key2545, -1), (key2410, -1), (key2557, -1), (key2445, -1), (key2483, -2), (key2473, -2), (key2507, -2), (key2393, -1), (key2379, -1), (key2912, -1), (key2771, -1), (key2991, -1), (key2933, -1), (key2595, 4), (key2882, 4), (key2774, 4)]

theorem rawRowCheck16552 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form12 = rawRow16552 := by decide +kernel

def row16552 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, -1), (key2395, -1), (key2410, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2595, 4), (key2771, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2933, -1), (key2991, -1)]

theorem rowCheck16552 : row16552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16552 := by decide +kernel

theorem rowEval16552 (x : Key → ℝ) : Integer.Sparse.eval row16552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16552, Integer.Sparse.eval_collectBalanced, rawRowCheck16552]

def rawRow16553 : Integer.Sparse Key := [(key2555, 2), (key2544, 2), (key2565, 2), (key2539, -2), (key2557, -2), (key2545, -2), (key2507, 2), (key2483, 2), (key2526, 2), (key2410, -1), (key2445, -1), (key2382, -1), (key2557, -1), (key2395, -1), (key2545, -1), (key2473, -2), (key2507, -2), (key2483, -2), (key2407, -1), (key2441, -1), (key2592, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2774, 4), (key2595, 4), (key2882, 4)]

theorem rawRowCheck16553 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form12 = rawRow16553 := by decide +kernel

def row16553 : Integer.Sparse Key := [(key2382, -1), (key2395, -1), (key2407, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2592, -1), (key2595, 4), (key2602, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2991, -1)]

theorem rowCheck16553 : row16553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16553 := by decide +kernel

theorem rowEval16553 (x : Key → ℝ) : Integer.Sparse.eval row16553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16553, Integer.Sparse.eval_collectBalanced, rawRowCheck16553]

def rawRow16554 : Integer.Sparse Key := [(key2555, 2), (key2565, 2), (key2544, 2), (key2557, -2), (key2539, -2), (key2545, -2), (key2507, 2), (key2526, 2), (key2483, 2), (key2445, -1), (key2410, -1), (key2557, -1), (key2382, -1), (key2545, -1), (key2395, -1), (key2507, -2), (key2473, -2), (key2483, -2), (key2441, -1), (key2407, -1), (key2991, -1), (key2592, -1), (key2912, -1), (key2602, -1), (key2774, 4), (key2882, 4), (key2595, 4)]

theorem rawRowCheck16554 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form12 = rawRow16554 := by decide +kernel

def row16554 : Integer.Sparse Key := [(key2382, -1), (key2395, -1), (key2407, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2592, -1), (key2595, 4), (key2602, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2991, -1)]

theorem rowCheck16554 : row16554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16554 := by decide +kernel

theorem rowEval16554 (x : Key → ℝ) : Integer.Sparse.eval row16554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16554, Integer.Sparse.eval_collectBalanced, rawRowCheck16554]

def rawRow16555 : Integer.Sparse Key := [(key2565, 2), (key2544, 2), (key2555, 2), (key2545, -2), (key2557, -2), (key2539, -2), (key2526, 2), (key2483, 2), (key2507, 2), (key2545, -1), (key2557, -1), (key2395, -1), (key2445, -1), (key2382, -1), (key2410, -1), (key2483, -2), (key2507, -2), (key2473, -2), (key2544, -1), (key2555, -1), (key2393, -1), (key2441, -1), (key2379, -1), (key2771, -1), (key2882, 4), (key2595, 4), (key2774, 4)]

theorem rawRowCheck16555 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form12 = rawRow16555 := by decide +kernel

def row16555 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, -1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, -3), (key2555, 1), (key2557, -3), (key2565, 2), (key2595, 4), (key2771, -1), (key2774, 4), (key2882, 4)]

theorem rowCheck16555 : row16555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16555 := by decide +kernel

theorem rowEval16555 (x : Key → ℝ) : Integer.Sparse.eval row16555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16555, Integer.Sparse.eval_collectBalanced, rawRowCheck16555]

def rawRow16556 : Integer.Sparse Key := [(key2565, 2), (key2555, 2), (key2544, 2), (key2557, -2), (key2545, -2), (key2539, -2), (key2526, 2), (key2507, 2), (key2483, 2), (key2557, -1), (key2545, -1), (key2445, -1), (key2395, -1), (key2410, -1), (key2382, -1), (key2507, -2), (key2483, -2), (key2473, -2), (key2555, -1), (key2544, -1), (key2441, -1), (key2393, -1), (key2407, -1), (key2592, -1), (key2882, 4), (key2774, 4), (key2595, 4)]

theorem rawRowCheck16556 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form12 = rawRow16556 := by decide +kernel

def row16556 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, -1), (key2407, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, -3), (key2555, 1), (key2557, -3), (key2565, 2), (key2592, -1), (key2595, 4), (key2774, 4), (key2882, 4)]

theorem rowCheck16556 : row16556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16556 := by decide +kernel

theorem rowEval16556 (x : Key → ℝ) : Integer.Sparse.eval row16556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16556, Integer.Sparse.eval_collectBalanced, rawRowCheck16556]

def rawRow16557 : Integer.Sparse Key := [(key2545, 2), (key2557, 2), (key2565, 2), (key2539, -2), (key2544, -2), (key2555, -2), (key2545, 2), (key2557, 2), (key2565, 2), (key2382, -1), (key2393, -1), (key2410, -1), (key2483, -1), (key2441, -1), (key2507, -1), (key2539, -2), (key2544, -2), (key2555, -2), (key2382, -1), (key2393, -1), (key2410, -1), (key2483, -1), (key2441, -1), (key2507, -1), (key2379, 4), (key2771, 4), (key2848, 4)]

theorem rawRowCheck16557 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form12 = rawRow16557 := by decide +kernel

def row16557 : Integer.Sparse Key := [(key2379, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2771, 4), (key2848, 4)]

theorem rowCheck16557 : row16557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16557 := by decide +kernel

theorem rowEval16557 (x : Key → ℝ) : Integer.Sparse.eval row16557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16557, Integer.Sparse.eval_collectBalanced, rawRowCheck16557]

def rawRow16558 : Integer.Sparse Key := [(key2545, 2), (key2565, 2), (key2557, 2), (key2544, -2), (key2539, -2), (key2555, -2), (key2545, 2), (key2565, 2), (key2557, 2), (key2393, -1), (key2382, -1), (key2483, -1), (key2410, -1), (key2507, -1), (key2441, -1), (key2544, -2), (key2539, -2), (key2555, -2), (key2393, -1), (key2382, -1), (key2483, -1), (key2410, -1), (key2507, -1), (key2441, -1), (key2379, 4), (key2848, 4), (key2771, 4)]

theorem rawRowCheck16558 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form12 = rawRow16558 := by decide +kernel

def row16558 : Integer.Sparse Key := [(key2379, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2771, 4), (key2848, 4)]

theorem rowCheck16558 : row16558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16558 := by decide +kernel

theorem rowEval16558 (x : Key → ℝ) : Integer.Sparse.eval row16558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16558, Integer.Sparse.eval_collectBalanced, rawRowCheck16558]

def rawRow16559 : Integer.Sparse Key := [(key2557, 2), (key2545, 2), (key2565, 2), (key2539, -2), (key2555, -2), (key2544, -2), (key2557, 2), (key2545, 2), (key2565, 2), (key2410, -1), (key2441, -1), (key2382, -1), (key2507, -1), (key2393, -1), (key2483, -1), (key2539, -2), (key2555, -2), (key2544, -2), (key2410, -1), (key2441, -1), (key2382, -1), (key2507, -1), (key2393, -1), (key2483, -1), (key2407, 4), (key2592, 4), (key2848, 4)]

theorem rawRowCheck16559 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form12 = rawRow16559 := by decide +kernel

def row16559 : Integer.Sparse Key := [(key2382, -2), (key2393, -2), (key2407, 4), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2592, 4), (key2848, 4)]

theorem rowCheck16559 : row16559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16559 := by decide +kernel

theorem rowEval16559 (x : Key → ℝ) : Integer.Sparse.eval row16559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck16559, Integer.Sparse.eval_collectBalanced, rawRowCheck16559]

def rawRow16560 : Integer.Sparse Key := [(key2557, 2), (key2565, 2), (key2545, 2), (key2555, -2), (key2539, -2), (key2544, -2), (key2557, 2), (key2565, 2), (key2545, 2), (key2441, -1), (key2410, -1), (key2507, -1), (key2382, -1), (key2483, -1), (key2393, -1), (key2555, -2), (key2539, -2), (key2544, -2), (key2441, -1), (key2410, -1), (key2507, -1), (key2382, -1), (key2483, -1), (key2393, -1), (key2407, 4), (key2848, 4), (key2592, 4)]

theorem rawRowCheck16560 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form12 = rawRow16560 := by decide +kernel

def row16560 : Integer.Sparse Key := [(key2382, -2), (key2393, -2), (key2407, 4), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2592, 4), (key2848, 4)]

theorem rowCheck16560 : row16560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16560 := by decide +kernel

theorem rowEval16560 (x : Key → ℝ) : Integer.Sparse.eval row16560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16560, Integer.Sparse.eval_collectBalanced, rawRowCheck16560]

def rawRow16561 : Integer.Sparse Key := [(key2565, 2), (key2545, 2), (key2557, 2), (key2544, -2), (key2555, -2), (key2539, -2), (key2565, 2), (key2545, 2), (key2557, 2), (key2483, -1), (key2507, -1), (key2393, -1), (key2441, -1), (key2382, -1), (key2410, -1), (key2544, -2), (key2555, -2), (key2539, -2), (key2483, -1), (key2507, -1), (key2393, -1), (key2441, -1), (key2382, -1), (key2410, -1), (key2473, 4), (key2379, 4), (key2771, 4)]

theorem rawRowCheck16561 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form12 = rawRow16561 := by decide +kernel

def row16561 : Integer.Sparse Key := [(key2379, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2441, -2), (key2473, 4), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2771, 4)]

theorem rowCheck16561 : row16561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16561 := by decide +kernel

theorem rowEval16561 (x : Key → ℝ) : Integer.Sparse.eval row16561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck16561, Integer.Sparse.eval_collectBalanced, rawRowCheck16561]

def rawRow16562 : Integer.Sparse Key := [(key2565, 2), (key2557, 2), (key2545, 2), (key2555, -2), (key2544, -2), (key2539, -2), (key2565, 2), (key2557, 2), (key2545, 2), (key2507, -1), (key2483, -1), (key2441, -1), (key2393, -1), (key2410, -1), (key2382, -1), (key2555, -2), (key2544, -2), (key2539, -2), (key2507, -1), (key2483, -1), (key2441, -1), (key2393, -1), (key2410, -1), (key2382, -1), (key2473, 4), (key2407, 4), (key2592, 4)]

theorem rawRowCheck16562 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form12 = rawRow16562 := by decide +kernel

def row16562 : Integer.Sparse Key := [(key2382, -2), (key2393, -2), (key2407, 4), (key2410, -2), (key2441, -2), (key2473, 4), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2592, 4)]

theorem rowCheck16562 : row16562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16562 := by decide +kernel

theorem rowEval16562 (x : Key → ℝ) : Integer.Sparse.eval row16562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck16562, Integer.Sparse.eval_collectBalanced, rawRowCheck16562]

def rawRow16563 : Integer.Sparse Key := [(key2702, 2), (key2702, 2), (key2728, 2), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2805, 2), (key2805, 2), (key2831, 2), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key3023, -1), (key3023, -1), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key3026, -1), (key3026, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2)]

theorem rawRowCheck16563 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form13 = rawRow16563 := by decide +kernel

def row16563 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2706, -2), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2805, 4), (key2829, -2), (key2831, 2), (key2860, -2), (key2870, -2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck16563 : row16563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16563 := by decide +kernel

theorem rowEval16563 (x : Key → ℝ) : Integer.Sparse.eval row16563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16563, Integer.Sparse.eval_collectBalanced, rawRowCheck16563]

def rawRow16564 : Integer.Sparse Key := [(key2702, 2), (key2728, 2), (key2702, 2), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2805, 2), (key2831, 2), (key2805, 2), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2870, -1), (key3026, -1), (key2632, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2)]

theorem rawRowCheck16564 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form13 = rawRow16564 := by decide +kernel

def row16564 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2706, -2), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, -2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck16564 : row16564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16564 := by decide +kernel

theorem rowEval16564 (x : Key → ℝ) : Integer.Sparse.eval row16564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16564, Integer.Sparse.eval_collectBalanced, rawRowCheck16564]

def rawRow16565 : Integer.Sparse Key := [(key2728, 2), (key2702, 2), (key2702, 2), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2831, 2), (key2805, 2), (key2805, 2), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3023, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key3026, -1), (key2870, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2)]

theorem rawRowCheck16565 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form13 = rawRow16565 := by decide +kernel

def row16565 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2706, -2), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, -2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck16565 : row16565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16565 := by decide +kernel

theorem rowEval16565 (x : Key → ℝ) : Integer.Sparse.eval row16565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16565, Integer.Sparse.eval_collectBalanced, rawRowCheck16565]

def rawRow16566 : Integer.Sparse Key := [(key2735, 2), (key2737, 2), (key2747, 2), (key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2948, 2), (key2950, 2), (key2960, 2), (key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2726, -1), (key2732, -1), (key2870, -1), (key2885, -1), (key3026, -1), (key3030, -1), (key2640, -1), (key2644, -1), (key2860, -1), (key2885, -1), (key3023, -1), (key3030, -1), (key2632, 2), (key2644, 2), (key2706, 2), (key2732, 2), (key3023, 2), (key3026, 2)]

theorem rawRowCheck16566 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form13 = rawRow16566 := by decide +kernel

def row16566 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck16566 : row16566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16566 := by decide +kernel

theorem rowEval16566 (x : Key → ℝ) : Integer.Sparse.eval row16566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16566, Integer.Sparse.eval_collectBalanced, rawRowCheck16566]

def rawRow16567 : Integer.Sparse Key := [(key2737, 2), (key2735, 2), (key2747, 2), (key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2950, 2), (key2948, 2), (key2960, 2), (key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2732, -1), (key2726, -1), (key2885, -1), (key2870, -1), (key3030, -1), (key3026, -1), (key2644, -1), (key2640, -1), (key2885, -1), (key2860, -1), (key3030, -1), (key3023, -1), (key2644, 2), (key2632, 2), (key2732, 2), (key2706, 2), (key3026, 2), (key3023, 2)]

theorem rawRowCheck16567 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form13 = rawRow16567 := by decide +kernel

def row16567 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck16567 : row16567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16567 := by decide +kernel

theorem rowEval16567 (x : Key → ℝ) : Integer.Sparse.eval row16567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16567, Integer.Sparse.eval_collectBalanced, rawRowCheck16567]

def rawRow16568 : Integer.Sparse Key := [(key2735, 2), (key2747, 2), (key2737, 2), (key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2948, 2), (key2960, 2), (key2950, 2), (key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2870, -1), (key3026, -1), (key2726, -1), (key3030, -1), (key2732, -1), (key2885, -1), (key2860, -1), (key3023, -1), (key2640, -1), (key3030, -1), (key2644, -1), (key2885, -1), (key2706, 2), (key3023, 2), (key2632, 2), (key3026, 2), (key2644, 2), (key2732, 2)]

theorem rawRowCheck16568 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form13 = rawRow16568 := by decide +kernel

def row16568 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck16568 : row16568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16568 := by decide +kernel

theorem rowEval16568 (x : Key → ℝ) : Integer.Sparse.eval row16568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16568, Integer.Sparse.eval_collectBalanced, rawRowCheck16568]

def rawRow16569 : Integer.Sparse Key := [(key2747, 2), (key2735, 2), (key2737, 2), (key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2960, 2), (key2948, 2), (key2950, 2), (key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key3026, -1), (key2870, -1), (key3030, -1), (key2726, -1), (key2885, -1), (key2732, -1), (key3023, -1), (key2860, -1), (key3030, -1), (key2640, -1), (key2885, -1), (key2644, -1), (key3023, 2), (key2706, 2), (key3026, 2), (key2632, 2), (key2732, 2), (key2644, 2)]

theorem rawRowCheck16569 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form13 = rawRow16569 := by decide +kernel

def row16569 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck16569 : row16569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16569 := by decide +kernel

theorem rowEval16569 (x : Key → ℝ) : Integer.Sparse.eval row16569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16569, Integer.Sparse.eval_collectBalanced, rawRowCheck16569]

def rawRow16570 : Integer.Sparse Key := [(key2737, 2), (key2747, 2), (key2735, 2), (key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2950, 2), (key2960, 2), (key2948, 2), (key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2885, -1), (key3030, -1), (key2732, -1), (key3026, -1), (key2726, -1), (key2870, -1), (key2885, -1), (key3030, -1), (key2644, -1), (key3023, -1), (key2640, -1), (key2860, -1), (key2732, 2), (key3026, 2), (key2644, 2), (key3023, 2), (key2632, 2), (key2706, 2)]

theorem rawRowCheck16570 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form13 = rawRow16570 := by decide +kernel

def row16570 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck16570 : row16570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16570 := by decide +kernel

theorem rowEval16570 (x : Key → ℝ) : Integer.Sparse.eval row16570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16570, Integer.Sparse.eval_collectBalanced, rawRowCheck16570]

def rawRow16571 : Integer.Sparse Key := [(key2747, 2), (key2737, 2), (key2735, 2), (key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2960, 2), (key2950, 2), (key2948, 2), (key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key3030, -1), (key2885, -1), (key3026, -1), (key2732, -1), (key2870, -1), (key2726, -1), (key3030, -1), (key2885, -1), (key3023, -1), (key2644, -1), (key2860, -1), (key2640, -1), (key3026, 2), (key2732, 2), (key3023, 2), (key2644, 2), (key2706, 2), (key2632, 2)]

theorem rawRowCheck16571 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form13 = rawRow16571 := by decide +kernel

def row16571 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck16571 : row16571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16571 := by decide +kernel

theorem rowEval16571 (x : Key → ℝ) : Integer.Sparse.eval row16571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16571, Integer.Sparse.eval_collectBalanced, rawRowCheck16571]

def rawRow16572 : Integer.Sparse Key := [(key2805, 2), (key2805, 2), (key2831, 2), (key2782, -1), (key2782, -1), (key2893, -1), (key2893, -1), (key2904, -1), (key2904, -1), (key2702, 2), (key2702, 2), (key2728, 2), (key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2)]

theorem rawRowCheck16572 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form13 = rawRow16572 := by decide +kernel

def row16572 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2805, 4), (key2829, -2), (key2831, 2), (key2893, -2), (key2904, -2), (key2972, -2), (key2983, -2), (key3017, -2), (key3030, 4)]

theorem rowCheck16572 : row16572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16572 := by decide +kernel

theorem rowEval16572 (x : Key → ℝ) : Integer.Sparse.eval row16572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16572, Integer.Sparse.eval_collectBalanced, rawRowCheck16572]

def rawRow16573 : Integer.Sparse Key := [(key2805, 2), (key2831, 2), (key2805, 2), (key2893, -1), (key2904, -1), (key2782, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2702, 2), (key2728, 2), (key2702, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2)]

theorem rawRowCheck16573 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form13 = rawRow16573 := by decide +kernel

def row16573 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2893, -2), (key2904, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2983, -2), (key3030, 4)]

theorem rowCheck16573 : row16573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16573 := by decide +kernel

theorem rowEval16573 (x : Key → ℝ) : Integer.Sparse.eval row16573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16573, Integer.Sparse.eval_collectBalanced, rawRowCheck16573]

def rawRow16574 : Integer.Sparse Key := [(key2831, 2), (key2805, 2), (key2805, 2), (key2904, -1), (key2893, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2782, -1), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2)]

theorem rawRowCheck16574 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form13 = rawRow16574 := by decide +kernel

def row16574 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2893, -2), (key2904, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2983, -2), (key3030, 4)]

theorem rowCheck16574 : row16574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16574 := by decide +kernel

theorem rowEval16574 (x : Key → ℝ) : Integer.Sparse.eval row16574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16574, Integer.Sparse.eval_collectBalanced, rawRowCheck16574]

def rawRow16575 : Integer.Sparse Key := [(key2893, 2), (key2897, 2), (key2904, 2), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2972, 2), (key2976, 2), (key2983, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2)]

theorem rawRowCheck16575 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form13 = rawRow16575 := by decide +kernel

def row16575 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16575 : row16575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16575 := by decide +kernel

theorem rowEval16575 (x : Key → ℝ) : Integer.Sparse.eval row16575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16575, Integer.Sparse.eval_collectBalanced, rawRowCheck16575]

def rawRow16576 : Integer.Sparse Key := [(key2897, 2), (key2893, 2), (key2904, 2), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2976, 2), (key2972, 2), (key2983, 2), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2)]

theorem rawRowCheck16576 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form13 = rawRow16576 := by decide +kernel

def row16576 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16576 : row16576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16576 := by decide +kernel

theorem rowEval16576 (x : Key → ℝ) : Integer.Sparse.eval row16576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16576, Integer.Sparse.eval_collectBalanced, rawRowCheck16576]

def rawRow16577 : Integer.Sparse Key := [(key2893, 2), (key2904, 2), (key2897, 2), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2972, 2), (key2983, 2), (key2976, 2), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2)]

theorem rawRowCheck16577 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form13 = rawRow16577 := by decide +kernel

def row16577 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16577 : row16577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16577 := by decide +kernel

theorem rowEval16577 (x : Key → ℝ) : Integer.Sparse.eval row16577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16577, Integer.Sparse.eval_collectBalanced, rawRowCheck16577]

def rawRow16578 : Integer.Sparse Key := [(key2904, 2), (key2893, 2), (key2897, 2), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2983, 2), (key2972, 2), (key2976, 2), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2)]

theorem rawRowCheck16578 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form13 = rawRow16578 := by decide +kernel

def row16578 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16578 : row16578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16578 := by decide +kernel

theorem rowEval16578 (x : Key → ℝ) : Integer.Sparse.eval row16578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16578, Integer.Sparse.eval_collectBalanced, rawRowCheck16578]

def rawRow16579 : Integer.Sparse Key := [(key2897, 2), (key2904, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, 2), (key2983, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2)]

theorem rawRowCheck16579 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form13 = rawRow16579 := by decide +kernel

def row16579 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16579 : row16579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16579 := by decide +kernel

theorem rowEval16579 (x : Key → ℝ) : Integer.Sparse.eval row16579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16579, Integer.Sparse.eval_collectBalanced, rawRowCheck16579]

def rawRow16580 : Integer.Sparse Key := [(key2904, 2), (key2897, 2), (key2893, 2), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, 2), (key2976, 2), (key2972, 2), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2)]

theorem rawRowCheck16580 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form13 = rawRow16580 := by decide +kernel

def row16580 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16580 : row16580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16580 := by decide +kernel

theorem rowEval16580 (x : Key → ℝ) : Integer.Sparse.eval row16580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16580, Integer.Sparse.eval_collectBalanced, rawRowCheck16580]

def rawRow16581 : Integer.Sparse Key := [(key2948, 2), (key2950, 2), (key2960, 2), (key2936, -1), (key2938, -1), (key2972, -1), (key2997, -1), (key2983, -1), (key3000, -1), (key2735, 2), (key2737, 2), (key2747, 2), (key2646, -1), (key2648, -1), (key2893, -1), (key2997, -1), (key2904, -1), (key3000, -1), (key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2628, 2), (key2648, 2), (key2782, 2), (key2938, 2), (key2904, 2), (key2983, 2)]

theorem rawRowCheck16581 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form13 = rawRow16581 := by decide +kernel

def row16581 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

theorem rowCheck16581 : row16581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16581 := by decide +kernel

theorem rowEval16581 (x : Key → ℝ) : Integer.Sparse.eval row16581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16581, Integer.Sparse.eval_collectBalanced, rawRowCheck16581]

def rawRow16582 : Integer.Sparse Key := [(key2950, 2), (key2948, 2), (key2960, 2), (key2938, -1), (key2936, -1), (key2997, -1), (key2972, -1), (key3000, -1), (key2983, -1), (key2737, 2), (key2735, 2), (key2747, 2), (key2648, -1), (key2646, -1), (key2997, -1), (key2893, -1), (key3000, -1), (key2904, -1), (key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2648, 2), (key2628, 2), (key2938, 2), (key2782, 2), (key2983, 2), (key2904, 2)]

theorem rawRowCheck16582 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form13 = rawRow16582 := by decide +kernel

def row16582 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

theorem rowCheck16582 : row16582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16582 := by decide +kernel

theorem rowEval16582 (x : Key → ℝ) : Integer.Sparse.eval row16582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16582, Integer.Sparse.eval_collectBalanced, rawRowCheck16582]

def rawRow16583 : Integer.Sparse Key := [(key2948, 2), (key2960, 2), (key2950, 2), (key2972, -1), (key2983, -1), (key2936, -1), (key3000, -1), (key2938, -1), (key2997, -1), (key2735, 2), (key2747, 2), (key2737, 2), (key2893, -1), (key2904, -1), (key2646, -1), (key3000, -1), (key2648, -1), (key2997, -1), (key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2782, 2), (key2904, 2), (key2628, 2), (key2983, 2), (key2648, 2), (key2938, 2)]

theorem rawRowCheck16583 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form13 = rawRow16583 := by decide +kernel

def row16583 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

theorem rowCheck16583 : row16583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16583 := by decide +kernel

theorem rowEval16583 (x : Key → ℝ) : Integer.Sparse.eval row16583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16583, Integer.Sparse.eval_collectBalanced, rawRowCheck16583]

def rawRow16584 : Integer.Sparse Key := [(key2960, 2), (key2948, 2), (key2950, 2), (key2983, -1), (key2972, -1), (key3000, -1), (key2936, -1), (key2997, -1), (key2938, -1), (key2747, 2), (key2735, 2), (key2737, 2), (key2904, -1), (key2893, -1), (key3000, -1), (key2646, -1), (key2997, -1), (key2648, -1), (key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key2904, 2), (key2782, 2), (key2983, 2), (key2628, 2), (key2938, 2), (key2648, 2)]

theorem rawRowCheck16584 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form13 = rawRow16584 := by decide +kernel

def row16584 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

theorem rowCheck16584 : row16584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16584 := by decide +kernel

theorem rowEval16584 (x : Key → ℝ) : Integer.Sparse.eval row16584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16584, Integer.Sparse.eval_collectBalanced, rawRowCheck16584]

def rawRow16585 : Integer.Sparse Key := [(key2950, 2), (key2960, 2), (key2948, 2), (key2997, -1), (key3000, -1), (key2938, -1), (key2983, -1), (key2936, -1), (key2972, -1), (key2737, 2), (key2747, 2), (key2735, 2), (key2997, -1), (key3000, -1), (key2648, -1), (key2904, -1), (key2646, -1), (key2893, -1), (key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2938, 2), (key2983, 2), (key2648, 2), (key2904, 2), (key2628, 2), (key2782, 2)]

theorem rawRowCheck16585 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form13 = rawRow16585 := by decide +kernel

def row16585 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

theorem rowCheck16585 : row16585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16585 := by decide +kernel

theorem rowEval16585 (x : Key → ℝ) : Integer.Sparse.eval row16585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16585, Integer.Sparse.eval_collectBalanced, rawRowCheck16585]

def rawRow16586 : Integer.Sparse Key := [(key2960, 2), (key2950, 2), (key2948, 2), (key3000, -1), (key2997, -1), (key2983, -1), (key2938, -1), (key2972, -1), (key2936, -1), (key2747, 2), (key2737, 2), (key2735, 2), (key3000, -1), (key2997, -1), (key2904, -1), (key2648, -1), (key2893, -1), (key2646, -1), (key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2983, 2), (key2938, 2), (key2904, 2), (key2648, 2), (key2782, 2), (key2628, 2)]

theorem rawRowCheck16586 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form13 = rawRow16586 := by decide +kernel

def row16586 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

theorem rowCheck16586 : row16586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16586 := by decide +kernel

theorem rowEval16586 (x : Key → ℝ) : Integer.Sparse.eval row16586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16586, Integer.Sparse.eval_collectBalanced, rawRowCheck16586]

def rawRow16587 : Integer.Sparse Key := [(key2972, 2), (key2976, 2), (key2983, 2), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2893, 2), (key2897, 2), (key2904, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2)]

theorem rawRowCheck16587 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form13 = rawRow16587 := by decide +kernel

def row16587 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16587 : row16587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16587 := by decide +kernel

theorem rowEval16587 (x : Key → ℝ) : Integer.Sparse.eval row16587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16587, Integer.Sparse.eval_collectBalanced, rawRowCheck16587]

def rawRow16588 : Integer.Sparse Key := [(key2976, 2), (key2972, 2), (key2983, 2), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2897, 2), (key2893, 2), (key2904, 2), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2)]

theorem rawRowCheck16588 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form13 = rawRow16588 := by decide +kernel

def row16588 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16588 : row16588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16588 := by decide +kernel

theorem rowEval16588 (x : Key → ℝ) : Integer.Sparse.eval row16588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16588, Integer.Sparse.eval_collectBalanced, rawRowCheck16588]

def rawRow16589 : Integer.Sparse Key := [(key2972, 2), (key2983, 2), (key2976, 2), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2893, 2), (key2904, 2), (key2897, 2), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2)]

theorem rawRowCheck16589 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form13 = rawRow16589 := by decide +kernel

def row16589 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16589 : row16589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16589 := by decide +kernel

theorem rowEval16589 (x : Key → ℝ) : Integer.Sparse.eval row16589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16589, Integer.Sparse.eval_collectBalanced, rawRowCheck16589]

def rawRow16590 : Integer.Sparse Key := [(key2983, 2), (key2972, 2), (key2976, 2), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2904, 2), (key2893, 2), (key2897, 2), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2)]

theorem rawRowCheck16590 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form13 = rawRow16590 := by decide +kernel

def row16590 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16590 : row16590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16590 := by decide +kernel

theorem rowEval16590 (x : Key → ℝ) : Integer.Sparse.eval row16590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16590, Integer.Sparse.eval_collectBalanced, rawRowCheck16590]

def rawRow16591 : Integer.Sparse Key := [(key2976, 2), (key2983, 2), (key2972, 2), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2897, 2), (key2904, 2), (key2893, 2), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2)]

theorem rawRowCheck16591 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form13 = rawRow16591 := by decide +kernel

def row16591 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16591 : row16591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16591 := by decide +kernel

theorem rowEval16591 (x : Key → ℝ) : Integer.Sparse.eval row16591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16591, Integer.Sparse.eval_collectBalanced, rawRowCheck16591]

def rawRow16592 : Integer.Sparse Key := [(key2983, 2), (key2976, 2), (key2972, 2), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key2904, 2), (key2897, 2), (key2893, 2), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2)]

theorem rawRowCheck16592 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form13 = rawRow16592 := by decide +kernel

def row16592 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

theorem rowCheck16592 : row16592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16592 := by decide +kernel

theorem rowEval16592 (x : Key → ℝ) : Integer.Sparse.eval row16592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16592, Integer.Sparse.eval_collectBalanced, rawRowCheck16592]

def rawRow16593 : Integer.Sparse Key := [(key2997, 2), (key2998, 2), (key3000, 2), (key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2997, 2), (key2998, 2), (key3000, 2), (key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2618, 2), (key2641, 2), (key2673, 2), (key2795, 2), (key2728, 2), (key2831, 2)]

theorem rawRowCheck16593 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form13 = rawRow16593 := by decide +kernel

def row16593 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

theorem rowCheck16593 : row16593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16593 := by decide +kernel

theorem rowEval16593 (x : Key → ℝ) : Integer.Sparse.eval row16593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16593, Integer.Sparse.eval_collectBalanced, rawRowCheck16593]

def rawRow16594 : Integer.Sparse Key := [(key2998, 2), (key2997, 2), (key3000, 2), (key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2998, 2), (key2997, 2), (key3000, 2), (key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2641, 2), (key2618, 2), (key2795, 2), (key2673, 2), (key2831, 2), (key2728, 2)]

theorem rawRowCheck16594 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form13 = rawRow16594 := by decide +kernel

def row16594 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

theorem rowCheck16594 : row16594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16594 := by decide +kernel

theorem rowEval16594 (x : Key → ℝ) : Integer.Sparse.eval row16594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16594, Integer.Sparse.eval_collectBalanced, rawRowCheck16594]

def rawRow16595 : Integer.Sparse Key := [(key2997, 2), (key3000, 2), (key2998, 2), (key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2997, 2), (key3000, 2), (key2998, 2), (key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2673, 2), (key2728, 2), (key2618, 2), (key2831, 2), (key2641, 2), (key2795, 2)]

theorem rawRowCheck16595 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form13 = rawRow16595 := by decide +kernel

def row16595 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

theorem rowCheck16595 : row16595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16595 := by decide +kernel

theorem rowEval16595 (x : Key → ℝ) : Integer.Sparse.eval row16595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16595, Integer.Sparse.eval_collectBalanced, rawRowCheck16595]

def rawRow16596 : Integer.Sparse Key := [(key3000, 2), (key2997, 2), (key2998, 2), (key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key3000, 2), (key2997, 2), (key2998, 2), (key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2728, 2), (key2673, 2), (key2831, 2), (key2618, 2), (key2795, 2), (key2641, 2)]

theorem rawRowCheck16596 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form13 = rawRow16596 := by decide +kernel

def row16596 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

theorem rowCheck16596 : row16596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16596 := by decide +kernel

theorem rowEval16596 (x : Key → ℝ) : Integer.Sparse.eval row16596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16596, Integer.Sparse.eval_collectBalanced, rawRowCheck16596]

def rawRow16597 : Integer.Sparse Key := [(key2998, 2), (key3000, 2), (key2997, 2), (key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2998, 2), (key3000, 2), (key2997, 2), (key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2795, 2), (key2831, 2), (key2641, 2), (key2728, 2), (key2618, 2), (key2673, 2)]

theorem rawRowCheck16597 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form13 = rawRow16597 := by decide +kernel

def row16597 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

theorem rowCheck16597 : row16597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16597 := by decide +kernel

theorem rowEval16597 (x : Key → ℝ) : Integer.Sparse.eval row16597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16597, Integer.Sparse.eval_collectBalanced, rawRowCheck16597]

def rawRow16598 : Integer.Sparse Key := [(key3000, 2), (key2998, 2), (key2997, 2), (key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key3000, 2), (key2998, 2), (key2997, 2), (key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2831, 2), (key2795, 2), (key2728, 2), (key2641, 2), (key2673, 2), (key2618, 2)]

theorem rawRowCheck16598 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form13 = rawRow16598 := by decide +kernel

def row16598 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

theorem rowCheck16598 : row16598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16598 := by decide +kernel

theorem rowEval16598 (x : Key → ℝ) : Integer.Sparse.eval row16598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16598, Integer.Sparse.eval_collectBalanced, rawRowCheck16598]

def rawRow16599 : Integer.Sparse Key := [(key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2673, 2), (key2737, 2), (key2737, 2), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2621, -2), (key2835, -2), (key2835, -2), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key3023, -1), (key3023, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2753, 2), (key2920, 2), (key2920, 2), (key2658, -2), (key2923, -2), (key2923, -2)]

theorem rawRowCheck16599 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form14 = rawRow16599 := by decide +kernel

def row16599 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2632, 2), (key2658, -2), (key2667, -2), (key2673, 2), (key2706, -2), (key2735, -2), (key2737, 4), (key2747, -2), (key2753, 2), (key2829, 2), (key2835, -4), (key2860, -2), (key2870, 2), (key2920, 4), (key2923, -4), (key3017, 2), (key3023, -2), (key3026, 2)]

theorem rowCheck16599 : row16599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16599 := by decide +kernel

theorem rowEval16599 (x : Key → ℝ) : Integer.Sparse.eval row16599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16599, Integer.Sparse.eval_collectBalanced, rawRowCheck16599]

def rawRow16600 : Integer.Sparse Key := [(key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2737, 2), (key2673, 2), (key2737, 2), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2835, -2), (key2621, -2), (key2835, -2), (key2860, -1), (key3023, -1), (key2706, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2920, 2), (key2753, 2), (key2920, 2), (key2923, -2), (key2658, -2), (key2923, -2)]

theorem rawRowCheck16600 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form14 = rawRow16600 := by decide +kernel

def row16600 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2632, 2), (key2658, -2), (key2667, -2), (key2673, 2), (key2706, -2), (key2735, -2), (key2737, 4), (key2747, -2), (key2753, 2), (key2829, 1), (key2835, -4), (key2860, -2), (key2870, 2), (key2920, 4), (key2923, -4), (key2948, 1), (key2960, 2), (key3023, -2), (key3026, 2)]

theorem rowCheck16600 : row16600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16600 := by decide +kernel

theorem rowEval16600 (x : Key → ℝ) : Integer.Sparse.eval row16600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16600, Integer.Sparse.eval_collectBalanced, rawRowCheck16600]

def rawRow16601 : Integer.Sparse Key := [(key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2737, 2), (key2737, 2), (key2673, 2), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key2835, -2), (key2835, -2), (key2621, -2), (key3023, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2920, 2), (key2920, 2), (key2753, 2), (key2923, -2), (key2923, -2), (key2658, -2)]

theorem rawRowCheck16601 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form14 = rawRow16601 := by decide +kernel

def row16601 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2632, 2), (key2658, -2), (key2667, -2), (key2673, 2), (key2706, -2), (key2735, -2), (key2737, 4), (key2747, -2), (key2753, 2), (key2829, 1), (key2835, -4), (key2860, -2), (key2870, 2), (key2920, 4), (key2923, -4), (key2948, 1), (key2960, 2), (key3023, -2), (key3026, 2)]

theorem rowCheck16601 : row16601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16601 := by decide +kernel

theorem rowEval16601 (x : Key → ℝ) : Integer.Sparse.eval row16601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16601, Integer.Sparse.eval_collectBalanced, rawRowCheck16601]

def rawRow16602 : Integer.Sparse Key := [(key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2667, 2), (key2702, 2), (key2735, 2), (key2612, 1), (key2618, 1), (key2805, 1), (key2950, 1), (key2831, 1), (key2960, 1), (key2616, -2), (key2809, -2), (key2829, -2), (key2726, -1), (key2732, -1), (key2870, -1), (key2885, -1), (key3026, -1), (key3030, -1), (key2640, 1), (key2644, 1), (key2860, 1), (key2885, 1), (key3023, 1), (key3030, 1), (key2758, 2), (key2923, 2), (key2927, 2), (key2660, -2), (key2920, -2), (key2927, -2)]

theorem rawRowCheck16602 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form14 = rawRow16602 := by decide +kernel

def row16602 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck16602 : row16602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16602 := by decide +kernel

theorem rowEval16602 (x : Key → ℝ) : Integer.Sparse.eval row16602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16602, Integer.Sparse.eval_collectBalanced, rawRowCheck16602]

def rawRow16603 : Integer.Sparse Key := [(key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2667, 2), (key2735, 2), (key2702, 2), (key2618, 1), (key2612, 1), (key2950, 1), (key2805, 1), (key2960, 1), (key2831, 1), (key2616, -2), (key2829, -2), (key2809, -2), (key2732, -1), (key2726, -1), (key2885, -1), (key2870, -1), (key3030, -1), (key3026, -1), (key2644, 1), (key2640, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key3023, 1), (key2758, 2), (key2927, 2), (key2923, 2), (key2660, -2), (key2927, -2), (key2920, -2)]

theorem rawRowCheck16603 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form14 = rawRow16603 := by decide +kernel

def row16603 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck16603 : row16603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16603 := by decide +kernel

theorem rowEval16603 (x : Key → ℝ) : Integer.Sparse.eval row16603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16603, Integer.Sparse.eval_collectBalanced, rawRowCheck16603]

def rawRow16604 : Integer.Sparse Key := [(key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2702, 2), (key2667, 2), (key2735, 2), (key2805, 1), (key2831, 1), (key2612, 1), (key2960, 1), (key2618, 1), (key2950, 1), (key2809, -2), (key2616, -2), (key2829, -2), (key2870, -1), (key3026, -1), (key2726, -1), (key3030, -1), (key2732, -1), (key2885, -1), (key2860, 1), (key3023, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2923, 2), (key2758, 2), (key2927, 2), (key2920, -2), (key2660, -2), (key2927, -2)]

theorem rawRowCheck16604 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form14 = rawRow16604 := by decide +kernel

def row16604 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck16604 : row16604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16604 := by decide +kernel

theorem rowEval16604 (x : Key → ℝ) : Integer.Sparse.eval row16604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16604, Integer.Sparse.eval_collectBalanced, rawRowCheck16604]

def rawRow16605 : Integer.Sparse Key := [(key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2702, 2), (key2735, 2), (key2667, 2), (key2831, 1), (key2805, 1), (key2960, 1), (key2612, 1), (key2950, 1), (key2618, 1), (key2809, -2), (key2829, -2), (key2616, -2), (key3026, -1), (key2870, -1), (key3030, -1), (key2726, -1), (key2885, -1), (key2732, -1), (key3023, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key2885, 1), (key2644, 1), (key2923, 2), (key2927, 2), (key2758, 2), (key2920, -2), (key2927, -2), (key2660, -2)]

theorem rawRowCheck16605 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form14 = rawRow16605 := by decide +kernel

def row16605 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck16605 : row16605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16605 := by decide +kernel

theorem rowEval16605 (x : Key → ℝ) : Integer.Sparse.eval row16605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16605, Integer.Sparse.eval_collectBalanced, rawRowCheck16605]

def rawRow16606 : Integer.Sparse Key := [(key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2735, 2), (key2667, 2), (key2702, 2), (key2950, 1), (key2960, 1), (key2618, 1), (key2831, 1), (key2612, 1), (key2805, 1), (key2829, -2), (key2616, -2), (key2809, -2), (key2885, -1), (key3030, -1), (key2732, -1), (key3026, -1), (key2726, -1), (key2870, -1), (key2885, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2640, 1), (key2860, 1), (key2927, 2), (key2758, 2), (key2923, 2), (key2927, -2), (key2660, -2), (key2920, -2)]

theorem rawRowCheck16606 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form14 = rawRow16606 := by decide +kernel

def row16606 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck16606 : row16606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16606 := by decide +kernel

theorem rowEval16606 (x : Key → ℝ) : Integer.Sparse.eval row16606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16606, Integer.Sparse.eval_collectBalanced, rawRowCheck16606]

def rawRow16607 : Integer.Sparse Key := [(key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2735, 2), (key2702, 2), (key2667, 2), (key2960, 1), (key2950, 1), (key2831, 1), (key2618, 1), (key2805, 1), (key2612, 1), (key2829, -2), (key2809, -2), (key2616, -2), (key3030, -1), (key2885, -1), (key3026, -1), (key2732, -1), (key2870, -1), (key2726, -1), (key3030, 1), (key2885, 1), (key3023, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key2927, 2), (key2923, 2), (key2758, 2), (key2927, -2), (key2920, -2), (key2660, -2)]

theorem rawRowCheck16607 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form14 = rawRow16607 := by decide +kernel

def row16607 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck16607 : row16607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16607 := by decide +kernel

theorem rowEval16607 (x : Key → ℝ) : Integer.Sparse.eval row16607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16607, Integer.Sparse.eval_collectBalanced, rawRowCheck16607]

def rawRow16608 : Integer.Sparse Key := [(key2782, -1), (key2782, -1), (key2893, -1), (key2893, -1), (key2904, -1), (key2904, -1), (key2795, 2), (key2897, 2), (key2897, 2), (key2628, 1), (key2628, 1), (key2972, 1), (key2972, 1), (key2983, 1), (key2983, 1), (key2641, -2), (key2976, -2), (key2976, -2), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2676, 2), (key2798, 2), (key2798, 2), (key2621, -2), (key2835, -2), (key2835, -2)]

theorem rawRowCheck16608 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form14 = rawRow16608 := by decide +kernel

def row16608 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, 2), (key2641, -2), (key2667, -2), (key2676, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2795, 2), (key2798, 4), (key2829, 2), (key2835, -4), (key2893, -2), (key2897, 4), (key2904, -2), (key2972, 2), (key2976, -4), (key2983, 2), (key3017, 2)]

theorem rowCheck16608 : row16608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16608 := by decide +kernel

theorem rowEval16608 (x : Key → ℝ) : Integer.Sparse.eval row16608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16608, Integer.Sparse.eval_collectBalanced, rawRowCheck16608]

def rawRow16609 : Integer.Sparse Key := [(key2893, -1), (key2904, -1), (key2782, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2897, 2), (key2795, 2), (key2897, 2), (key2972, 1), (key2983, 1), (key2628, 1), (key2983, 1), (key2628, 1), (key2972, 1), (key2976, -2), (key2641, -2), (key2976, -2), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2798, 2), (key2676, 2), (key2798, 2), (key2835, -2), (key2621, -2), (key2835, -2)]

theorem rawRowCheck16609 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form14 = rawRow16609 := by decide +kernel

def row16609 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, 2), (key2641, -2), (key2667, -2), (key2676, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2795, 2), (key2798, 4), (key2829, 1), (key2835, -4), (key2893, -2), (key2897, 4), (key2904, -2), (key2948, 1), (key2960, 2), (key2972, 2), (key2976, -4), (key2983, 2)]

theorem rowCheck16609 : row16609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16609 := by decide +kernel

theorem rowEval16609 (x : Key → ℝ) : Integer.Sparse.eval row16609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16609, Integer.Sparse.eval_collectBalanced, rawRowCheck16609]

def rawRow16610 : Integer.Sparse Key := [(key2904, -1), (key2893, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2782, -1), (key2897, 2), (key2897, 2), (key2795, 2), (key2983, 1), (key2972, 1), (key2983, 1), (key2628, 1), (key2972, 1), (key2628, 1), (key2976, -2), (key2976, -2), (key2641, -2), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key2798, 2), (key2798, 2), (key2676, 2), (key2835, -2), (key2835, -2), (key2621, -2)]

theorem rawRowCheck16610 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form14 = rawRow16610 := by decide +kernel

def row16610 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, 2), (key2641, -2), (key2667, -2), (key2676, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2795, 2), (key2798, 4), (key2829, 1), (key2835, -4), (key2893, -2), (key2897, 4), (key2904, -2), (key2948, 1), (key2960, 2), (key2972, 2), (key2976, -4), (key2983, 2)]

theorem rowCheck16610 : row16610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16610 := by decide +kernel

theorem rowEval16610 (x : Key → ℝ) : Integer.Sparse.eval row16610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16610, Integer.Sparse.eval_collectBalanced, rawRowCheck16610]

def rawRow16611 : Integer.Sparse Key := [(key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2782, 2), (key2805, 2), (key2893, 2), (key2628, 1), (key2641, 1), (key2702, 1), (key2976, 1), (key2728, 1), (key2983, 1), (key2628, -2), (key2702, -2), (key2972, -2), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2732, 2), (key2835, 2), (key2885, 2), (key2644, -2), (key2798, -2), (key2885, -2)]

theorem rawRowCheck16611 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form14 = rawRow16611 := by decide +kernel

def row16611 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

theorem rowCheck16611 : row16611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16611 := by decide +kernel

theorem rowEval16611 (x : Key → ℝ) : Integer.Sparse.eval row16611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16611, Integer.Sparse.eval_collectBalanced, rawRowCheck16611]

def rawRow16612 : Integer.Sparse Key := [(key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2782, 2), (key2893, 2), (key2805, 2), (key2641, 1), (key2628, 1), (key2976, 1), (key2702, 1), (key2983, 1), (key2728, 1), (key2628, -2), (key2972, -2), (key2702, -2), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2732, 2), (key2885, 2), (key2835, 2), (key2644, -2), (key2885, -2), (key2798, -2)]

theorem rawRowCheck16612 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form14 = rawRow16612 := by decide +kernel

def row16612 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

theorem rowCheck16612 : row16612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16612 := by decide +kernel

theorem rowEval16612 (x : Key → ℝ) : Integer.Sparse.eval row16612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16612, Integer.Sparse.eval_collectBalanced, rawRowCheck16612]

def rawRow16613 : Integer.Sparse Key := [(key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2805, 2), (key2782, 2), (key2893, 2), (key2702, 1), (key2728, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2702, -2), (key2628, -2), (key2972, -2), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2835, 2), (key2732, 2), (key2885, 2), (key2798, -2), (key2644, -2), (key2885, -2)]

theorem rawRowCheck16613 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form14 = rawRow16613 := by decide +kernel

def row16613 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

theorem rowCheck16613 : row16613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16613 := by decide +kernel

theorem rowEval16613 (x : Key → ℝ) : Integer.Sparse.eval row16613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16613, Integer.Sparse.eval_collectBalanced, rawRowCheck16613]

def rawRow16614 : Integer.Sparse Key := [(key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2805, 2), (key2893, 2), (key2782, 2), (key2728, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2976, 1), (key2641, 1), (key2702, -2), (key2972, -2), (key2628, -2), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2835, 2), (key2885, 2), (key2732, 2), (key2798, -2), (key2885, -2), (key2644, -2)]

theorem rawRowCheck16614 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form14 = rawRow16614 := by decide +kernel

def row16614 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

theorem rowCheck16614 : row16614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16614 := by decide +kernel

theorem rowEval16614 (x : Key → ℝ) : Integer.Sparse.eval row16614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16614, Integer.Sparse.eval_collectBalanced, rawRowCheck16614]

def rawRow16615 : Integer.Sparse Key := [(key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2893, 2), (key2782, 2), (key2805, 2), (key2976, 1), (key2983, 1), (key2641, 1), (key2728, 1), (key2628, 1), (key2702, 1), (key2972, -2), (key2628, -2), (key2702, -2), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2885, 2), (key2732, 2), (key2835, 2), (key2885, -2), (key2644, -2), (key2798, -2)]

theorem rawRowCheck16615 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form14 = rawRow16615 := by decide +kernel

def row16615 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

theorem rowCheck16615 : row16615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16615 := by decide +kernel

theorem rowEval16615 (x : Key → ℝ) : Integer.Sparse.eval row16615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16615, Integer.Sparse.eval_collectBalanced, rawRowCheck16615]

def rawRow16616 : Integer.Sparse Key := [(key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2893, 2), (key2805, 2), (key2782, 2), (key2983, 1), (key2976, 1), (key2728, 1), (key2641, 1), (key2702, 1), (key2628, 1), (key2972, -2), (key2702, -2), (key2628, -2), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2885, 2), (key2835, 2), (key2732, 2), (key2885, -2), (key2798, -2), (key2644, -2)]

theorem rawRowCheck16616 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form14 = rawRow16616 := by decide +kernel

def row16616 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

theorem rowCheck16616 : row16616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16616 := by decide +kernel

theorem rowEval16616 (x : Key → ℝ) : Integer.Sparse.eval row16616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16616, Integer.Sparse.eval_collectBalanced, rawRowCheck16616]

def rawRow16617 : Integer.Sparse Key := [(key2936, -1), (key2938, -1), (key2972, -1), (key2997, -1), (key2983, -1), (key3000, -1), (key2943, 2), (key2976, 2), (key2998, 2), (key2646, 1), (key2648, 1), (key2893, 1), (key2997, 1), (key2904, 1), (key3000, 1), (key2653, -2), (key2897, -2), (key2998, -2), (key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2612, 1), (key2618, 1), (key2805, 1), (key2950, 1), (key2831, 1), (key2960, 1), (key2671, 2), (key2786, 2), (key2794, 2), (key2616, -2), (key2809, -2), (key2829, -2)]

theorem rawRowCheck16617 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form14 = rawRow16617 := by decide +kernel

def row16617 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

theorem rowCheck16617 : row16617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16617 := by decide +kernel

theorem rowEval16617 (x : Key → ℝ) : Integer.Sparse.eval row16617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16617, Integer.Sparse.eval_collectBalanced, rawRowCheck16617]

def rawRow16618 : Integer.Sparse Key := [(key2938, -1), (key2936, -1), (key2997, -1), (key2972, -1), (key3000, -1), (key2983, -1), (key2943, 2), (key2998, 2), (key2976, 2), (key2648, 1), (key2646, 1), (key2997, 1), (key2893, 1), (key3000, 1), (key2904, 1), (key2653, -2), (key2998, -2), (key2897, -2), (key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2618, 1), (key2612, 1), (key2950, 1), (key2805, 1), (key2960, 1), (key2831, 1), (key2671, 2), (key2794, 2), (key2786, 2), (key2616, -2), (key2829, -2), (key2809, -2)]

theorem rawRowCheck16618 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form14 = rawRow16618 := by decide +kernel

def row16618 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

theorem rowCheck16618 : row16618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16618 := by decide +kernel

theorem rowEval16618 (x : Key → ℝ) : Integer.Sparse.eval row16618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16618, Integer.Sparse.eval_collectBalanced, rawRowCheck16618]

def rawRow16619 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2936, -1), (key3000, -1), (key2938, -1), (key2997, -1), (key2976, 2), (key2943, 2), (key2998, 2), (key2893, 1), (key2904, 1), (key2646, 1), (key3000, 1), (key2648, 1), (key2997, 1), (key2897, -2), (key2653, -2), (key2998, -2), (key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2805, 1), (key2831, 1), (key2612, 1), (key2960, 1), (key2618, 1), (key2950, 1), (key2786, 2), (key2671, 2), (key2794, 2), (key2809, -2), (key2616, -2), (key2829, -2)]

theorem rawRowCheck16619 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form14 = rawRow16619 := by decide +kernel

def row16619 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

theorem rowCheck16619 : row16619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16619 := by decide +kernel

theorem rowEval16619 (x : Key → ℝ) : Integer.Sparse.eval row16619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16619, Integer.Sparse.eval_collectBalanced, rawRowCheck16619]

def rawRow16620 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key3000, -1), (key2936, -1), (key2997, -1), (key2938, -1), (key2976, 2), (key2998, 2), (key2943, 2), (key2904, 1), (key2893, 1), (key3000, 1), (key2646, 1), (key2997, 1), (key2648, 1), (key2897, -2), (key2998, -2), (key2653, -2), (key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2831, 1), (key2805, 1), (key2960, 1), (key2612, 1), (key2950, 1), (key2618, 1), (key2786, 2), (key2794, 2), (key2671, 2), (key2809, -2), (key2829, -2), (key2616, -2)]

theorem rawRowCheck16620 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form14 = rawRow16620 := by decide +kernel

def row16620 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

theorem rowCheck16620 : row16620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16620 := by decide +kernel

theorem rowEval16620 (x : Key → ℝ) : Integer.Sparse.eval row16620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16620, Integer.Sparse.eval_collectBalanced, rawRowCheck16620]

def rawRow16621 : Integer.Sparse Key := [(key2997, -1), (key3000, -1), (key2938, -1), (key2983, -1), (key2936, -1), (key2972, -1), (key2998, 2), (key2943, 2), (key2976, 2), (key2997, 1), (key3000, 1), (key2648, 1), (key2904, 1), (key2646, 1), (key2893, 1), (key2998, -2), (key2653, -2), (key2897, -2), (key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2950, 1), (key2960, 1), (key2618, 1), (key2831, 1), (key2612, 1), (key2805, 1), (key2794, 2), (key2671, 2), (key2786, 2), (key2829, -2), (key2616, -2), (key2809, -2)]

theorem rawRowCheck16621 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form14 = rawRow16621 := by decide +kernel

def row16621 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

theorem rowCheck16621 : row16621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16621 := by decide +kernel

theorem rowEval16621 (x : Key → ℝ) : Integer.Sparse.eval row16621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16621, Integer.Sparse.eval_collectBalanced, rawRowCheck16621]

def rawRow16622 : Integer.Sparse Key := [(key3000, -1), (key2997, -1), (key2983, -1), (key2938, -1), (key2972, -1), (key2936, -1), (key2998, 2), (key2976, 2), (key2943, 2), (key3000, 1), (key2997, 1), (key2904, 1), (key2648, 1), (key2893, 1), (key2646, 1), (key2998, -2), (key2897, -2), (key2653, -2), (key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2960, 1), (key2950, 1), (key2831, 1), (key2618, 1), (key2805, 1), (key2612, 1), (key2794, 2), (key2786, 2), (key2671, 2), (key2829, -2), (key2809, -2), (key2616, -2)]

theorem rawRowCheck16622 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form14 = rawRow16622 := by decide +kernel

def row16622 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

theorem rowCheck16622 : row16622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16622 := by decide +kernel

theorem rowEval16622 (x : Key → ℝ) : Integer.Sparse.eval row16622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16622, Integer.Sparse.eval_collectBalanced, rawRowCheck16622]

def rawRow16623 : Integer.Sparse Key := [(key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2938, 2), (key2950, 2), (key2997, 2), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2648, -2), (key2737, -2), (key2997, -2), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2976, 1), (key2728, 1), (key2983, 1), (key2706, 2), (key2809, 2), (key2860, 2), (key2632, -2), (key2786, -2), (key2870, -2)]

theorem rawRowCheck16623 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form14 = rawRow16623 := by decide +kernel

def row16623 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

theorem rowCheck16623 : row16623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16623 := by decide +kernel

theorem rowEval16623 (x : Key → ℝ) : Integer.Sparse.eval row16623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16623, Integer.Sparse.eval_collectBalanced, rawRowCheck16623]

def rawRow16624 : Integer.Sparse Key := [(key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2938, 2), (key2997, 2), (key2950, 2), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2648, -2), (key2997, -2), (key2737, -2), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2641, 1), (key2628, 1), (key2976, 1), (key2702, 1), (key2983, 1), (key2728, 1), (key2706, 2), (key2860, 2), (key2809, 2), (key2632, -2), (key2870, -2), (key2786, -2)]

theorem rawRowCheck16624 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form14 = rawRow16624 := by decide +kernel

def row16624 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

theorem rowCheck16624 : row16624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16624 := by decide +kernel

theorem rowEval16624 (x : Key → ℝ) : Integer.Sparse.eval row16624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16624, Integer.Sparse.eval_collectBalanced, rawRowCheck16624]

def rawRow16625 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2950, 2), (key2938, 2), (key2997, 2), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2737, -2), (key2648, -2), (key2997, -2), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2702, 1), (key2728, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2809, 2), (key2706, 2), (key2860, 2), (key2786, -2), (key2632, -2), (key2870, -2)]

theorem rawRowCheck16625 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form14 = rawRow16625 := by decide +kernel

def row16625 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

theorem rowCheck16625 : row16625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16625 := by decide +kernel

theorem rowEval16625 (x : Key → ℝ) : Integer.Sparse.eval row16625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16625, Integer.Sparse.eval_collectBalanced, rawRowCheck16625]

def rawRow16626 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2950, 2), (key2997, 2), (key2938, 2), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2737, -2), (key2997, -2), (key2648, -2), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2728, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2976, 1), (key2641, 1), (key2809, 2), (key2860, 2), (key2706, 2), (key2786, -2), (key2870, -2), (key2632, -2)]

theorem rawRowCheck16626 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form14 = rawRow16626 := by decide +kernel

def row16626 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

theorem rowCheck16626 : row16626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16626 := by decide +kernel

theorem rowEval16626 (x : Key → ℝ) : Integer.Sparse.eval row16626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16626, Integer.Sparse.eval_collectBalanced, rawRowCheck16626]

def rawRow16627 : Integer.Sparse Key := [(key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2997, 2), (key2938, 2), (key2950, 2), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2997, -2), (key2648, -2), (key2737, -2), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, 1), (key2983, 1), (key2641, 1), (key2728, 1), (key2628, 1), (key2702, 1), (key2860, 2), (key2706, 2), (key2809, 2), (key2870, -2), (key2632, -2), (key2786, -2)]

theorem rawRowCheck16627 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form14 = rawRow16627 := by decide +kernel

def row16627 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

theorem rowCheck16627 : row16627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16627 := by decide +kernel

theorem rowEval16627 (x : Key → ℝ) : Integer.Sparse.eval row16627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16627, Integer.Sparse.eval_collectBalanced, rawRowCheck16627]

def rawRow16628 : Integer.Sparse Key := [(key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key2997, 2), (key2950, 2), (key2938, 2), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2997, -2), (key2737, -2), (key2648, -2), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, 1), (key2976, 1), (key2728, 1), (key2641, 1), (key2702, 1), (key2628, 1), (key2860, 2), (key2809, 2), (key2706, 2), (key2870, -2), (key2786, -2), (key2632, -2)]

theorem rawRowCheck16628 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form14 = rawRow16628 := by decide +kernel

def row16628 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

theorem rowCheck16628 : row16628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16628 := by decide +kernel

theorem rowEval16628 (x : Key → ℝ) : Integer.Sparse.eval row16628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16628, Integer.Sparse.eval_collectBalanced, rawRowCheck16628]

def rawRow16629 : Integer.Sparse Key := [(key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2936, 2), (key2948, 2), (key2972, 2), (key2648, 1), (key2653, 1), (key2737, 1), (key2897, 1), (key2747, 1), (key2904, 1), (key2646, -2), (key2735, -2), (key2893, -2), (key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2648, 1), (key2653, 1), (key2737, 1), (key2897, 1), (key2747, 1), (key2904, 1), (key2726, 2), (key2829, 2), (key2870, 2), (key2640, -2), (key2794, -2), (key2860, -2)]

theorem rawRowCheck16629 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form14 = rawRow16629 := by decide +kernel

def row16629 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

theorem rowCheck16629 : row16629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16629 := by decide +kernel

theorem rowEval16629 (x : Key → ℝ) : Integer.Sparse.eval row16629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16629, Integer.Sparse.eval_collectBalanced, rawRowCheck16629]

def rawRow16630 : Integer.Sparse Key := [(key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2936, 2), (key2972, 2), (key2948, 2), (key2653, 1), (key2648, 1), (key2897, 1), (key2737, 1), (key2904, 1), (key2747, 1), (key2646, -2), (key2893, -2), (key2735, -2), (key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2653, 1), (key2648, 1), (key2897, 1), (key2737, 1), (key2904, 1), (key2747, 1), (key2726, 2), (key2870, 2), (key2829, 2), (key2640, -2), (key2860, -2), (key2794, -2)]

theorem rawRowCheck16630 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form14 = rawRow16630 := by decide +kernel

def row16630 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

theorem rowCheck16630 : row16630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16630 := by decide +kernel

theorem rowEval16630 (x : Key → ℝ) : Integer.Sparse.eval row16630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16630, Integer.Sparse.eval_collectBalanced, rawRowCheck16630]

def rawRow16631 : Integer.Sparse Key := [(key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2948, 2), (key2936, 2), (key2972, 2), (key2737, 1), (key2747, 1), (key2648, 1), (key2904, 1), (key2653, 1), (key2897, 1), (key2735, -2), (key2646, -2), (key2893, -2), (key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2737, 1), (key2747, 1), (key2648, 1), (key2904, 1), (key2653, 1), (key2897, 1), (key2829, 2), (key2726, 2), (key2870, 2), (key2794, -2), (key2640, -2), (key2860, -2)]

theorem rawRowCheck16631 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form14 = rawRow16631 := by decide +kernel

def row16631 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

theorem rowCheck16631 : row16631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16631 := by decide +kernel

theorem rowEval16631 (x : Key → ℝ) : Integer.Sparse.eval row16631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16631, Integer.Sparse.eval_collectBalanced, rawRowCheck16631]

def rawRow16632 : Integer.Sparse Key := [(key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key2948, 2), (key2972, 2), (key2936, 2), (key2747, 1), (key2737, 1), (key2904, 1), (key2648, 1), (key2897, 1), (key2653, 1), (key2735, -2), (key2893, -2), (key2646, -2), (key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key2747, 1), (key2737, 1), (key2904, 1), (key2648, 1), (key2897, 1), (key2653, 1), (key2829, 2), (key2870, 2), (key2726, 2), (key2794, -2), (key2860, -2), (key2640, -2)]

theorem rawRowCheck16632 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form14 = rawRow16632 := by decide +kernel

def row16632 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

theorem rowCheck16632 : row16632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16632 := by decide +kernel

theorem rowEval16632 (x : Key → ℝ) : Integer.Sparse.eval row16632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16632, Integer.Sparse.eval_collectBalanced, rawRowCheck16632]

def rawRow16633 : Integer.Sparse Key := [(key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2972, 2), (key2936, 2), (key2948, 2), (key2897, 1), (key2904, 1), (key2653, 1), (key2747, 1), (key2648, 1), (key2737, 1), (key2893, -2), (key2646, -2), (key2735, -2), (key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2897, 1), (key2904, 1), (key2653, 1), (key2747, 1), (key2648, 1), (key2737, 1), (key2870, 2), (key2726, 2), (key2829, 2), (key2860, -2), (key2640, -2), (key2794, -2)]

theorem rawRowCheck16633 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form14 = rawRow16633 := by decide +kernel

def row16633 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

theorem rowCheck16633 : row16633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16633 := by decide +kernel

theorem rowEval16633 (x : Key → ℝ) : Integer.Sparse.eval row16633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16633, Integer.Sparse.eval_collectBalanced, rawRowCheck16633]

def rawRow16634 : Integer.Sparse Key := [(key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key2972, 2), (key2948, 2), (key2936, 2), (key2904, 1), (key2897, 1), (key2747, 1), (key2653, 1), (key2737, 1), (key2648, 1), (key2893, -2), (key2735, -2), (key2646, -2), (key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key2904, 1), (key2897, 1), (key2747, 1), (key2653, 1), (key2737, 1), (key2648, 1), (key2870, 2), (key2829, 2), (key2726, 2), (key2860, -2), (key2794, -2), (key2640, -2)]

theorem rawRowCheck16634 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form14 = rawRow16634 := by decide +kernel

def row16634 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

theorem rowCheck16634 : row16634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16634 := by decide +kernel

theorem rowEval16634 (x : Key → ℝ) : Integer.Sparse.eval row16634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16634, Integer.Sparse.eval_collectBalanced, rawRowCheck16634]

def rawRow16635 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2794, -1), (key2794, -1), (key2944, -1), (key2944, -1), (key2674, 2), (key2796, 2), (key2796, 2), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1), (key2619, -2), (key2832, -2), (key2832, -2), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key2977, -1), (key2977, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1), (key2738, 2), (key2898, 2), (key2898, 2), (key2649, -2), (key2905, -2), (key2905, -2)]

theorem rawRowCheck16635 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form15 = rawRow16635 := by decide +kernel

def row16635 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

theorem rowCheck16635 : row16635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16635 := by decide +kernel

theorem rowEval16635 (x : Key → ℝ) : Integer.Sparse.eval row16635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16635, Integer.Sparse.eval_collectBalanced, rawRowCheck16635]

def rawRow16636 : Integer.Sparse Key := [(key2794, -1), (key2944, -1), (key2671, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2796, 2), (key2674, 2), (key2796, 2), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2832, -2), (key2619, -2), (key2832, -2), (key2860, -1), (key2977, -1), (key2706, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2898, 2), (key2738, 2), (key2898, 2), (key2905, -2), (key2649, -2), (key2905, -2)]

theorem rawRowCheck16636 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form15 = rawRow16636 := by decide +kernel

def row16636 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

theorem rowCheck16636 : row16636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16636 := by decide +kernel

theorem rowEval16636 (x : Key → ℝ) : Integer.Sparse.eval row16636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16636, Integer.Sparse.eval_collectBalanced, rawRowCheck16636]

def rawRow16637 : Integer.Sparse Key := [(key2944, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2796, 2), (key2796, 2), (key2674, 2), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2832, -2), (key2832, -2), (key2619, -2), (key2977, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2898, 2), (key2898, 2), (key2738, 2), (key2905, -2), (key2905, -2), (key2649, -2)]

theorem rawRowCheck16637 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form15 = rawRow16637 := by decide +kernel

def row16637 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

theorem rowCheck16637 : row16637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16637 := by decide +kernel

theorem rowEval16637 (x : Key → ℝ) : Integer.Sparse.eval row16637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16637, Integer.Sparse.eval_collectBalanced, rawRowCheck16637]

def rawRow16638 : Integer.Sparse Key := [(key2671, -1), (key2674, -1), (key2786, -1), (key2796, -1), (key2939, -1), (key2944, -1), (key2671, 2), (key2786, 2), (key2794, 2), (key2616, 1), (key2619, 1), (key2809, 1), (key2832, 1), (key2951, 1), (key2961, 1), (key2616, -2), (key2809, -2), (key2829, -2), (key2726, -1), (key2729, -1), (key2870, -1), (key2883, -1), (key2984, -1), (key2992, -1), (key2640, 1), (key2642, 1), (key2860, 1), (key2883, 1), (key2977, 1), (key2992, 1), (key2748, 2), (key2905, 2), (key2913, 2), (key2654, -2), (key2898, -2), (key2913, -2)]

theorem rawRowCheck16638 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form15 = rawRow16638 := by decide +kernel

def row16638 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16638 : row16638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16638 := by decide +kernel

theorem rowEval16638 (x : Key → ℝ) : Integer.Sparse.eval row16638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16638, Integer.Sparse.eval_collectBalanced, rawRowCheck16638]

def rawRow16639 : Integer.Sparse Key := [(key2674, -1), (key2671, -1), (key2796, -1), (key2786, -1), (key2944, -1), (key2939, -1), (key2671, 2), (key2794, 2), (key2786, 2), (key2619, 1), (key2616, 1), (key2832, 1), (key2809, 1), (key2961, 1), (key2951, 1), (key2616, -2), (key2829, -2), (key2809, -2), (key2729, -1), (key2726, -1), (key2883, -1), (key2870, -1), (key2992, -1), (key2984, -1), (key2642, 1), (key2640, 1), (key2883, 1), (key2860, 1), (key2992, 1), (key2977, 1), (key2748, 2), (key2913, 2), (key2905, 2), (key2654, -2), (key2913, -2), (key2898, -2)]

theorem rawRowCheck16639 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form15 = rawRow16639 := by decide +kernel

def row16639 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16639 : row16639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16639 := by decide +kernel

theorem rowEval16639 (x : Key → ℝ) : Integer.Sparse.eval row16639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16639, Integer.Sparse.eval_collectBalanced, rawRowCheck16639]

end MUB6.Certificate.GramRows

end OAI

import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18688 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key86, 24), (key3, 24), (key147, 24)]

theorem rawRowCheck18688 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form1 = rawRow18688 := by decide +kernel

def row18688 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18688 : row18688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18688 := by decide +kernel

theorem rowEval18688 (x : Key → ℝ) : Integer.Sparse.eval row18688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18688, Integer.Sparse.eval_collectBalanced, rawRowCheck18688]

def rawRow18689 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key86, 24), (key147, 24), (key3, 24)]

theorem rawRowCheck18689 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form1 = rawRow18689 := by decide +kernel

def row18689 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18689 : row18689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18689 := by decide +kernel

theorem rowEval18689 (x : Key → ℝ) : Integer.Sparse.eval row18689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18689, Integer.Sparse.eval_collectBalanced, rawRowCheck18689]

def rawRow18690 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key147, 24), (key3, 24), (key86, 24)]

theorem rawRowCheck18690 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form1 = rawRow18690 := by decide +kernel

def row18690 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18690 : row18690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18690 := by decide +kernel

theorem rowEval18690 (x : Key → ℝ) : Integer.Sparse.eval row18690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18690, Integer.Sparse.eval_collectBalanced, rawRowCheck18690]

def rawRow18691 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key147, 24), (key86, 24), (key3, 24)]

theorem rawRowCheck18691 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form1 = rawRow18691 := by decide +kernel

def row18691 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18691 : row18691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18691 := by decide +kernel

theorem rowEval18691 (x : Key → ℝ) : Integer.Sparse.eval row18691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18691, Integer.Sparse.eval_collectBalanced, rawRowCheck18691]

def rawRow18692 : Integer.Sparse Key := [(key86, 24), (key147, 24), (key3, 24), (key86, 24), (key86, 24)]

theorem rawRowCheck18692 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18692 := by decide +kernel

def row18692 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18692 : row18692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18692 := by decide +kernel

theorem rowEval18692 (x : Key → ℝ) : Integer.Sparse.eval row18692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18692, Integer.Sparse.eval_collectBalanced, rawRowCheck18692]

def rawRow18693 : Integer.Sparse Key := [(key86, 24), (key147, 24), (key86, 24), (key3, 24), (key86, 24)]

theorem rawRowCheck18693 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18693 := by decide +kernel

def row18693 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18693 : row18693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18693 := by decide +kernel

theorem rowEval18693 (x : Key → ℝ) : Integer.Sparse.eval row18693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18693, Integer.Sparse.eval_collectBalanced, rawRowCheck18693]

def rawRow18694 : Integer.Sparse Key := [(key86, 24), (key147, 24), (key86, 24), (key86, 24), (key3, 24)]

theorem rawRowCheck18694 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18694 := by decide +kernel

def row18694 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18694 : row18694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18694 := by decide +kernel

theorem rowEval18694 (x : Key → ℝ) : Integer.Sparse.eval row18694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18694, Integer.Sparse.eval_collectBalanced, rawRowCheck18694]

def rawRow18695 : Integer.Sparse Key := [(key147, 24), (key3, 24), (key86, 24), (key86, 24), (key86, 24)]

theorem rawRowCheck18695 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18695 := by decide +kernel

def row18695 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18695 : row18695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18695 := by decide +kernel

theorem rowEval18695 (x : Key → ℝ) : Integer.Sparse.eval row18695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18695, Integer.Sparse.eval_collectBalanced, rawRowCheck18695]

def rawRow18696 : Integer.Sparse Key := [(key147, 24), (key86, 24), (key3, 24), (key86, 24), (key86, 24)]

theorem rawRowCheck18696 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18696 := by decide +kernel

def row18696 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18696 : row18696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18696 := by decide +kernel

theorem rowEval18696 (x : Key → ℝ) : Integer.Sparse.eval row18696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18696, Integer.Sparse.eval_collectBalanced, rawRowCheck18696]

def rawRow18697 : Integer.Sparse Key := [(key147, 24), (key86, 24), (key86, 24), (key3, 24), (key86, 24)]

theorem rawRowCheck18697 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18697 := by decide +kernel

def row18697 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18697 : row18697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18697 := by decide +kernel

theorem rowEval18697 (x : Key → ℝ) : Integer.Sparse.eval row18697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18697, Integer.Sparse.eval_collectBalanced, rawRowCheck18697]

def rawRow18698 : Integer.Sparse Key := [(key147, 24), (key86, 24), (key86, 24), (key86, 24), (key3, 24)]

theorem rawRowCheck18698 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18698 := by decide +kernel

def row18698 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

theorem rowCheck18698 : row18698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18698 := by decide +kernel

theorem rowEval18698 (x : Key → ℝ) : Integer.Sparse.eval row18698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18698, Integer.Sparse.eval_collectBalanced, rawRowCheck18698]

def rawRow18699 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1001, 2), (key993, 2), (key1001, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1150, 2), (key1114, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1150, 2), (key1232, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1235, 2), (key1242, 2)]

theorem rawRowCheck18699 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form2 = rawRow18699 := by decide +kernel

def row18699 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18699 : row18699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18699 := by decide +kernel

theorem rowEval18699 (x : Key → ℝ) : Integer.Sparse.eval row18699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18699, Integer.Sparse.eval_collectBalanced, rawRowCheck18699]

def rawRow18700 : Integer.Sparse Key := [(key1001, 2), (key993, 2), (key1001, 2), (key1001, 2), (key993, 2), (key1015, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1015, 2), (key1001, 2), (key1036, 2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1242, 2), (key1235, 2)]

theorem rawRowCheck18700 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form2 = rawRow18700 := by decide +kernel

def row18700 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18700 : row18700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18700 := by decide +kernel

theorem rowEval18700 (x : Key → ℝ) : Integer.Sparse.eval row18700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18700, Integer.Sparse.eval_collectBalanced, rawRowCheck18700]

def rawRow18701 : Integer.Sparse Key := [(key1001, 2), (key1001, 2), (key993, 2), (key1015, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key993, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1242, 2), (key1235, 2), (key1235, 2), (key1232, 2), (key1232, 2)]

theorem rawRowCheck18701 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form2 = rawRow18701 := by decide +kernel

def row18701 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18701 : row18701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18701 := by decide +kernel

theorem rowEval18701 (x : Key → ℝ) : Integer.Sparse.eval row18701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18701, Integer.Sparse.eval_collectBalanced, rawRowCheck18701]

def rawRow18702 : Integer.Sparse Key := [(key1015, 2), (key1015, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key993, 2), (key993, 2), (key993, 2), (key1071, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1028, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1242, 2), (key1242, 2), (key1235, 2), (key1235, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2)]

theorem rawRowCheck18702 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18702 := by decide +kernel

def row18702 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18702 : row18702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18702 := by decide +kernel

theorem rowEval18702 (x : Key → ℝ) : Integer.Sparse.eval row18702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18702, Integer.Sparse.eval_collectBalanced, rawRowCheck18702]

def rawRow18703 : Integer.Sparse Key := [(key1028, 2), (key1036, 2), (key1036, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1232, 2), (key1232, 2), (key1235, 2), (key993, 2), (key1001, 2), (key1001, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key993, 2), (key1001, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1071, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1150, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1235, 2), (key1242, 2), (key1001, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1114, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1150, 2)]

theorem rawRowCheck18703 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form2 = rawRow18703 := by decide +kernel

def row18703 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18703 : row18703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18703 := by decide +kernel

theorem rowEval18703 (x : Key → ℝ) : Integer.Sparse.eval row18703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18703, Integer.Sparse.eval_collectBalanced, rawRowCheck18703]

def rawRow18704 : Integer.Sparse Key := [(key1036, 2), (key1028, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1015, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1242, 2), (key1235, 2), (key1001, 2), (key1015, 2), (key1001, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1123, 2)]

theorem rawRowCheck18704 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form2 = rawRow18704 := by decide +kernel

def row18704 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18704 : row18704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18704 := by decide +kernel

theorem rowEval18704 (x : Key → ℝ) : Integer.Sparse.eval row18704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18704, Integer.Sparse.eval_collectBalanced, rawRowCheck18704]

def rawRow18705 : Integer.Sparse Key := [(key1036, 2), (key1036, 2), (key1028, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key993, 2), (key1150, 2), (key1150, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1232, 2), (key1015, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key993, 2), (key993, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1242, 2), (key1235, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2)]

theorem rawRowCheck18705 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form2 = rawRow18705 := by decide +kernel

def row18705 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18705 : row18705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18705 := by decide +kernel

theorem rowEval18705 (x : Key → ℝ) : Integer.Sparse.eval row18705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18705, Integer.Sparse.eval_collectBalanced, rawRowCheck18705]

def rawRow18706 : Integer.Sparse Key := [(key1106, 2), (key1114, 2), (key1232, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1123, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1114, 2), (key1232, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1150, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1114, 2), (key1150, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1123, 2), (key1232, 2), (key1235, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1150, 2), (key1232, 2), (key1242, 2), (key993, 2), (key1015, 2), (key1028, 2), (key1071, 2), (key1235, 2), (key1242, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1071, 2), (key1123, 2), (key1150, 2), (key1036, 2), (key1114, 2), (key1123, 2), (key1001, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1071, 2), (key1123, 2), (key1150, 2)]

theorem rawRowCheck18706 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form2 = rawRow18706 := by decide +kernel

def row18706 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18706 : row18706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18706 := by decide +kernel

theorem rowEval18706 (x : Key → ℝ) : Integer.Sparse.eval row18706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18706, Integer.Sparse.eval_collectBalanced, rawRowCheck18706]

def rawRow18707 : Integer.Sparse Key := [(key1114, 2), (key1106, 2), (key1232, 2), (key1036, 2), (key1028, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1001, 2), (key1150, 2), (key1114, 2), (key1036, 2), (key1028, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1015, 2), (key993, 2), (key1071, 2), (key1028, 2), (key1242, 2), (key1235, 2), (key1015, 2), (key1001, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1114, 2), (key1015, 2), (key1001, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1123, 2)]

theorem rawRowCheck18707 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form2 = rawRow18707 := by decide +kernel

def row18707 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18707 : row18707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18707 := by decide +kernel

theorem rowEval18707 (x : Key → ℝ) : Integer.Sparse.eval row18707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18707, Integer.Sparse.eval_collectBalanced, rawRowCheck18707]

def rawRow18708 : Integer.Sparse Key := [(key1106, 2), (key1232, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1036, 2), (key1123, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1106, 2), (key1232, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1106, 2), (key1232, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key1028, 2), (key1235, 2), (key993, 2), (key1242, 2), (key1015, 2), (key1071, 2), (key1036, 2), (key1123, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1114, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1036, 2), (key1123, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1071, 2)]

theorem rawRowCheck18708 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form2 = rawRow18708 := by decide +kernel

def row18708 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18708 : row18708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18708 := by decide +kernel

theorem rowEval18708 (x : Key → ℝ) : Integer.Sparse.eval row18708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18708, Integer.Sparse.eval_collectBalanced, rawRowCheck18708]

def rawRow18709 : Integer.Sparse Key := [(key1232, 2), (key1106, 2), (key1114, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1106, 2), (key1114, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1150, 2), (key1001, 2), (key1235, 2), (key1028, 2), (key1242, 2), (key993, 2), (key1071, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1071, 2), (key1015, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1071, 2), (key1015, 2)]

theorem rawRowCheck18709 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form2 = rawRow18709 := by decide +kernel

def row18709 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18709 : row18709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18709 := by decide +kernel

theorem rowEval18709 (x : Key → ℝ) : Integer.Sparse.eval row18709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18709, Integer.Sparse.eval_collectBalanced, rawRowCheck18709]

def rawRow18710 : Integer.Sparse Key := [(key1114, 2), (key1232, 2), (key1106, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1028, 2), (key1106, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key993, 2), (key1106, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1028, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key993, 2), (key1106, 2), (key1071, 2), (key1242, 2), (key1015, 2), (key1235, 2), (key993, 2), (key1028, 2), (key1071, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1001, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1071, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1001, 2), (key1036, 2)]

theorem rawRowCheck18710 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form2 = rawRow18710 := by decide +kernel

def row18710 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18710 : row18710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18710 := by decide +kernel

theorem rowEval18710 (x : Key → ℝ) : Integer.Sparse.eval row18710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18710, Integer.Sparse.eval_collectBalanced, rawRowCheck18710]

def rawRow18711 : Integer.Sparse Key := [(key1232, 2), (key1114, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1232, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1123, 2), (key1114, 2), (key1036, 2), (key1232, 2), (key1114, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1232, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1150, 2), (key1114, 2), (key1001, 2), (key1235, 2), (key1123, 2), (key1232, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1242, 2), (key1150, 2), (key1232, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1242, 2), (key1071, 2), (key1235, 2), (key1015, 2), (key1028, 2), (key993, 2), (key1150, 2), (key1071, 2), (key1123, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1123, 2), (key1114, 2), (key1036, 2), (key1150, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1071, 2), (key1123, 2), (key1015, 2), (key1036, 2), (key1001, 2)]

theorem rawRowCheck18711 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form2 = rawRow18711 := by decide +kernel

def row18711 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18711 : row18711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18711 := by decide +kernel

theorem rowEval18711 (x : Key → ℝ) : Integer.Sparse.eval row18711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18711, Integer.Sparse.eval_collectBalanced, rawRowCheck18711]

def rawRow18712 : Integer.Sparse Key := [(key1123, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key993, 2), (key1106, 2), (key1106, 2), (key1071, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1242, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1232, 2), (key1232, 2), (key993, 2), (key993, 2), (key1028, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2)]

theorem rawRowCheck18712 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18712 := by decide +kernel

def row18712 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18712 : row18712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18712 := by decide +kernel

theorem rowEval18712 (x : Key → ℝ) : Integer.Sparse.eval row18712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18712, Integer.Sparse.eval_collectBalanced, rawRowCheck18712]

def rawRow18713 : Integer.Sparse Key := [(key1123, 2), (key1235, 2), (key1123, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1150, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1106, 2), (key993, 2), (key1028, 2), (key1150, 2), (key1071, 2), (key1150, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1036, 2)]

theorem rawRowCheck18713 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18713 := by decide +kernel

def row18713 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18713 : row18713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18713 := by decide +kernel

theorem rowEval18713 (x : Key → ℝ) : Integer.Sparse.eval row18713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18713, Integer.Sparse.eval_collectBalanced, rawRowCheck18713]

def rawRow18714 : Integer.Sparse Key := [(key1235, 2), (key1123, 2), (key1123, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1106, 2), (key1106, 2), (key1028, 2), (key1242, 2), (key1150, 2), (key1150, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1242, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1071, 2), (key1235, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1015, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1001, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1028, 2), (key993, 2), (key1150, 2), (key1150, 2), (key1071, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1114, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1036, 2), (key1001, 2)]

theorem rawRowCheck18714 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18714 := by decide +kernel

def row18714 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18714 : row18714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18714 := by decide +kernel

theorem rowEval18714 (x : Key → ℝ) : Integer.Sparse.eval row18714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18714, Integer.Sparse.eval_collectBalanced, rawRowCheck18714]

def rawRow18715 : Integer.Sparse Key := [(key1071, 2), (key1071, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1242, 2), (key1242, 2), (key1015, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1235, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key993, 2), (key993, 2), (key993, 2), (key1028, 2), (key1028, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2)]

theorem rawRowCheck18715 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18715 := by decide +kernel

def row18715 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18715 : row18715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18715 := by decide +kernel

theorem rowEval18715 (x : Key → ℝ) : Integer.Sparse.eval row18715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18715, Integer.Sparse.eval_collectBalanced, rawRowCheck18715]

def rawRow18716 : Integer.Sparse Key := [(key1150, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1106, 2), (key993, 2), (key993, 2), (key1028, 2), (key1028, 2), (key1106, 2), (key1106, 2)]

theorem rawRowCheck18716 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18716 := by decide +kernel

def row18716 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18716 : row18716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18716 := by decide +kernel

theorem rowEval18716 (x : Key → ℝ) : Integer.Sparse.eval row18716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18716, Integer.Sparse.eval_collectBalanced, rawRowCheck18716]

def rawRow18717 : Integer.Sparse Key := [(key1150, 2), (key1242, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1071, 2), (key1150, 2), (key1123, 2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1106, 2), (key993, 2), (key1028, 2)]

theorem rawRowCheck18717 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18717 := by decide +kernel

def row18717 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18717 : row18717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18717 := by decide +kernel

theorem rowEval18717 (x : Key → ℝ) : Integer.Sparse.eval row18717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18717, Integer.Sparse.eval_collectBalanced, rawRowCheck18717]

def rawRow18718 : Integer.Sparse Key := [(key1242, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1071, 2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1001, 2), (key1114, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1036, 2), (key1001, 2), (key1106, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1028, 2), (key993, 2)]

theorem rawRowCheck18718 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18718 := by decide +kernel

def row18718 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

theorem rowCheck18718 : row18718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18718 := by decide +kernel

theorem rowEval18718 (x : Key → ℝ) : Integer.Sparse.eval row18718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18718, Integer.Sparse.eval_collectBalanced, rawRowCheck18718]

def rawRow18719 : Integer.Sparse Key := [(key973, 24), (key1087, 24), (key1087, 24), (key1087, 24), (key1160, 24)]

theorem rawRowCheck18719 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form3 = rawRow18719 := by decide +kernel

def row18719 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18719 : row18719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18719 := by decide +kernel

theorem rowEval18719 (x : Key → ℝ) : Integer.Sparse.eval row18719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18719, Integer.Sparse.eval_collectBalanced, rawRowCheck18719]

def rawRow18720 : Integer.Sparse Key := [(key973, 24), (key1087, 24), (key1087, 24), (key1160, 24), (key1087, 24)]

theorem rawRowCheck18720 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form3 = rawRow18720 := by decide +kernel

def row18720 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18720 : row18720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18720 := by decide +kernel

theorem rowEval18720 (x : Key → ℝ) : Integer.Sparse.eval row18720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18720, Integer.Sparse.eval_collectBalanced, rawRowCheck18720]

def rawRow18721 : Integer.Sparse Key := [(key973, 24), (key1087, 24), (key1160, 24), (key1087, 24), (key1087, 24)]

theorem rawRowCheck18721 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form3 = rawRow18721 := by decide +kernel

def row18721 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18721 : row18721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18721 := by decide +kernel

theorem rowEval18721 (x : Key → ℝ) : Integer.Sparse.eval row18721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18721, Integer.Sparse.eval_collectBalanced, rawRowCheck18721]

def rawRow18722 : Integer.Sparse Key := [(key973, 24), (key1160, 24), (key1087, 24), (key1087, 24), (key1087, 24)]

theorem rawRowCheck18722 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18722 := by decide +kernel

def row18722 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18722 : row18722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18722 := by decide +kernel

theorem rowEval18722 (x : Key → ℝ) : Integer.Sparse.eval row18722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18722, Integer.Sparse.eval_collectBalanced, rawRowCheck18722]

def rawRow18723 : Integer.Sparse Key := [(key1087, 24), (key973, 24), (key1087, 24), (key1087, 24), (key1160, 24)]

theorem rawRowCheck18723 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form3 = rawRow18723 := by decide +kernel

def row18723 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18723 : row18723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18723 := by decide +kernel

theorem rowEval18723 (x : Key → ℝ) : Integer.Sparse.eval row18723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18723, Integer.Sparse.eval_collectBalanced, rawRowCheck18723]

def rawRow18724 : Integer.Sparse Key := [(key1087, 24), (key973, 24), (key1087, 24), (key1160, 24), (key1087, 24)]

theorem rawRowCheck18724 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form3 = rawRow18724 := by decide +kernel

def row18724 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18724 : row18724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18724 := by decide +kernel

theorem rowEval18724 (x : Key → ℝ) : Integer.Sparse.eval row18724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18724, Integer.Sparse.eval_collectBalanced, rawRowCheck18724]

def rawRow18725 : Integer.Sparse Key := [(key1087, 24), (key973, 24), (key1160, 24), (key1087, 24), (key1087, 24)]

theorem rawRowCheck18725 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form3 = rawRow18725 := by decide +kernel

def row18725 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18725 : row18725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18725 := by decide +kernel

theorem rowEval18725 (x : Key → ℝ) : Integer.Sparse.eval row18725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18725, Integer.Sparse.eval_collectBalanced, rawRowCheck18725]

def rawRow18726 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key973, 24), (key1087, 24), (key1160, 24)]

theorem rawRowCheck18726 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form3 = rawRow18726 := by decide +kernel

def row18726 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18726 : row18726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18726 := by decide +kernel

theorem rowEval18726 (x : Key → ℝ) : Integer.Sparse.eval row18726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18726, Integer.Sparse.eval_collectBalanced, rawRowCheck18726]

def rawRow18727 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key973, 24), (key1160, 24), (key1087, 24)]

theorem rawRowCheck18727 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form3 = rawRow18727 := by decide +kernel

def row18727 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18727 : row18727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18727 := by decide +kernel

theorem rowEval18727 (x : Key → ℝ) : Integer.Sparse.eval row18727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18727, Integer.Sparse.eval_collectBalanced, rawRowCheck18727]

def rawRow18728 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1087, 24), (key973, 24), (key1160, 24)]

theorem rawRowCheck18728 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form3 = rawRow18728 := by decide +kernel

def row18728 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18728 : row18728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18728 := by decide +kernel

theorem rowEval18728 (x : Key → ℝ) : Integer.Sparse.eval row18728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18728, Integer.Sparse.eval_collectBalanced, rawRowCheck18728]

def rawRow18729 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1087, 24), (key1160, 24), (key973, 24)]

theorem rawRowCheck18729 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form3 = rawRow18729 := by decide +kernel

def row18729 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18729 : row18729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18729 := by decide +kernel

theorem rowEval18729 (x : Key → ℝ) : Integer.Sparse.eval row18729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18729, Integer.Sparse.eval_collectBalanced, rawRowCheck18729]

def rawRow18730 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1160, 24), (key973, 24), (key1087, 24)]

theorem rawRowCheck18730 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form3 = rawRow18730 := by decide +kernel

def row18730 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18730 : row18730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18730 := by decide +kernel

theorem rowEval18730 (x : Key → ℝ) : Integer.Sparse.eval row18730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18730, Integer.Sparse.eval_collectBalanced, rawRowCheck18730]

def rawRow18731 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1160, 24), (key1087, 24), (key973, 24)]

theorem rawRowCheck18731 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form3 = rawRow18731 := by decide +kernel

def row18731 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18731 : row18731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18731 := by decide +kernel

theorem rowEval18731 (x : Key → ℝ) : Integer.Sparse.eval row18731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18731, Integer.Sparse.eval_collectBalanced, rawRowCheck18731]

def rawRow18732 : Integer.Sparse Key := [(key1087, 24), (key1160, 24), (key973, 24), (key1087, 24), (key1087, 24)]

theorem rawRowCheck18732 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18732 := by decide +kernel

def row18732 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18732 : row18732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18732 := by decide +kernel

theorem rowEval18732 (x : Key → ℝ) : Integer.Sparse.eval row18732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18732, Integer.Sparse.eval_collectBalanced, rawRowCheck18732]

def rawRow18733 : Integer.Sparse Key := [(key1087, 24), (key1160, 24), (key1087, 24), (key973, 24), (key1087, 24)]

theorem rawRowCheck18733 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18733 := by decide +kernel

def row18733 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18733 : row18733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18733 := by decide +kernel

theorem rowEval18733 (x : Key → ℝ) : Integer.Sparse.eval row18733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18733, Integer.Sparse.eval_collectBalanced, rawRowCheck18733]

def rawRow18734 : Integer.Sparse Key := [(key1087, 24), (key1160, 24), (key1087, 24), (key1087, 24), (key973, 24)]

theorem rawRowCheck18734 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18734 := by decide +kernel

def row18734 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18734 : row18734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18734 := by decide +kernel

theorem rowEval18734 (x : Key → ℝ) : Integer.Sparse.eval row18734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18734, Integer.Sparse.eval_collectBalanced, rawRowCheck18734]

def rawRow18735 : Integer.Sparse Key := [(key1160, 24), (key973, 24), (key1087, 24), (key1087, 24), (key1087, 24)]

theorem rawRowCheck18735 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18735 := by decide +kernel

def row18735 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18735 : row18735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18735 := by decide +kernel

theorem rowEval18735 (x : Key → ℝ) : Integer.Sparse.eval row18735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18735, Integer.Sparse.eval_collectBalanced, rawRowCheck18735]

def rawRow18736 : Integer.Sparse Key := [(key1160, 24), (key1087, 24), (key973, 24), (key1087, 24), (key1087, 24)]

theorem rawRowCheck18736 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18736 := by decide +kernel

def row18736 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18736 : row18736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18736 := by decide +kernel

theorem rowEval18736 (x : Key → ℝ) : Integer.Sparse.eval row18736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18736, Integer.Sparse.eval_collectBalanced, rawRowCheck18736]

def rawRow18737 : Integer.Sparse Key := [(key1160, 24), (key1087, 24), (key1087, 24), (key973, 24), (key1087, 24)]

theorem rawRowCheck18737 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18737 := by decide +kernel

def row18737 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18737 : row18737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18737 := by decide +kernel

theorem rowEval18737 (x : Key → ℝ) : Integer.Sparse.eval row18737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18737, Integer.Sparse.eval_collectBalanced, rawRowCheck18737]

def rawRow18738 : Integer.Sparse Key := [(key1160, 24), (key1087, 24), (key1087, 24), (key1087, 24), (key973, 24)]

theorem rawRowCheck18738 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18738 := by decide +kernel

def row18738 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

theorem rowCheck18738 : row18738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18738 := by decide +kernel

theorem rowEval18738 (x : Key → ℝ) : Integer.Sparse.eval row18738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18738, Integer.Sparse.eval_collectBalanced, rawRowCheck18738]

def rawRow18739 : Integer.Sparse Key := [(key1, 6), (key7, 6), (key7, 6), (key7, 6), (key84, 6), (key90, 6), (key90, 6), (key84, 6), (key90, 6), (key84, 6), (key151, 6), (key90, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key193, 6), (key193, 6), (key193, 6), (key202, 6)]

theorem rawRowCheck18739 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form4 = rawRow18739 := by decide +kernel

def row18739 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

theorem rowCheck18739 : row18739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18739 := by decide +kernel

theorem rowEval18739 (x : Key → ℝ) : Integer.Sparse.eval row18739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck18739, Integer.Sparse.eval_collectBalanced, rawRowCheck18739]

def rawRow18740 : Integer.Sparse Key := [(key7, 6), (key1, 6), (key7, 6), (key7, 6), (key90, 6), (key84, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key84, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key90, 6), (key193, 6), (key193, 6), (key202, 6), (key193, 6)]

theorem rawRowCheck18740 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form4 = rawRow18740 := by decide +kernel

def row18740 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

theorem rowCheck18740 : row18740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18740 := by decide +kernel

theorem rowEval18740 (x : Key → ℝ) : Integer.Sparse.eval row18740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18740, Integer.Sparse.eval_collectBalanced, rawRowCheck18740]

def rawRow18741 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key1, 6), (key7, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key84, 6), (key151, 6), (key90, 6), (key90, 6), (key193, 6), (key202, 6), (key193, 6), (key193, 6)]

theorem rawRowCheck18741 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form4 = rawRow18741 := by decide +kernel

def row18741 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

theorem rowCheck18741 : row18741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18741 := by decide +kernel

theorem rowEval18741 (x : Key → ℝ) : Integer.Sparse.eval row18741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18741, Integer.Sparse.eval_collectBalanced, rawRowCheck18741]

def rawRow18742 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key7, 6), (key1, 6), (key151, 6), (key151, 6), (key151, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key84, 6), (key84, 6), (key84, 6), (key202, 6), (key193, 6), (key193, 6), (key193, 6)]

theorem rawRowCheck18742 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow18742 := by decide +kernel

def row18742 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

theorem rowCheck18742 : row18742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18742 := by decide +kernel

theorem rowEval18742 (x : Key → ℝ) : Integer.Sparse.eval row18742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18742, Integer.Sparse.eval_collectBalanced, rawRowCheck18742]

def rawRow18743 : Integer.Sparse Key := [(key84, 6), (key90, 6), (key90, 6), (key151, 6), (key1, 6), (key7, 6), (key7, 6), (key84, 6), (key90, 6), (key84, 6), (key151, 6), (key90, 6), (key151, 6), (key193, 6), (key193, 6), (key202, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6)]

theorem rawRowCheck18743 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form4 = rawRow18743 := by decide +kernel

def row18743 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

theorem rowCheck18743 : row18743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18743 := by decide +kernel

theorem rowEval18743 (x : Key → ℝ) : Integer.Sparse.eval row18743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck18743, Integer.Sparse.eval_collectBalanced, rawRowCheck18743]

def rawRow18744 : Integer.Sparse Key := [(key90, 6), (key84, 6), (key90, 6), (key151, 6), (key7, 6), (key1, 6), (key7, 6), (key90, 6), (key84, 6), (key151, 6), (key84, 6), (key151, 6), (key90, 6), (key193, 6), (key202, 6), (key193, 6), (key7, 6), (key90, 6), (key151, 6), (key90, 6)]

theorem rawRowCheck18744 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form4 = rawRow18744 := by decide +kernel

def row18744 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

theorem rowCheck18744 : row18744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18744 := by decide +kernel

theorem rowEval18744 (x : Key → ℝ) : Integer.Sparse.eval row18744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18744, Integer.Sparse.eval_collectBalanced, rawRowCheck18744]

def rawRow18745 : Integer.Sparse Key := [(key90, 6), (key90, 6), (key84, 6), (key151, 6), (key7, 6), (key7, 6), (key1, 6), (key151, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key84, 6), (key202, 6), (key193, 6), (key193, 6), (key7, 6), (key151, 6), (key90, 6), (key90, 6)]

theorem rawRowCheck18745 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form4 = rawRow18745 := by decide +kernel

def row18745 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

theorem rowCheck18745 : row18745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18745 := by decide +kernel

theorem rowEval18745 (x : Key → ℝ) : Integer.Sparse.eval row18745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18745, Integer.Sparse.eval_collectBalanced, rawRowCheck18745]

def rawRow18746 : Integer.Sparse Key := [(key84, 6), (key90, 6), (key151, 6), (key90, 6), (key84, 6), (key90, 6), (key151, 6), (key1, 6), (key7, 6), (key84, 6), (key151, 6), (key193, 6), (key202, 6), (key7, 6), (key90, 6), (key151, 6), (key90, 6), (key7, 6), (key90, 6), (key151, 6)]

theorem rawRowCheck18746 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form4 = rawRow18746 := by decide +kernel

def row18746 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

theorem rowCheck18746 : row18746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18746 := by decide +kernel

theorem rowEval18746 (x : Key → ℝ) : Integer.Sparse.eval row18746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck18746, Integer.Sparse.eval_collectBalanced, rawRowCheck18746]

def rawRow18747 : Integer.Sparse Key := [(key90, 6), (key84, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key7, 6), (key1, 6), (key151, 6), (key84, 6), (key202, 6), (key193, 6), (key7, 6), (key151, 6), (key90, 6), (key90, 6), (key7, 6), (key151, 6), (key90, 6)]

theorem rawRowCheck18747 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form4 = rawRow18747 := by decide +kernel

def row18747 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

theorem rowCheck18747 : row18747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18747 := by decide +kernel

theorem rowEval18747 (x : Key → ℝ) : Integer.Sparse.eval row18747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18747, Integer.Sparse.eval_collectBalanced, rawRowCheck18747]

def rawRow18748 : Integer.Sparse Key := [(key84, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key90, 6), (key84, 6), (key151, 6), (key1, 6), (key202, 6), (key7, 6), (key151, 6), (key90, 6), (key7, 6), (key151, 6), (key90, 6), (key90, 6), (key7, 6), (key151, 6)]

theorem rawRowCheck18748 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form4 = rawRow18748 := by decide +kernel

def row18748 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 36), (key202, 6)]

theorem rowCheck18748 : row18748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18748 := by decide +kernel

theorem rowEval18748 (x : Key → ℝ) : Integer.Sparse.eval row18748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck18748, Integer.Sparse.eval_collectBalanced, rawRowCheck18748]

def rawRow18749 : Integer.Sparse Key := [(key151, 6), (key84, 6), (key90, 6), (key90, 6), (key151, 6), (key84, 6), (key90, 6), (key151, 6), (key84, 6), (key202, 6), (key1, 6), (key151, 6), (key7, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6)]

theorem rawRowCheck18749 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form4 = rawRow18749 := by decide +kernel

def row18749 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 36), (key202, 6)]

theorem rowCheck18749 : row18749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18749 := by decide +kernel

theorem rowEval18749 (x : Key → ℝ) : Integer.Sparse.eval row18749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18749, Integer.Sparse.eval_collectBalanced, rawRowCheck18749]

def rawRow18750 : Integer.Sparse Key := [(key90, 6), (key151, 6), (key84, 6), (key90, 6), (key90, 6), (key151, 6), (key84, 6), (key193, 6), (key202, 6), (key7, 6), (key151, 6), (key1, 6), (key84, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6)]

theorem rawRowCheck18750 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form4 = rawRow18750 := by decide +kernel

def row18750 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

theorem rowCheck18750 : row18750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18750 := by decide +kernel

theorem rowEval18750 (x : Key → ℝ) : Integer.Sparse.eval row18750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18750, Integer.Sparse.eval_collectBalanced, rawRowCheck18750]

def rawRow18751 : Integer.Sparse Key := [(key151, 6), (key90, 6), (key84, 6), (key90, 6), (key151, 6), (key90, 6), (key84, 6), (key202, 6), (key193, 6), (key151, 6), (key7, 6), (key84, 6), (key1, 6), (key151, 6), (key90, 6), (key7, 6), (key90, 6), (key151, 6), (key90, 6), (key7, 6)]

theorem rawRowCheck18751 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form4 = rawRow18751 := by decide +kernel

def row18751 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

theorem rowCheck18751 : row18751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18751 := by decide +kernel

theorem rowEval18751 (x : Key → ℝ) : Integer.Sparse.eval row18751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18751, Integer.Sparse.eval_collectBalanced, rawRowCheck18751]

def rawRow18752 : Integer.Sparse Key := [(key90, 6), (key90, 6), (key151, 6), (key84, 6), (key193, 6), (key193, 6), (key202, 6), (key7, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key151, 6), (key1, 6), (key84, 6), (key84, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6)]

theorem rawRowCheck18752 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form4 = rawRow18752 := by decide +kernel

def row18752 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

theorem rowCheck18752 : row18752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18752 := by decide +kernel

theorem rowEval18752 (x : Key → ℝ) : Integer.Sparse.eval row18752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18752, Integer.Sparse.eval_collectBalanced, rawRowCheck18752]

def rawRow18753 : Integer.Sparse Key := [(key90, 6), (key151, 6), (key90, 6), (key84, 6), (key193, 6), (key202, 6), (key193, 6), (key90, 6), (key151, 6), (key7, 6), (key151, 6), (key7, 6), (key90, 6), (key84, 6), (key1, 6), (key84, 6), (key151, 6), (key90, 6), (key7, 6), (key90, 6)]

theorem rawRowCheck18753 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form4 = rawRow18753 := by decide +kernel

def row18753 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

theorem rowCheck18753 : row18753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18753 := by decide +kernel

theorem rowEval18753 (x : Key → ℝ) : Integer.Sparse.eval row18753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18753, Integer.Sparse.eval_collectBalanced, rawRowCheck18753]

def rawRow18754 : Integer.Sparse Key := [(key151, 6), (key90, 6), (key90, 6), (key84, 6), (key202, 6), (key193, 6), (key193, 6), (key151, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6), (key7, 6), (key84, 6), (key84, 6), (key1, 6), (key151, 6), (key90, 6), (key90, 6), (key7, 6)]

theorem rawRowCheck18754 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form4 = rawRow18754 := by decide +kernel

def row18754 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

theorem rowCheck18754 : row18754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18754 := by decide +kernel

theorem rowEval18754 (x : Key → ℝ) : Integer.Sparse.eval row18754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18754, Integer.Sparse.eval_collectBalanced, rawRowCheck18754]

def rawRow18755 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key193, 6), (key202, 6), (key7, 6), (key7, 6), (key7, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key151, 6), (key151, 6), (key151, 6), (key1, 6), (key84, 6), (key84, 6), (key84, 6)]

theorem rawRowCheck18755 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form4 = rawRow18755 := by decide +kernel

def row18755 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

theorem rowCheck18755 : row18755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18755 := by decide +kernel

theorem rowEval18755 (x : Key → ℝ) : Integer.Sparse.eval row18755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18755, Integer.Sparse.eval_collectBalanced, rawRowCheck18755]

def rawRow18756 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key202, 6), (key193, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key84, 6), (key1, 6), (key84, 6), (key84, 6)]

theorem rawRowCheck18756 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form4 = rawRow18756 := by decide +kernel

def row18756 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

theorem rowCheck18756 : row18756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18756 := by decide +kernel

theorem rowEval18756 (x : Key → ℝ) : Integer.Sparse.eval row18756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18756, Integer.Sparse.eval_collectBalanced, rawRowCheck18756]

def rawRow18757 : Integer.Sparse Key := [(key193, 6), (key202, 6), (key193, 6), (key193, 6), (key90, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key7, 6), (key90, 6), (key84, 6), (key84, 6), (key1, 6), (key84, 6)]

theorem rawRowCheck18757 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form4 = rawRow18757 := by decide +kernel

def row18757 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

theorem rowCheck18757 : row18757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18757 := by decide +kernel

theorem rowEval18757 (x : Key → ℝ) : Integer.Sparse.eval row18757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18757, Integer.Sparse.eval_collectBalanced, rawRowCheck18757]

def rawRow18758 : Integer.Sparse Key := [(key202, 6), (key193, 6), (key193, 6), (key193, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6), (key7, 6), (key90, 6), (key90, 6), (key7, 6), (key84, 6), (key84, 6), (key84, 6), (key1, 6)]

theorem rawRowCheck18758 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form4 = rawRow18758 := by decide +kernel

def row18758 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

theorem rowCheck18758 : row18758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18758 := by decide +kernel

theorem rowEval18758 (x : Key → ℝ) : Integer.Sparse.eval row18758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18758, Integer.Sparse.eval_collectBalanced, rawRowCheck18758]

def rawRow18759 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 6), (key2366, 6), (key2456, 6), (key2456, 6), (key2461, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2523, 6), (key2567, 6), (key2567, 6), (key2579, 6), (key2579, 6)]

theorem rawRowCheck18759 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form0 = rawRow18759 := by decide +kernel

def row18759 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

theorem rowCheck18759 : row18759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18759 := by decide +kernel

theorem rowEval18759 (x : Key → ℝ) : Integer.Sparse.eval row18759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18759, Integer.Sparse.eval_collectBalanced, rawRowCheck18759]

def rawRow18760 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2361, 6), (key2366, 6), (key2456, 6), (key2461, 6), (key2456, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2567, 6), (key2579, 6), (key2567, 6), (key2579, 6)]

theorem rawRowCheck18760 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form0 = rawRow18760 := by decide +kernel

def row18760 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

theorem rowCheck18760 : row18760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18760 := by decide +kernel

theorem rowEval18760 (x : Key → ℝ) : Integer.Sparse.eval row18760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18760, Integer.Sparse.eval_collectBalanced, rawRowCheck18760]

def rawRow18761 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2361, 6), (key2366, 6), (key2461, 6), (key2456, 6), (key2456, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2567, 6), (key2579, 6), (key2579, 6), (key2567, 6)]

theorem rawRowCheck18761 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form0 = rawRow18761 := by decide +kernel

def row18761 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

theorem rowCheck18761 : row18761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18761 := by decide +kernel

theorem rowEval18761 (x : Key → ℝ) : Integer.Sparse.eval row18761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18761, Integer.Sparse.eval_collectBalanced, rawRowCheck18761]

def rawRow18762 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2363, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2456, 6), (key2461, 6), (key2456, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2579, 6), (key2567, 6), (key2567, 6), (key2579, 6)]

theorem rawRowCheck18762 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18762 := by decide +kernel

def row18762 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

theorem rowCheck18762 : row18762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18762 := by decide +kernel

theorem rowEval18762 (x : Key → ℝ) : Integer.Sparse.eval row18762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18762, Integer.Sparse.eval_collectBalanced, rawRowCheck18762]

def rawRow18763 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2363, 6), (key2361, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2461, 6), (key2456, 6), (key2523, 6), (key2456, 6), (key2523, 6), (key2461, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2579, 6), (key2567, 6), (key2579, 6), (key2567, 6)]

theorem rawRowCheck18763 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18763 := by decide +kernel

def row18763 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

theorem rowCheck18763 : row18763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18763 := by decide +kernel

theorem rowEval18763 (x : Key → ℝ) : Integer.Sparse.eval row18763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18763, Integer.Sparse.eval_collectBalanced, rawRowCheck18763]

def rawRow18764 : Integer.Sparse Key := [(key2363, 6), (key2363, 6), (key2357, 6), (key2361, 6), (key2523, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2461, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2456, 6), (key2579, 6), (key2579, 6), (key2567, 6), (key2567, 6)]

theorem rawRowCheck18764 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18764 := by decide +kernel

def row18764 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

theorem rowCheck18764 : row18764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18764 := by decide +kernel

theorem rowEval18764 (x : Key → ℝ) : Integer.Sparse.eval row18764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18764, Integer.Sparse.eval_collectBalanced, rawRowCheck18764]

def rawRow18765 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2357, 6), (key2361, 6), (key2366, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2567, 6), (key2579, 6), (key2579, 6), (key2366, 6), (key2461, 6), (key2523, 6), (key2523, 6)]

theorem rawRowCheck18765 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form0 = rawRow18765 := by decide +kernel

def row18765 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 12), (key2456, 12), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 6), (key2523, 24), (key2567, 6), (key2579, 12)]

theorem rowCheck18765 : row18765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18765 := by decide +kernel

theorem rowEval18765 (x : Key → ℝ) : Integer.Sparse.eval row18765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18765, Integer.Sparse.eval_collectBalanced, rawRowCheck18765]

def rawRow18766 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2363, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2579, 6), (key2567, 6), (key2579, 6), (key2366, 6), (key2523, 6), (key2461, 6), (key2523, 6)]

theorem rawRowCheck18766 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form0 = rawRow18766 := by decide +kernel

def row18766 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 12), (key2456, 12), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 6), (key2523, 24), (key2567, 6), (key2579, 12)]

theorem rowCheck18766 : row18766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18766 := by decide +kernel

theorem rowEval18766 (x : Key → ℝ) : Integer.Sparse.eval row18766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18766, Integer.Sparse.eval_collectBalanced, rawRowCheck18766]

def rawRow18767 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2452, 6), (key2519, 6), (key2363, 6), (key2357, 6), (key2361, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2579, 6), (key2579, 6), (key2567, 6), (key2366, 6), (key2523, 6), (key2523, 6), (key2461, 6)]

theorem rawRowCheck18767 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form0 = rawRow18767 := by decide +kernel

def row18767 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 12), (key2456, 12), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 6), (key2523, 24), (key2567, 6), (key2579, 12)]

theorem rowCheck18767 : row18767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18767 := by decide +kernel

theorem rowEval18767 (x : Key → ℝ) : Integer.Sparse.eval row18767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18767, Integer.Sparse.eval_collectBalanced, rawRowCheck18767]

def rawRow18768 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2361, 6), (key2517, 6), (key2517, 6), (key2579, 6), (key2579, 6), (key2366, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2366, 6), (key2523, 6), (key2523, 6)]

theorem rawRowCheck18768 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form0 = rawRow18768 := by decide +kernel

def row18768 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 24), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 12), (key2523, 24), (key2579, 12)]

theorem rowCheck18768 : row18768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18768 := by decide +kernel

theorem rowEval18768 (x : Key → ℝ) : Integer.Sparse.eval row18768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18768, Integer.Sparse.eval_collectBalanced, rawRowCheck18768]

def rawRow18769 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2452, 6), (key2528, 6), (key2560, 6), (key2357, 6), (key2560, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2366, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2366, 6), (key2523, 6)]

theorem rawRowCheck18769 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form0 = rawRow18769 := by decide +kernel

def row18769 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 24), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 24), (key2528, 6), (key2560, 12)]

theorem rowCheck18769 : row18769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18769 := by decide +kernel

theorem rowEval18769 (x : Key → ℝ) : Integer.Sparse.eval row18769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18769, Integer.Sparse.eval_collectBalanced, rawRowCheck18769]

def rawRow18770 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2452, 6), (key2560, 6), (key2528, 6), (key2560, 6), (key2357, 6), (key2517, 6), (key2361, 6), (key2523, 6), (key2523, 6), (key2366, 6), (key2461, 6), (key2523, 6), (key2523, 6), (key2366, 6)]

theorem rawRowCheck18770 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form0 = rawRow18770 := by decide +kernel

def row18770 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 24), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 24), (key2528, 6), (key2560, 12)]

theorem rowCheck18770 : row18770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18770 := by decide +kernel

theorem rowEval18770 (x : Key → ℝ) : Integer.Sparse.eval row18770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18770, Integer.Sparse.eval_collectBalanced, rawRowCheck18770]

def rawRow18771 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2357, 6), (key2363, 6), (key2452, 6), (key2530, 6), (key2519, 6), (key2560, 6), (key2361, 6), (key2456, 6), (key2517, 6), (key2523, 6), (key2366, 6), (key2461, 6), (key2523, 6)]

theorem rawRowCheck18771 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form0 = rawRow18771 := by decide +kernel

def row18771 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

theorem rowCheck18771 : row18771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18771 := by decide +kernel

theorem rowEval18771 (x : Key → ℝ) : Integer.Sparse.eval row18771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18771, Integer.Sparse.eval_collectBalanced, rawRowCheck18771]

def rawRow18772 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2519, 6), (key2452, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2363, 6), (key2357, 6), (key2530, 6), (key2452, 6), (key2560, 6), (key2519, 6), (key2361, 6), (key2517, 6), (key2456, 6), (key2523, 6), (key2366, 6), (key2523, 6), (key2461, 6)]

theorem rawRowCheck18772 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form0 = rawRow18772 := by decide +kernel

def row18772 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

theorem rowCheck18772 : row18772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18772 := by decide +kernel

theorem rowEval18772 (x : Key → ℝ) : Integer.Sparse.eval row18772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18772, Integer.Sparse.eval_collectBalanced, rawRowCheck18772]

def rawRow18773 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2560, 6), (key2363, 6), (key2530, 6), (key2456, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2461, 6), (key2366, 6), (key2523, 6)]

theorem rawRowCheck18773 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form0 = rawRow18773 := by decide +kernel

def row18773 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

theorem rowCheck18773 : row18773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18773 := by decide +kernel

theorem rowEval18773 (x : Key → ℝ) : Integer.Sparse.eval row18773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18773, Integer.Sparse.eval_collectBalanced, rawRowCheck18773]

def rawRow18774 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2519, 6), (key2452, 6), (key2560, 6), (key2357, 6), (key2530, 6), (key2363, 6), (key2456, 6), (key2517, 6), (key2361, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2366, 6)]

theorem rawRowCheck18774 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form0 = rawRow18774 := by decide +kernel

def row18774 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

theorem rowCheck18774 : row18774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18774 := by decide +kernel

theorem rowEval18774 (x : Key → ℝ) : Integer.Sparse.eval row18774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18774, Integer.Sparse.eval_collectBalanced, rawRowCheck18774]

def rawRow18775 : Integer.Sparse Key := [(key2458, 6), (key2519, 6), (key2452, 6), (key2452, 6), (key2530, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2519, 6), (key2357, 6), (key2452, 6), (key2517, 6), (key2361, 6), (key2456, 6), (key2523, 6), (key2523, 6), (key2366, 6), (key2461, 6)]

theorem rawRowCheck18775 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form0 = rawRow18775 := by decide +kernel

def row18775 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

theorem rowCheck18775 : row18775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18775 := by decide +kernel

theorem rowEval18775 (x : Key → ℝ) : Integer.Sparse.eval row18775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18775, Integer.Sparse.eval_collectBalanced, rawRowCheck18775]

def rawRow18776 : Integer.Sparse Key := [(key2519, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2560, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2519, 6), (key2363, 6), (key2452, 6), (key2357, 6), (key2517, 6), (key2456, 6), (key2361, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2366, 6)]

theorem rawRowCheck18776 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form0 = rawRow18776 := by decide +kernel

def row18776 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

theorem rowCheck18776 : row18776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18776 := by decide +kernel

theorem rowEval18776 (x : Key → ℝ) : Integer.Sparse.eval row18776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18776, Integer.Sparse.eval_collectBalanced, rawRowCheck18776]

def rawRow18777 : Integer.Sparse Key := [(key2528, 6), (key2530, 6), (key2530, 6), (key2560, 6), (key2357, 6), (key2363, 6), (key2363, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2530, 6), (key2458, 6), (key2530, 6), (key2519, 6), (key2519, 6), (key2560, 6), (key2361, 6), (key2456, 6), (key2456, 6), (key2517, 6)]

theorem rawRowCheck18777 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18777 := by decide +kernel

def row18777 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18777 : row18777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18777 := by decide +kernel

theorem rowEval18777 (x : Key → ℝ) : Integer.Sparse.eval row18777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18777, Integer.Sparse.eval_collectBalanced, rawRowCheck18777]

def rawRow18778 : Integer.Sparse Key := [(key2530, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2357, 6), (key2363, 6), (key2458, 6), (key2452, 6), (key2530, 6), (key2452, 6), (key2530, 6), (key2458, 6), (key2519, 6), (key2560, 6), (key2519, 6), (key2361, 6), (key2456, 6), (key2517, 6), (key2456, 6)]

theorem rawRowCheck18778 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18778 := by decide +kernel

def row18778 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18778 : row18778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18778 := by decide +kernel

theorem rowEval18778 (x : Key → ℝ) : Integer.Sparse.eval row18778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18778, Integer.Sparse.eval_collectBalanced, rawRowCheck18778]

def rawRow18779 : Integer.Sparse Key := [(key2530, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2363, 6), (key2363, 6), (key2357, 6), (key2530, 6), (key2530, 6), (key2458, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2560, 6), (key2519, 6), (key2519, 6), (key2361, 6), (key2517, 6), (key2456, 6), (key2456, 6)]

theorem rawRowCheck18779 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18779 := by decide +kernel

def row18779 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18779 : row18779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18779 := by decide +kernel

theorem rowEval18779 (x : Key → ℝ) : Integer.Sparse.eval row18779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18779, Integer.Sparse.eval_collectBalanced, rawRowCheck18779]

def rawRow18780 : Integer.Sparse Key := [(key2528, 6), (key2530, 6), (key2560, 6), (key2530, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2357, 6), (key2363, 6), (key2452, 6), (key2530, 6), (key2519, 6), (key2560, 6), (key2363, 6), (key2458, 6), (key2530, 6), (key2456, 6), (key2361, 6), (key2456, 6), (key2517, 6)]

theorem rawRowCheck18780 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form0 = rawRow18780 := by decide +kernel

def row18780 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18780 : row18780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18780 := by decide +kernel

theorem rowEval18780 (x : Key → ℝ) : Integer.Sparse.eval row18780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18780, Integer.Sparse.eval_collectBalanced, rawRowCheck18780]

def rawRow18781 : Integer.Sparse Key := [(key2530, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2363, 6), (key2357, 6), (key2530, 6), (key2452, 6), (key2560, 6), (key2519, 6), (key2363, 6), (key2530, 6), (key2458, 6), (key2456, 6), (key2361, 6), (key2517, 6), (key2456, 6)]

theorem rawRowCheck18781 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form0 = rawRow18781 := by decide +kernel

def row18781 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18781 : row18781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18781 := by decide +kernel

theorem rowEval18781 (x : Key → ℝ) : Integer.Sparse.eval row18781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18781, Integer.Sparse.eval_collectBalanced, rawRowCheck18781]

def rawRow18782 : Integer.Sparse Key := [(key2528, 6), (key2560, 6), (key2530, 6), (key2530, 6), (key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2560, 6), (key2363, 6), (key2530, 6), (key2458, 6), (key2363, 6), (key2530, 6), (key2456, 6), (key2456, 6), (key2361, 6), (key2517, 6)]

theorem rawRowCheck18782 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form0 = rawRow18782 := by decide +kernel

def row18782 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18782 : row18782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18782 := by decide +kernel

theorem rowEval18782 (x : Key → ℝ) : Integer.Sparse.eval row18782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18782, Integer.Sparse.eval_collectBalanced, rawRowCheck18782]

def rawRow18783 : Integer.Sparse Key := [(key2560, 6), (key2528, 6), (key2530, 6), (key2530, 6), (key2519, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2560, 6), (key2357, 6), (key2530, 6), (key2363, 6), (key2458, 6), (key2530, 6), (key2363, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2361, 6)]

theorem rawRowCheck18783 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form0 = rawRow18783 := by decide +kernel

def row18783 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18783 : row18783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18783 := by decide +kernel

theorem rowEval18783 (x : Key → ℝ) : Integer.Sparse.eval row18783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18783, Integer.Sparse.eval_collectBalanced, rawRowCheck18783]

def rawRow18784 : Integer.Sparse Key := [(key2530, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2519, 6), (key2357, 6), (key2452, 6), (key2530, 6), (key2363, 6), (key2458, 6), (key2456, 6), (key2517, 6), (key2361, 6), (key2456, 6)]

theorem rawRowCheck18784 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form0 = rawRow18784 := by decide +kernel

def row18784 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18784 : row18784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18784 := by decide +kernel

theorem rowEval18784 (x : Key → ℝ) : Integer.Sparse.eval row18784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18784, Integer.Sparse.eval_collectBalanced, rawRowCheck18784]

def rawRow18785 : Integer.Sparse Key := [(key2560, 6), (key2530, 6), (key2528, 6), (key2530, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2560, 6), (key2530, 6), (key2519, 6), (key2363, 6), (key2452, 6), (key2357, 6), (key2530, 6), (key2458, 6), (key2363, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2361, 6)]

theorem rawRowCheck18785 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form0 = rawRow18785 := by decide +kernel

def row18785 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18785 : row18785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18785 := by decide +kernel

theorem rowEval18785 (x : Key → ℝ) : Integer.Sparse.eval row18785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18785, Integer.Sparse.eval_collectBalanced, rawRowCheck18785]

def rawRow18786 : Integer.Sparse Key := [(key2530, 6), (key2530, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2363, 6), (key2458, 6), (key2458, 6), (key2519, 6), (key2519, 6), (key2357, 6), (key2452, 6), (key2452, 6), (key2517, 6), (key2361, 6), (key2456, 6), (key2456, 6)]

theorem rawRowCheck18786 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18786 := by decide +kernel

def row18786 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18786 : row18786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18786 := by decide +kernel

theorem rowEval18786 (x : Key → ℝ) : Integer.Sparse.eval row18786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18786, Integer.Sparse.eval_collectBalanced, rawRowCheck18786]

def rawRow18787 : Integer.Sparse Key := [(key2530, 6), (key2560, 6), (key2530, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2530, 6), (key2458, 6), (key2519, 6), (key2363, 6), (key2519, 6), (key2363, 6), (key2458, 6), (key2452, 6), (key2357, 6), (key2452, 6), (key2517, 6), (key2456, 6), (key2361, 6), (key2456, 6)]

theorem rawRowCheck18787 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18787 := by decide +kernel

def row18787 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18787 : row18787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18787 := by decide +kernel

theorem rowEval18787 (x : Key → ℝ) : Integer.Sparse.eval row18787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18787, Integer.Sparse.eval_collectBalanced, rawRowCheck18787]

def rawRow18788 : Integer.Sparse Key := [(key2560, 6), (key2530, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2530, 6), (key2519, 6), (key2458, 6), (key2519, 6), (key2363, 6), (key2458, 6), (key2363, 6), (key2452, 6), (key2452, 6), (key2357, 6), (key2517, 6), (key2456, 6), (key2456, 6), (key2361, 6)]

theorem rawRowCheck18788 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18788 := by decide +kernel

def row18788 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

theorem rowCheck18788 : row18788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18788 := by decide +kernel

theorem rowEval18788 (x : Key → ℝ) : Integer.Sparse.eval row18788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18788, Integer.Sparse.eval_collectBalanced, rawRowCheck18788]

def rawRow18789 : Integer.Sparse Key := [(key974, 24), (key1088, 24), (key1088, 24), (key1178, 24), (key1178, 24)]

theorem rawRowCheck18789 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form1 = rawRow18789 := by decide +kernel

def row18789 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18789 : row18789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18789 := by decide +kernel

theorem rowEval18789 (x : Key → ℝ) : Integer.Sparse.eval row18789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18789, Integer.Sparse.eval_collectBalanced, rawRowCheck18789]

def rawRow18790 : Integer.Sparse Key := [(key974, 24), (key1088, 24), (key1178, 24), (key1088, 24), (key1178, 24)]

theorem rawRowCheck18790 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form1 = rawRow18790 := by decide +kernel

def row18790 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18790 : row18790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18790 := by decide +kernel

theorem rowEval18790 (x : Key → ℝ) : Integer.Sparse.eval row18790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18790, Integer.Sparse.eval_collectBalanced, rawRowCheck18790]

def rawRow18791 : Integer.Sparse Key := [(key974, 24), (key1088, 24), (key1178, 24), (key1178, 24), (key1088, 24)]

theorem rawRowCheck18791 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form1 = rawRow18791 := by decide +kernel

def row18791 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18791 : row18791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18791 := by decide +kernel

theorem rowEval18791 (x : Key → ℝ) : Integer.Sparse.eval row18791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18791, Integer.Sparse.eval_collectBalanced, rawRowCheck18791]

def rawRow18792 : Integer.Sparse Key := [(key974, 24), (key1178, 24), (key1088, 24), (key1088, 24), (key1178, 24)]

theorem rawRowCheck18792 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18792 := by decide +kernel

def row18792 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18792 : row18792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18792 := by decide +kernel

theorem rowEval18792 (x : Key → ℝ) : Integer.Sparse.eval row18792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18792, Integer.Sparse.eval_collectBalanced, rawRowCheck18792]

def rawRow18793 : Integer.Sparse Key := [(key974, 24), (key1178, 24), (key1088, 24), (key1178, 24), (key1088, 24)]

theorem rawRowCheck18793 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18793 := by decide +kernel

def row18793 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18793 : row18793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18793 := by decide +kernel

theorem rowEval18793 (x : Key → ℝ) : Integer.Sparse.eval row18793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18793, Integer.Sparse.eval_collectBalanced, rawRowCheck18793]

def rawRow18794 : Integer.Sparse Key := [(key974, 24), (key1178, 24), (key1178, 24), (key1088, 24), (key1088, 24)]

theorem rawRowCheck18794 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18794 := by decide +kernel

def row18794 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18794 : row18794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18794 := by decide +kernel

theorem rowEval18794 (x : Key → ℝ) : Integer.Sparse.eval row18794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18794, Integer.Sparse.eval_collectBalanced, rawRowCheck18794]

def rawRow18795 : Integer.Sparse Key := [(key1088, 24), (key974, 24), (key1088, 24), (key1178, 24), (key1178, 24)]

theorem rawRowCheck18795 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form1 = rawRow18795 := by decide +kernel

def row18795 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18795 : row18795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18795 := by decide +kernel

theorem rowEval18795 (x : Key → ℝ) : Integer.Sparse.eval row18795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18795, Integer.Sparse.eval_collectBalanced, rawRowCheck18795]

def rawRow18796 : Integer.Sparse Key := [(key1088, 24), (key974, 24), (key1178, 24), (key1088, 24), (key1178, 24)]

theorem rawRowCheck18796 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form1 = rawRow18796 := by decide +kernel

def row18796 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18796 : row18796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18796 := by decide +kernel

theorem rowEval18796 (x : Key → ℝ) : Integer.Sparse.eval row18796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18796, Integer.Sparse.eval_collectBalanced, rawRowCheck18796]

def rawRow18797 : Integer.Sparse Key := [(key1088, 24), (key974, 24), (key1178, 24), (key1178, 24), (key1088, 24)]

theorem rawRowCheck18797 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form1 = rawRow18797 := by decide +kernel

def row18797 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18797 : row18797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18797 := by decide +kernel

theorem rowEval18797 (x : Key → ℝ) : Integer.Sparse.eval row18797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18797, Integer.Sparse.eval_collectBalanced, rawRowCheck18797]

def rawRow18798 : Integer.Sparse Key := [(key1088, 24), (key1088, 24), (key974, 24), (key1178, 24), (key1178, 24)]

theorem rawRowCheck18798 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form1 = rawRow18798 := by decide +kernel

def row18798 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18798 : row18798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18798 := by decide +kernel

theorem rowEval18798 (x : Key → ℝ) : Integer.Sparse.eval row18798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18798, Integer.Sparse.eval_collectBalanced, rawRowCheck18798]

def rawRow18799 : Integer.Sparse Key := [(key1088, 24), (key1088, 24), (key1178, 24), (key974, 24), (key1178, 24)]

theorem rawRowCheck18799 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form1 = rawRow18799 := by decide +kernel

def row18799 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18799 : row18799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18799 := by decide +kernel

theorem rowEval18799 (x : Key → ℝ) : Integer.Sparse.eval row18799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18799, Integer.Sparse.eval_collectBalanced, rawRowCheck18799]

def rawRow18800 : Integer.Sparse Key := [(key1088, 24), (key1088, 24), (key1178, 24), (key1178, 24), (key974, 24)]

theorem rawRowCheck18800 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form1 = rawRow18800 := by decide +kernel

def row18800 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18800 : row18800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18800 := by decide +kernel

theorem rowEval18800 (x : Key → ℝ) : Integer.Sparse.eval row18800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18800, Integer.Sparse.eval_collectBalanced, rawRowCheck18800]

def rawRow18801 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key974, 24), (key1088, 24), (key1178, 24)]

theorem rawRowCheck18801 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form1 = rawRow18801 := by decide +kernel

def row18801 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18801 : row18801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18801 := by decide +kernel

theorem rowEval18801 (x : Key → ℝ) : Integer.Sparse.eval row18801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18801, Integer.Sparse.eval_collectBalanced, rawRowCheck18801]

def rawRow18802 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key974, 24), (key1178, 24), (key1088, 24)]

theorem rawRowCheck18802 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form1 = rawRow18802 := by decide +kernel

def row18802 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18802 : row18802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18802 := by decide +kernel

theorem rowEval18802 (x : Key → ℝ) : Integer.Sparse.eval row18802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18802, Integer.Sparse.eval_collectBalanced, rawRowCheck18802]

def rawRow18803 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1088, 24), (key974, 24), (key1178, 24)]

theorem rawRowCheck18803 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form1 = rawRow18803 := by decide +kernel

def row18803 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18803 : row18803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18803 := by decide +kernel

theorem rowEval18803 (x : Key → ℝ) : Integer.Sparse.eval row18803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18803, Integer.Sparse.eval_collectBalanced, rawRowCheck18803]

def rawRow18804 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1088, 24), (key1178, 24), (key974, 24)]

theorem rawRowCheck18804 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form1 = rawRow18804 := by decide +kernel

def row18804 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18804 : row18804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18804 := by decide +kernel

theorem rowEval18804 (x : Key → ℝ) : Integer.Sparse.eval row18804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18804, Integer.Sparse.eval_collectBalanced, rawRowCheck18804]

def rawRow18805 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1178, 24), (key974, 24), (key1088, 24)]

theorem rawRowCheck18805 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form1 = rawRow18805 := by decide +kernel

def row18805 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18805 : row18805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18805 := by decide +kernel

theorem rowEval18805 (x : Key → ℝ) : Integer.Sparse.eval row18805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18805, Integer.Sparse.eval_collectBalanced, rawRowCheck18805]

def rawRow18806 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1178, 24), (key1088, 24), (key974, 24)]

theorem rawRowCheck18806 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form1 = rawRow18806 := by decide +kernel

def row18806 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18806 : row18806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18806 := by decide +kernel

theorem rowEval18806 (x : Key → ℝ) : Integer.Sparse.eval row18806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18806, Integer.Sparse.eval_collectBalanced, rawRowCheck18806]

def rawRow18807 : Integer.Sparse Key := [(key1178, 24), (key974, 24), (key1088, 24), (key1088, 24), (key1178, 24)]

theorem rawRowCheck18807 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18807 := by decide +kernel

def row18807 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18807 : row18807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18807 := by decide +kernel

theorem rowEval18807 (x : Key → ℝ) : Integer.Sparse.eval row18807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18807, Integer.Sparse.eval_collectBalanced, rawRowCheck18807]

def rawRow18808 : Integer.Sparse Key := [(key1178, 24), (key974, 24), (key1088, 24), (key1178, 24), (key1088, 24)]

theorem rawRowCheck18808 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18808 := by decide +kernel

def row18808 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18808 : row18808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18808 := by decide +kernel

theorem rowEval18808 (x : Key → ℝ) : Integer.Sparse.eval row18808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18808, Integer.Sparse.eval_collectBalanced, rawRowCheck18808]

def rawRow18809 : Integer.Sparse Key := [(key1178, 24), (key974, 24), (key1178, 24), (key1088, 24), (key1088, 24)]

theorem rawRowCheck18809 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18809 := by decide +kernel

def row18809 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18809 : row18809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18809 := by decide +kernel

theorem rowEval18809 (x : Key → ℝ) : Integer.Sparse.eval row18809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18809, Integer.Sparse.eval_collectBalanced, rawRowCheck18809]

def rawRow18810 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key974, 24), (key1088, 24), (key1178, 24)]

theorem rawRowCheck18810 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form1 = rawRow18810 := by decide +kernel

def row18810 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18810 : row18810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18810 := by decide +kernel

theorem rowEval18810 (x : Key → ℝ) : Integer.Sparse.eval row18810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18810, Integer.Sparse.eval_collectBalanced, rawRowCheck18810]

def rawRow18811 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key974, 24), (key1178, 24), (key1088, 24)]

theorem rawRowCheck18811 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form1 = rawRow18811 := by decide +kernel

def row18811 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18811 : row18811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18811 := by decide +kernel

theorem rowEval18811 (x : Key → ℝ) : Integer.Sparse.eval row18811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18811, Integer.Sparse.eval_collectBalanced, rawRowCheck18811]

def rawRow18812 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1088, 24), (key974, 24), (key1178, 24)]

theorem rawRowCheck18812 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form1 = rawRow18812 := by decide +kernel

def row18812 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18812 : row18812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18812 := by decide +kernel

theorem rowEval18812 (x : Key → ℝ) : Integer.Sparse.eval row18812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18812, Integer.Sparse.eval_collectBalanced, rawRowCheck18812]

def rawRow18813 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1088, 24), (key1178, 24), (key974, 24)]

theorem rawRowCheck18813 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form1 = rawRow18813 := by decide +kernel

def row18813 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18813 : row18813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18813 := by decide +kernel

theorem rowEval18813 (x : Key → ℝ) : Integer.Sparse.eval row18813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18813, Integer.Sparse.eval_collectBalanced, rawRowCheck18813]

def rawRow18814 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1178, 24), (key974, 24), (key1088, 24)]

theorem rawRowCheck18814 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form1 = rawRow18814 := by decide +kernel

def row18814 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18814 : row18814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18814 := by decide +kernel

theorem rowEval18814 (x : Key → ℝ) : Integer.Sparse.eval row18814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18814, Integer.Sparse.eval_collectBalanced, rawRowCheck18814]

def rawRow18815 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1178, 24), (key1088, 24), (key974, 24)]

theorem rawRowCheck18815 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form1 = rawRow18815 := by decide +kernel

def row18815 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

theorem rowCheck18815 : row18815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18815 := by decide +kernel

theorem rowEval18815 (x : Key → ℝ) : Integer.Sparse.eval row18815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18815, Integer.Sparse.eval_collectBalanced, rawRowCheck18815]

end MUB6.Certificate.GramRows

end OAI

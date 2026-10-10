import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12800 : Integer.Sparse Key := [(key558, -6), (key297, -6), (key525, -6), (key525, -6), (key372, 2), (key545, 2), (key545, 2), (key297, 2), (key525, 2), (key525, 2), (key286, 2), (key286, 2), (key355, 2), (key355, 2), (key512, 2), (key512, 2)]

theorem rawRowCheck12800 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form10 = rawRow12800 := by decide +kernel

def row12800 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12800 : row12800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12800 := by decide +kernel

theorem rowEval12800 (x : Key → ℝ) : Integer.Sparse.eval row12800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12800, Integer.Sparse.eval_collectBalanced, rawRowCheck12800]

def rawRow12801 : Integer.Sparse Key := [(key558, -6), (key525, -6), (key297, -6), (key525, -6), (key545, 2), (key372, 2), (key545, 2), (key525, 2), (key297, 2), (key525, 2), (key355, 2), (key512, 2), (key286, 2), (key512, 2), (key286, 2), (key355, 2)]

theorem rawRowCheck12801 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form10 = rawRow12801 := by decide +kernel

def row12801 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12801 : row12801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12801 := by decide +kernel

theorem rowEval12801 (x : Key → ℝ) : Integer.Sparse.eval row12801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12801, Integer.Sparse.eval_collectBalanced, rawRowCheck12801]

def rawRow12802 : Integer.Sparse Key := [(key558, -6), (key525, -6), (key525, -6), (key297, -6), (key545, 2), (key545, 2), (key372, 2), (key525, 2), (key525, 2), (key297, 2), (key512, 2), (key355, 2), (key512, 2), (key286, 2), (key355, 2), (key286, 2)]

theorem rawRowCheck12802 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form10 = rawRow12802 := by decide +kernel

def row12802 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

theorem rowCheck12802 : row12802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12802 := by decide +kernel

theorem rowEval12802 (x : Key → ℝ) : Integer.Sparse.eval row12802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck12802, Integer.Sparse.eval_collectBalanced, rawRowCheck12802]

def rawRow12803 : Integer.Sparse Key := [(key1704, 6), (key1704, 6), (key1708, 6), (key1857, 6), (key1285, -6), (key1708, -6), (key1758, -6), (key1758, -6)]

theorem rawRowCheck12803 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form11 = rawRow12803 := by decide +kernel

def row12803 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12803 : row12803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12803 := by decide +kernel

theorem rowEval12803 (x : Key → ℝ) : Integer.Sparse.eval row12803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12803, Integer.Sparse.eval_collectBalanced, rawRowCheck12803]

def rawRow12804 : Integer.Sparse Key := [(key1704, 6), (key1708, 6), (key1704, 6), (key1857, 6), (key1285, -6), (key1758, -6), (key1708, -6), (key1758, -6)]

theorem rawRowCheck12804 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form11 = rawRow12804 := by decide +kernel

def row12804 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12804 : row12804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12804 := by decide +kernel

theorem rowEval12804 (x : Key → ℝ) : Integer.Sparse.eval row12804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12804, Integer.Sparse.eval_collectBalanced, rawRowCheck12804]

def rawRow12805 : Integer.Sparse Key := [(key1708, 6), (key1704, 6), (key1704, 6), (key1857, 6), (key1285, -6), (key1758, -6), (key1758, -6), (key1708, -6)]

theorem rawRowCheck12805 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form11 = rawRow12805 := by decide +kernel

def row12805 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12805 : row12805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12805 := by decide +kernel

theorem rowEval12805 (x : Key → ℝ) : Integer.Sparse.eval row12805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12805, Integer.Sparse.eval_collectBalanced, rawRowCheck12805]

def rawRow12806 : Integer.Sparse Key := [(key1704, 6), (key1704, 6), (key1857, 6), (key1708, 6), (key1708, -6), (key1285, -6), (key1758, -6), (key1758, -6)]

theorem rawRowCheck12806 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form11 = rawRow12806 := by decide +kernel

def row12806 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12806 : row12806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12806 := by decide +kernel

theorem rowEval12806 (x : Key → ℝ) : Integer.Sparse.eval row12806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12806, Integer.Sparse.eval_collectBalanced, rawRowCheck12806]

def rawRow12807 : Integer.Sparse Key := [(key1704, 6), (key1857, 6), (key1704, 6), (key1708, 6), (key1708, -6), (key1758, -6), (key1285, -6), (key1758, -6)]

theorem rawRowCheck12807 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form11 = rawRow12807 := by decide +kernel

def row12807 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12807 : row12807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12807 := by decide +kernel

theorem rowEval12807 (x : Key → ℝ) : Integer.Sparse.eval row12807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12807, Integer.Sparse.eval_collectBalanced, rawRowCheck12807]

def rawRow12808 : Integer.Sparse Key := [(key1857, 6), (key1704, 6), (key1704, 6), (key1708, 6), (key1708, -6), (key1758, -6), (key1758, -6), (key1285, -6)]

theorem rawRowCheck12808 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form11 = rawRow12808 := by decide +kernel

def row12808 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12808 : row12808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12808 := by decide +kernel

theorem rowEval12808 (x : Key → ℝ) : Integer.Sparse.eval row12808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12808, Integer.Sparse.eval_collectBalanced, rawRowCheck12808]

def rawRow12809 : Integer.Sparse Key := [(key1704, 6), (key1708, 6), (key1857, 6), (key1704, 6), (key1758, -6), (key1285, -6), (key1708, -6), (key1758, -6)]

theorem rawRowCheck12809 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form11 = rawRow12809 := by decide +kernel

def row12809 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12809 : row12809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12809 := by decide +kernel

theorem rowEval12809 (x : Key → ℝ) : Integer.Sparse.eval row12809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12809, Integer.Sparse.eval_collectBalanced, rawRowCheck12809]

def rawRow12810 : Integer.Sparse Key := [(key1708, 6), (key1704, 6), (key1857, 6), (key1704, 6), (key1758, -6), (key1285, -6), (key1758, -6), (key1708, -6)]

theorem rawRowCheck12810 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form11 = rawRow12810 := by decide +kernel

def row12810 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12810 : row12810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12810 := by decide +kernel

theorem rowEval12810 (x : Key → ℝ) : Integer.Sparse.eval row12810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12810, Integer.Sparse.eval_collectBalanced, rawRowCheck12810]

def rawRow12811 : Integer.Sparse Key := [(key1704, 6), (key1857, 6), (key1708, 6), (key1704, 6), (key1758, -6), (key1708, -6), (key1285, -6), (key1758, -6)]

theorem rawRowCheck12811 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form11 = rawRow12811 := by decide +kernel

def row12811 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12811 : row12811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12811 := by decide +kernel

theorem rowEval12811 (x : Key → ℝ) : Integer.Sparse.eval row12811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12811, Integer.Sparse.eval_collectBalanced, rawRowCheck12811]

def rawRow12812 : Integer.Sparse Key := [(key1857, 6), (key1704, 6), (key1708, 6), (key1704, 6), (key1758, -6), (key1708, -6), (key1758, -6), (key1285, -6)]

theorem rawRowCheck12812 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form11 = rawRow12812 := by decide +kernel

def row12812 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12812 : row12812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12812 := by decide +kernel

theorem rowEval12812 (x : Key → ℝ) : Integer.Sparse.eval row12812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12812, Integer.Sparse.eval_collectBalanced, rawRowCheck12812]

def rawRow12813 : Integer.Sparse Key := [(key1708, 6), (key1857, 6), (key1704, 6), (key1704, 6), (key1758, -6), (key1758, -6), (key1285, -6), (key1708, -6)]

theorem rawRowCheck12813 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form11 = rawRow12813 := by decide +kernel

def row12813 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12813 : row12813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12813 := by decide +kernel

theorem rowEval12813 (x : Key → ℝ) : Integer.Sparse.eval row12813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12813, Integer.Sparse.eval_collectBalanced, rawRowCheck12813]

def rawRow12814 : Integer.Sparse Key := [(key1857, 6), (key1708, 6), (key1704, 6), (key1704, 6), (key1758, -6), (key1758, -6), (key1708, -6), (key1285, -6)]

theorem rawRowCheck12814 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form11 = rawRow12814 := by decide +kernel

def row12814 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

theorem rowCheck12814 : row12814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12814 := by decide +kernel

theorem rowEval12814 (x : Key → ℝ) : Integer.Sparse.eval row12814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12814, Integer.Sparse.eval_collectBalanced, rawRowCheck12814]

def rawRow12815 : Integer.Sparse Key := [(key1753, 6), (key1758, 6), (key1758, 6), (key1888, 6), (key1281, -6), (key1704, -6), (key1704, -6), (key1753, -6)]

theorem rawRowCheck12815 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form11 = rawRow12815 := by decide +kernel

def row12815 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12815 : row12815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12815 := by decide +kernel

theorem rowEval12815 (x : Key → ℝ) : Integer.Sparse.eval row12815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12815, Integer.Sparse.eval_collectBalanced, rawRowCheck12815]

def rawRow12816 : Integer.Sparse Key := [(key1758, 6), (key1753, 6), (key1758, 6), (key1888, 6), (key1281, -6), (key1704, -6), (key1753, -6), (key1704, -6)]

theorem rawRowCheck12816 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form11 = rawRow12816 := by decide +kernel

def row12816 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12816 : row12816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12816 := by decide +kernel

theorem rowEval12816 (x : Key → ℝ) : Integer.Sparse.eval row12816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12816, Integer.Sparse.eval_collectBalanced, rawRowCheck12816]

def rawRow12817 : Integer.Sparse Key := [(key1758, 6), (key1758, 6), (key1753, 6), (key1888, 6), (key1281, -6), (key1753, -6), (key1704, -6), (key1704, -6)]

theorem rawRowCheck12817 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form11 = rawRow12817 := by decide +kernel

def row12817 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12817 : row12817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12817 := by decide +kernel

theorem rowEval12817 (x : Key → ℝ) : Integer.Sparse.eval row12817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12817, Integer.Sparse.eval_collectBalanced, rawRowCheck12817]

def rawRow12818 : Integer.Sparse Key := [(key1753, 6), (key1758, 6), (key1888, 6), (key1758, 6), (key1704, -6), (key1281, -6), (key1704, -6), (key1753, -6)]

theorem rawRowCheck12818 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form11 = rawRow12818 := by decide +kernel

def row12818 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12818 : row12818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12818 := by decide +kernel

theorem rowEval12818 (x : Key → ℝ) : Integer.Sparse.eval row12818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12818, Integer.Sparse.eval_collectBalanced, rawRowCheck12818]

def rawRow12819 : Integer.Sparse Key := [(key1758, 6), (key1753, 6), (key1888, 6), (key1758, 6), (key1704, -6), (key1281, -6), (key1753, -6), (key1704, -6)]

theorem rawRowCheck12819 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form11 = rawRow12819 := by decide +kernel

def row12819 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12819 : row12819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12819 := by decide +kernel

theorem rowEval12819 (x : Key → ℝ) : Integer.Sparse.eval row12819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12819, Integer.Sparse.eval_collectBalanced, rawRowCheck12819]

def rawRow12820 : Integer.Sparse Key := [(key1753, 6), (key1888, 6), (key1758, 6), (key1758, 6), (key1704, -6), (key1704, -6), (key1281, -6), (key1753, -6)]

theorem rawRowCheck12820 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form11 = rawRow12820 := by decide +kernel

def row12820 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12820 : row12820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12820 := by decide +kernel

theorem rowEval12820 (x : Key → ℝ) : Integer.Sparse.eval row12820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12820, Integer.Sparse.eval_collectBalanced, rawRowCheck12820]

def rawRow12821 : Integer.Sparse Key := [(key1888, 6), (key1753, 6), (key1758, 6), (key1758, 6), (key1704, -6), (key1704, -6), (key1753, -6), (key1281, -6)]

theorem rawRowCheck12821 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form11 = rawRow12821 := by decide +kernel

def row12821 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12821 : row12821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12821 := by decide +kernel

theorem rowEval12821 (x : Key → ℝ) : Integer.Sparse.eval row12821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12821, Integer.Sparse.eval_collectBalanced, rawRowCheck12821]

def rawRow12822 : Integer.Sparse Key := [(key1758, 6), (key1888, 6), (key1753, 6), (key1758, 6), (key1704, -6), (key1753, -6), (key1281, -6), (key1704, -6)]

theorem rawRowCheck12822 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form11 = rawRow12822 := by decide +kernel

def row12822 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12822 : row12822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12822 := by decide +kernel

theorem rowEval12822 (x : Key → ℝ) : Integer.Sparse.eval row12822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12822, Integer.Sparse.eval_collectBalanced, rawRowCheck12822]

def rawRow12823 : Integer.Sparse Key := [(key1888, 6), (key1758, 6), (key1753, 6), (key1758, 6), (key1704, -6), (key1753, -6), (key1704, -6), (key1281, -6)]

theorem rawRowCheck12823 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form11 = rawRow12823 := by decide +kernel

def row12823 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12823 : row12823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12823 := by decide +kernel

theorem rowEval12823 (x : Key → ℝ) : Integer.Sparse.eval row12823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12823, Integer.Sparse.eval_collectBalanced, rawRowCheck12823]

def rawRow12824 : Integer.Sparse Key := [(key1758, 6), (key1758, 6), (key1888, 6), (key1753, 6), (key1753, -6), (key1281, -6), (key1704, -6), (key1704, -6)]

theorem rawRowCheck12824 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form11 = rawRow12824 := by decide +kernel

def row12824 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12824 : row12824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12824 := by decide +kernel

theorem rowEval12824 (x : Key → ℝ) : Integer.Sparse.eval row12824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12824, Integer.Sparse.eval_collectBalanced, rawRowCheck12824]

def rawRow12825 : Integer.Sparse Key := [(key1758, 6), (key1888, 6), (key1758, 6), (key1753, 6), (key1753, -6), (key1704, -6), (key1281, -6), (key1704, -6)]

theorem rawRowCheck12825 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form11 = rawRow12825 := by decide +kernel

def row12825 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12825 : row12825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12825 := by decide +kernel

theorem rowEval12825 (x : Key → ℝ) : Integer.Sparse.eval row12825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12825, Integer.Sparse.eval_collectBalanced, rawRowCheck12825]

def rawRow12826 : Integer.Sparse Key := [(key1888, 6), (key1758, 6), (key1758, 6), (key1753, 6), (key1753, -6), (key1704, -6), (key1704, -6), (key1281, -6)]

theorem rawRowCheck12826 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form11 = rawRow12826 := by decide +kernel

def row12826 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

theorem rowCheck12826 : row12826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12826 := by decide +kernel

theorem rowEval12826 (x : Key → ℝ) : Integer.Sparse.eval row12826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12826, Integer.Sparse.eval_collectBalanced, rawRowCheck12826]

def rawRow12827 : Integer.Sparse Key := [(key1702, 6), (key1702, 6), (key1708, 6), (key1935, 6), (key1285, -6), (key1708, -6), (key1758, -6), (key1758, -6)]

theorem rawRowCheck12827 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form12 = rawRow12827 := by decide +kernel

def row12827 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12827 : row12827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12827 := by decide +kernel

theorem rowEval12827 (x : Key → ℝ) : Integer.Sparse.eval row12827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12827, Integer.Sparse.eval_collectBalanced, rawRowCheck12827]

def rawRow12828 : Integer.Sparse Key := [(key1702, 6), (key1708, 6), (key1702, 6), (key1935, 6), (key1285, -6), (key1758, -6), (key1708, -6), (key1758, -6)]

theorem rawRowCheck12828 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form12 = rawRow12828 := by decide +kernel

def row12828 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12828 : row12828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12828 := by decide +kernel

theorem rowEval12828 (x : Key → ℝ) : Integer.Sparse.eval row12828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12828, Integer.Sparse.eval_collectBalanced, rawRowCheck12828]

def rawRow12829 : Integer.Sparse Key := [(key1708, 6), (key1702, 6), (key1702, 6), (key1935, 6), (key1285, -6), (key1758, -6), (key1758, -6), (key1708, -6)]

theorem rawRowCheck12829 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form12 = rawRow12829 := by decide +kernel

def row12829 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12829 : row12829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12829 := by decide +kernel

theorem rowEval12829 (x : Key → ℝ) : Integer.Sparse.eval row12829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12829, Integer.Sparse.eval_collectBalanced, rawRowCheck12829]

def rawRow12830 : Integer.Sparse Key := [(key1702, 6), (key1702, 6), (key1935, 6), (key1708, 6), (key1708, -6), (key1285, -6), (key1758, -6), (key1758, -6)]

theorem rawRowCheck12830 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form12 = rawRow12830 := by decide +kernel

def row12830 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12830 : row12830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12830 := by decide +kernel

theorem rowEval12830 (x : Key → ℝ) : Integer.Sparse.eval row12830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12830, Integer.Sparse.eval_collectBalanced, rawRowCheck12830]

def rawRow12831 : Integer.Sparse Key := [(key1702, 6), (key1935, 6), (key1702, 6), (key1708, 6), (key1708, -6), (key1758, -6), (key1285, -6), (key1758, -6)]

theorem rawRowCheck12831 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form12 = rawRow12831 := by decide +kernel

def row12831 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12831 : row12831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12831 := by decide +kernel

theorem rowEval12831 (x : Key → ℝ) : Integer.Sparse.eval row12831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12831, Integer.Sparse.eval_collectBalanced, rawRowCheck12831]

def rawRow12832 : Integer.Sparse Key := [(key1935, 6), (key1702, 6), (key1702, 6), (key1708, 6), (key1708, -6), (key1758, -6), (key1758, -6), (key1285, -6)]

theorem rawRowCheck12832 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form12 = rawRow12832 := by decide +kernel

def row12832 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12832 : row12832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12832 := by decide +kernel

theorem rowEval12832 (x : Key → ℝ) : Integer.Sparse.eval row12832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12832, Integer.Sparse.eval_collectBalanced, rawRowCheck12832]

def rawRow12833 : Integer.Sparse Key := [(key1702, 6), (key1708, 6), (key1935, 6), (key1702, 6), (key1758, -6), (key1285, -6), (key1708, -6), (key1758, -6)]

theorem rawRowCheck12833 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form12 = rawRow12833 := by decide +kernel

def row12833 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12833 : row12833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12833 := by decide +kernel

theorem rowEval12833 (x : Key → ℝ) : Integer.Sparse.eval row12833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12833, Integer.Sparse.eval_collectBalanced, rawRowCheck12833]

def rawRow12834 : Integer.Sparse Key := [(key1708, 6), (key1702, 6), (key1935, 6), (key1702, 6), (key1758, -6), (key1285, -6), (key1758, -6), (key1708, -6)]

theorem rawRowCheck12834 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form12 = rawRow12834 := by decide +kernel

def row12834 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12834 : row12834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12834 := by decide +kernel

theorem rowEval12834 (x : Key → ℝ) : Integer.Sparse.eval row12834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12834, Integer.Sparse.eval_collectBalanced, rawRowCheck12834]

def rawRow12835 : Integer.Sparse Key := [(key1702, 6), (key1935, 6), (key1708, 6), (key1702, 6), (key1758, -6), (key1708, -6), (key1285, -6), (key1758, -6)]

theorem rawRowCheck12835 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form12 = rawRow12835 := by decide +kernel

def row12835 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12835 : row12835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12835 := by decide +kernel

theorem rowEval12835 (x : Key → ℝ) : Integer.Sparse.eval row12835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12835, Integer.Sparse.eval_collectBalanced, rawRowCheck12835]

def rawRow12836 : Integer.Sparse Key := [(key1935, 6), (key1702, 6), (key1708, 6), (key1702, 6), (key1758, -6), (key1708, -6), (key1758, -6), (key1285, -6)]

theorem rawRowCheck12836 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form12 = rawRow12836 := by decide +kernel

def row12836 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12836 : row12836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12836 := by decide +kernel

theorem rowEval12836 (x : Key → ℝ) : Integer.Sparse.eval row12836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12836, Integer.Sparse.eval_collectBalanced, rawRowCheck12836]

def rawRow12837 : Integer.Sparse Key := [(key1708, 6), (key1935, 6), (key1702, 6), (key1702, 6), (key1758, -6), (key1758, -6), (key1285, -6), (key1708, -6)]

theorem rawRowCheck12837 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form12 = rawRow12837 := by decide +kernel

def row12837 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12837 : row12837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12837 := by decide +kernel

theorem rowEval12837 (x : Key → ℝ) : Integer.Sparse.eval row12837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12837, Integer.Sparse.eval_collectBalanced, rawRowCheck12837]

def rawRow12838 : Integer.Sparse Key := [(key1935, 6), (key1708, 6), (key1702, 6), (key1702, 6), (key1758, -6), (key1758, -6), (key1708, -6), (key1285, -6)]

theorem rawRowCheck12838 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form12 = rawRow12838 := by decide +kernel

def row12838 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

theorem rowCheck12838 : row12838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12838 := by decide +kernel

theorem rowEval12838 (x : Key → ℝ) : Integer.Sparse.eval row12838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12838, Integer.Sparse.eval_collectBalanced, rawRowCheck12838]

def rawRow12839 : Integer.Sparse Key := [(key1752, 6), (key1758, 6), (key1758, 6), (key1955, 6), (key1279, -6), (key1702, -6), (key1702, -6), (key1752, -6)]

theorem rawRowCheck12839 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form12 = rawRow12839 := by decide +kernel

def row12839 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12839 : row12839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12839 := by decide +kernel

theorem rowEval12839 (x : Key → ℝ) : Integer.Sparse.eval row12839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12839, Integer.Sparse.eval_collectBalanced, rawRowCheck12839]

def rawRow12840 : Integer.Sparse Key := [(key1758, 6), (key1752, 6), (key1758, 6), (key1955, 6), (key1279, -6), (key1702, -6), (key1752, -6), (key1702, -6)]

theorem rawRowCheck12840 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form12 = rawRow12840 := by decide +kernel

def row12840 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12840 : row12840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12840 := by decide +kernel

theorem rowEval12840 (x : Key → ℝ) : Integer.Sparse.eval row12840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12840, Integer.Sparse.eval_collectBalanced, rawRowCheck12840]

def rawRow12841 : Integer.Sparse Key := [(key1758, 6), (key1758, 6), (key1752, 6), (key1955, 6), (key1279, -6), (key1752, -6), (key1702, -6), (key1702, -6)]

theorem rawRowCheck12841 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form12 = rawRow12841 := by decide +kernel

def row12841 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12841 : row12841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12841 := by decide +kernel

theorem rowEval12841 (x : Key → ℝ) : Integer.Sparse.eval row12841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12841, Integer.Sparse.eval_collectBalanced, rawRowCheck12841]

def rawRow12842 : Integer.Sparse Key := [(key1752, 6), (key1758, 6), (key1955, 6), (key1758, 6), (key1702, -6), (key1279, -6), (key1702, -6), (key1752, -6)]

theorem rawRowCheck12842 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form12 = rawRow12842 := by decide +kernel

def row12842 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12842 : row12842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12842 := by decide +kernel

theorem rowEval12842 (x : Key → ℝ) : Integer.Sparse.eval row12842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12842, Integer.Sparse.eval_collectBalanced, rawRowCheck12842]

def rawRow12843 : Integer.Sparse Key := [(key1758, 6), (key1752, 6), (key1955, 6), (key1758, 6), (key1702, -6), (key1279, -6), (key1752, -6), (key1702, -6)]

theorem rawRowCheck12843 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form12 = rawRow12843 := by decide +kernel

def row12843 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12843 : row12843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12843 := by decide +kernel

theorem rowEval12843 (x : Key → ℝ) : Integer.Sparse.eval row12843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12843, Integer.Sparse.eval_collectBalanced, rawRowCheck12843]

def rawRow12844 : Integer.Sparse Key := [(key1752, 6), (key1955, 6), (key1758, 6), (key1758, 6), (key1702, -6), (key1702, -6), (key1279, -6), (key1752, -6)]

theorem rawRowCheck12844 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form12 = rawRow12844 := by decide +kernel

def row12844 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12844 : row12844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12844 := by decide +kernel

theorem rowEval12844 (x : Key → ℝ) : Integer.Sparse.eval row12844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12844, Integer.Sparse.eval_collectBalanced, rawRowCheck12844]

def rawRow12845 : Integer.Sparse Key := [(key1955, 6), (key1752, 6), (key1758, 6), (key1758, 6), (key1702, -6), (key1702, -6), (key1752, -6), (key1279, -6)]

theorem rawRowCheck12845 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form12 = rawRow12845 := by decide +kernel

def row12845 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12845 : row12845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12845 := by decide +kernel

theorem rowEval12845 (x : Key → ℝ) : Integer.Sparse.eval row12845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12845, Integer.Sparse.eval_collectBalanced, rawRowCheck12845]

def rawRow12846 : Integer.Sparse Key := [(key1758, 6), (key1955, 6), (key1752, 6), (key1758, 6), (key1702, -6), (key1752, -6), (key1279, -6), (key1702, -6)]

theorem rawRowCheck12846 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form12 = rawRow12846 := by decide +kernel

def row12846 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12846 : row12846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12846 := by decide +kernel

theorem rowEval12846 (x : Key → ℝ) : Integer.Sparse.eval row12846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12846, Integer.Sparse.eval_collectBalanced, rawRowCheck12846]

def rawRow12847 : Integer.Sparse Key := [(key1955, 6), (key1758, 6), (key1752, 6), (key1758, 6), (key1702, -6), (key1752, -6), (key1702, -6), (key1279, -6)]

theorem rawRowCheck12847 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form12 = rawRow12847 := by decide +kernel

def row12847 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12847 : row12847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12847 := by decide +kernel

theorem rowEval12847 (x : Key → ℝ) : Integer.Sparse.eval row12847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12847, Integer.Sparse.eval_collectBalanced, rawRowCheck12847]

def rawRow12848 : Integer.Sparse Key := [(key1758, 6), (key1758, 6), (key1955, 6), (key1752, 6), (key1752, -6), (key1279, -6), (key1702, -6), (key1702, -6)]

theorem rawRowCheck12848 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form12 = rawRow12848 := by decide +kernel

def row12848 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12848 : row12848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12848 := by decide +kernel

theorem rowEval12848 (x : Key → ℝ) : Integer.Sparse.eval row12848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12848, Integer.Sparse.eval_collectBalanced, rawRowCheck12848]

def rawRow12849 : Integer.Sparse Key := [(key1758, 6), (key1955, 6), (key1758, 6), (key1752, 6), (key1752, -6), (key1702, -6), (key1279, -6), (key1702, -6)]

theorem rawRowCheck12849 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form12 = rawRow12849 := by decide +kernel

def row12849 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12849 : row12849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12849 := by decide +kernel

theorem rowEval12849 (x : Key → ℝ) : Integer.Sparse.eval row12849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12849, Integer.Sparse.eval_collectBalanced, rawRowCheck12849]

def rawRow12850 : Integer.Sparse Key := [(key1955, 6), (key1758, 6), (key1758, 6), (key1752, 6), (key1752, -6), (key1702, -6), (key1702, -6), (key1279, -6)]

theorem rawRowCheck12850 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form12 = rawRow12850 := by decide +kernel

def row12850 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

theorem rowCheck12850 : row12850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12850 := by decide +kernel

theorem rowEval12850 (x : Key → ℝ) : Integer.Sparse.eval row12850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12850, Integer.Sparse.eval_collectBalanced, rawRowCheck12850]

def rawRow12851 : Integer.Sparse Key := [(key866, -6), (key866, -6), (key868, -6), (key882, -6), (key732, 2), (key732, 2), (key734, 2), (key866, 2), (key866, 2), (key900, 2), (key900, 2), (key901, 2), (key901, 2), (key882, 2), (key913, 2), (key913, 2)]

theorem rawRowCheck12851 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form13 = rawRow12851 := by decide +kernel

def row12851 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12851 : row12851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12851 := by decide +kernel

theorem rowEval12851 (x : Key → ℝ) : Integer.Sparse.eval row12851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12851, Integer.Sparse.eval_collectBalanced, rawRowCheck12851]

def rawRow12852 : Integer.Sparse Key := [(key866, -6), (key868, -6), (key866, -6), (key882, -6), (key732, 2), (key734, 2), (key732, 2), (key900, 2), (key901, 2), (key866, 2), (key901, 2), (key866, 2), (key900, 2), (key913, 2), (key882, 2), (key913, 2)]

theorem rawRowCheck12852 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form13 = rawRow12852 := by decide +kernel

def row12852 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12852 : row12852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12852 := by decide +kernel

theorem rowEval12852 (x : Key → ℝ) : Integer.Sparse.eval row12852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12852, Integer.Sparse.eval_collectBalanced, rawRowCheck12852]

def rawRow12853 : Integer.Sparse Key := [(key868, -6), (key866, -6), (key866, -6), (key882, -6), (key734, 2), (key732, 2), (key732, 2), (key901, 2), (key900, 2), (key901, 2), (key866, 2), (key900, 2), (key866, 2), (key913, 2), (key913, 2), (key882, 2)]

theorem rawRowCheck12853 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form13 = rawRow12853 := by decide +kernel

def row12853 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12853 : row12853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12853 := by decide +kernel

theorem rowEval12853 (x : Key → ℝ) : Integer.Sparse.eval row12853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12853, Integer.Sparse.eval_collectBalanced, rawRowCheck12853]

def rawRow12854 : Integer.Sparse Key := [(key866, -6), (key866, -6), (key882, -6), (key868, -6), (key866, 2), (key866, 2), (key882, 2), (key732, 2), (key732, 2), (key900, 2), (key900, 2), (key913, 2), (key913, 2), (key734, 2), (key901, 2), (key901, 2)]

theorem rawRowCheck12854 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form13 = rawRow12854 := by decide +kernel

def row12854 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12854 : row12854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12854 := by decide +kernel

theorem rowEval12854 (x : Key → ℝ) : Integer.Sparse.eval row12854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12854, Integer.Sparse.eval_collectBalanced, rawRowCheck12854]

def rawRow12855 : Integer.Sparse Key := [(key866, -6), (key882, -6), (key866, -6), (key868, -6), (key866, 2), (key882, 2), (key866, 2), (key900, 2), (key913, 2), (key732, 2), (key913, 2), (key732, 2), (key900, 2), (key901, 2), (key734, 2), (key901, 2)]

theorem rawRowCheck12855 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form13 = rawRow12855 := by decide +kernel

def row12855 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12855 : row12855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12855 := by decide +kernel

theorem rowEval12855 (x : Key → ℝ) : Integer.Sparse.eval row12855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12855, Integer.Sparse.eval_collectBalanced, rawRowCheck12855]

def rawRow12856 : Integer.Sparse Key := [(key882, -6), (key866, -6), (key866, -6), (key868, -6), (key882, 2), (key866, 2), (key866, 2), (key913, 2), (key900, 2), (key913, 2), (key732, 2), (key900, 2), (key732, 2), (key901, 2), (key901, 2), (key734, 2)]

theorem rawRowCheck12856 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form13 = rawRow12856 := by decide +kernel

def row12856 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12856 : row12856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12856 := by decide +kernel

theorem rowEval12856 (x : Key → ℝ) : Integer.Sparse.eval row12856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12856, Integer.Sparse.eval_collectBalanced, rawRowCheck12856]

def rawRow12857 : Integer.Sparse Key := [(key866, -6), (key868, -6), (key882, -6), (key866, -6), (key900, 2), (key901, 2), (key913, 2), (key732, 2), (key734, 2), (key866, 2), (key901, 2), (key882, 2), (key913, 2), (key732, 2), (key866, 2), (key900, 2)]

theorem rawRowCheck12857 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form13 = rawRow12857 := by decide +kernel

def row12857 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12857 : row12857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12857 := by decide +kernel

theorem rowEval12857 (x : Key → ℝ) : Integer.Sparse.eval row12857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12857, Integer.Sparse.eval_collectBalanced, rawRowCheck12857]

def rawRow12858 : Integer.Sparse Key := [(key868, -6), (key866, -6), (key882, -6), (key866, -6), (key901, 2), (key900, 2), (key913, 2), (key734, 2), (key732, 2), (key901, 2), (key866, 2), (key913, 2), (key882, 2), (key732, 2), (key900, 2), (key866, 2)]

theorem rawRowCheck12858 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form13 = rawRow12858 := by decide +kernel

def row12858 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12858 : row12858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12858 := by decide +kernel

theorem rowEval12858 (x : Key → ℝ) : Integer.Sparse.eval row12858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12858, Integer.Sparse.eval_collectBalanced, rawRowCheck12858]

def rawRow12859 : Integer.Sparse Key := [(key866, -6), (key882, -6), (key868, -6), (key866, -6), (key900, 2), (key913, 2), (key901, 2), (key866, 2), (key882, 2), (key732, 2), (key913, 2), (key734, 2), (key901, 2), (key866, 2), (key732, 2), (key900, 2)]

theorem rawRowCheck12859 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form13 = rawRow12859 := by decide +kernel

def row12859 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12859 : row12859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12859 := by decide +kernel

theorem rowEval12859 (x : Key → ℝ) : Integer.Sparse.eval row12859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12859, Integer.Sparse.eval_collectBalanced, rawRowCheck12859]

def rawRow12860 : Integer.Sparse Key := [(key882, -6), (key866, -6), (key868, -6), (key866, -6), (key913, 2), (key900, 2), (key901, 2), (key882, 2), (key866, 2), (key913, 2), (key732, 2), (key901, 2), (key734, 2), (key866, 2), (key900, 2), (key732, 2)]

theorem rawRowCheck12860 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form13 = rawRow12860 := by decide +kernel

def row12860 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12860 : row12860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12860 := by decide +kernel

theorem rowEval12860 (x : Key → ℝ) : Integer.Sparse.eval row12860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12860, Integer.Sparse.eval_collectBalanced, rawRowCheck12860]

def rawRow12861 : Integer.Sparse Key := [(key868, -6), (key882, -6), (key866, -6), (key866, -6), (key901, 2), (key913, 2), (key900, 2), (key901, 2), (key913, 2), (key734, 2), (key882, 2), (key732, 2), (key866, 2), (key900, 2), (key732, 2), (key866, 2)]

theorem rawRowCheck12861 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form13 = rawRow12861 := by decide +kernel

def row12861 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12861 : row12861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12861 := by decide +kernel

theorem rowEval12861 (x : Key → ℝ) : Integer.Sparse.eval row12861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12861, Integer.Sparse.eval_collectBalanced, rawRowCheck12861]

def rawRow12862 : Integer.Sparse Key := [(key882, -6), (key868, -6), (key866, -6), (key866, -6), (key913, 2), (key901, 2), (key900, 2), (key913, 2), (key901, 2), (key882, 2), (key734, 2), (key866, 2), (key732, 2), (key900, 2), (key866, 2), (key732, 2)]

theorem rawRowCheck12862 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form13 = rawRow12862 := by decide +kernel

def row12862 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

theorem rowCheck12862 : row12862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12862 := by decide +kernel

theorem rowEval12862 (x : Key → ℝ) : Integer.Sparse.eval row12862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12862, Integer.Sparse.eval_collectBalanced, rawRowCheck12862]

def rawRow12863 : Integer.Sparse Key := [(key900, -6), (key901, -6), (key901, -6), (key913, -6), (key732, 2), (key734, 2), (key734, 2), (key866, 2), (key868, 2), (key866, 2), (key901, 2), (key868, 2), (key901, 2), (key882, 2), (key882, 2), (key913, 2)]

theorem rawRowCheck12863 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form13 = rawRow12863 := by decide +kernel

def row12863 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12863 : row12863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12863 := by decide +kernel

theorem rowEval12863 (x : Key → ℝ) : Integer.Sparse.eval row12863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12863, Integer.Sparse.eval_collectBalanced, rawRowCheck12863]

def rawRow12864 : Integer.Sparse Key := [(key901, -6), (key900, -6), (key901, -6), (key913, -6), (key734, 2), (key732, 2), (key734, 2), (key868, 2), (key866, 2), (key901, 2), (key866, 2), (key901, 2), (key868, 2), (key882, 2), (key913, 2), (key882, 2)]

theorem rawRowCheck12864 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form13 = rawRow12864 := by decide +kernel

def row12864 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12864 : row12864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12864 := by decide +kernel

theorem rowEval12864 (x : Key → ℝ) : Integer.Sparse.eval row12864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12864, Integer.Sparse.eval_collectBalanced, rawRowCheck12864]

def rawRow12865 : Integer.Sparse Key := [(key901, -6), (key901, -6), (key900, -6), (key913, -6), (key734, 2), (key734, 2), (key732, 2), (key901, 2), (key901, 2), (key868, 2), (key868, 2), (key866, 2), (key866, 2), (key913, 2), (key882, 2), (key882, 2)]

theorem rawRowCheck12865 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form13 = rawRow12865 := by decide +kernel

def row12865 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12865 : row12865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12865 := by decide +kernel

theorem rowEval12865 (x : Key → ℝ) : Integer.Sparse.eval row12865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12865, Integer.Sparse.eval_collectBalanced, rawRowCheck12865]

def rawRow12866 : Integer.Sparse Key := [(key900, -6), (key901, -6), (key913, -6), (key901, -6), (key866, 2), (key868, 2), (key882, 2), (key732, 2), (key734, 2), (key866, 2), (key901, 2), (key882, 2), (key913, 2), (key734, 2), (key868, 2), (key901, 2)]

theorem rawRowCheck12866 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form13 = rawRow12866 := by decide +kernel

def row12866 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12866 : row12866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12866 := by decide +kernel

theorem rowEval12866 (x : Key → ℝ) : Integer.Sparse.eval row12866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12866, Integer.Sparse.eval_collectBalanced, rawRowCheck12866]

def rawRow12867 : Integer.Sparse Key := [(key901, -6), (key900, -6), (key913, -6), (key901, -6), (key868, 2), (key866, 2), (key882, 2), (key734, 2), (key732, 2), (key901, 2), (key866, 2), (key913, 2), (key882, 2), (key734, 2), (key901, 2), (key868, 2)]

theorem rawRowCheck12867 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form13 = rawRow12867 := by decide +kernel

def row12867 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12867 : row12867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12867 := by decide +kernel

theorem rowEval12867 (x : Key → ℝ) : Integer.Sparse.eval row12867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12867, Integer.Sparse.eval_collectBalanced, rawRowCheck12867]

def rawRow12868 : Integer.Sparse Key := [(key900, -6), (key913, -6), (key901, -6), (key901, -6), (key866, 2), (key882, 2), (key868, 2), (key866, 2), (key882, 2), (key732, 2), (key913, 2), (key734, 2), (key901, 2), (key868, 2), (key734, 2), (key901, 2)]

theorem rawRowCheck12868 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form13 = rawRow12868 := by decide +kernel

def row12868 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12868 : row12868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12868 := by decide +kernel

theorem rowEval12868 (x : Key → ℝ) : Integer.Sparse.eval row12868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12868, Integer.Sparse.eval_collectBalanced, rawRowCheck12868]

def rawRow12869 : Integer.Sparse Key := [(key913, -6), (key900, -6), (key901, -6), (key901, -6), (key882, 2), (key866, 2), (key868, 2), (key882, 2), (key866, 2), (key913, 2), (key732, 2), (key901, 2), (key734, 2), (key868, 2), (key901, 2), (key734, 2)]

theorem rawRowCheck12869 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form13 = rawRow12869 := by decide +kernel

def row12869 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12869 : row12869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12869 := by decide +kernel

theorem rowEval12869 (x : Key → ℝ) : Integer.Sparse.eval row12869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12869, Integer.Sparse.eval_collectBalanced, rawRowCheck12869]

def rawRow12870 : Integer.Sparse Key := [(key901, -6), (key913, -6), (key900, -6), (key901, -6), (key868, 2), (key882, 2), (key866, 2), (key901, 2), (key913, 2), (key734, 2), (key882, 2), (key732, 2), (key866, 2), (key901, 2), (key734, 2), (key868, 2)]

theorem rawRowCheck12870 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form13 = rawRow12870 := by decide +kernel

def row12870 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12870 : row12870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12870 := by decide +kernel

theorem rowEval12870 (x : Key → ℝ) : Integer.Sparse.eval row12870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12870, Integer.Sparse.eval_collectBalanced, rawRowCheck12870]

def rawRow12871 : Integer.Sparse Key := [(key913, -6), (key901, -6), (key900, -6), (key901, -6), (key882, 2), (key868, 2), (key866, 2), (key913, 2), (key901, 2), (key882, 2), (key734, 2), (key866, 2), (key732, 2), (key901, 2), (key868, 2), (key734, 2)]

theorem rawRowCheck12871 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form13 = rawRow12871 := by decide +kernel

def row12871 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12871 : row12871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12871 := by decide +kernel

theorem rowEval12871 (x : Key → ℝ) : Integer.Sparse.eval row12871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12871, Integer.Sparse.eval_collectBalanced, rawRowCheck12871]

def rawRow12872 : Integer.Sparse Key := [(key901, -6), (key901, -6), (key913, -6), (key900, -6), (key901, 2), (key901, 2), (key913, 2), (key734, 2), (key734, 2), (key868, 2), (key868, 2), (key882, 2), (key882, 2), (key732, 2), (key866, 2), (key866, 2)]

theorem rawRowCheck12872 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form13 = rawRow12872 := by decide +kernel

def row12872 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12872 : row12872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12872 := by decide +kernel

theorem rowEval12872 (x : Key → ℝ) : Integer.Sparse.eval row12872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12872, Integer.Sparse.eval_collectBalanced, rawRowCheck12872]

def rawRow12873 : Integer.Sparse Key := [(key901, -6), (key913, -6), (key901, -6), (key900, -6), (key901, 2), (key913, 2), (key901, 2), (key868, 2), (key882, 2), (key734, 2), (key882, 2), (key734, 2), (key868, 2), (key866, 2), (key732, 2), (key866, 2)]

theorem rawRowCheck12873 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form13 = rawRow12873 := by decide +kernel

def row12873 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12873 : row12873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12873 := by decide +kernel

theorem rowEval12873 (x : Key → ℝ) : Integer.Sparse.eval row12873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12873, Integer.Sparse.eval_collectBalanced, rawRowCheck12873]

def rawRow12874 : Integer.Sparse Key := [(key913, -6), (key901, -6), (key901, -6), (key900, -6), (key913, 2), (key901, 2), (key901, 2), (key882, 2), (key868, 2), (key882, 2), (key734, 2), (key868, 2), (key734, 2), (key866, 2), (key866, 2), (key732, 2)]

theorem rawRowCheck12874 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form13 = rawRow12874 := by decide +kernel

def row12874 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

theorem rowCheck12874 : row12874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12874 := by decide +kernel

theorem rowEval12874 (x : Key → ℝ) : Integer.Sparse.eval row12874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12874, Integer.Sparse.eval_collectBalanced, rawRowCheck12874]

def rawRow12875 : Integer.Sparse Key := [(key498, 6), (key498, 6), (key504, 6), (key666, 6), (key232, -6), (key504, -6), (key562, -6), (key562, -6)]

theorem rawRowCheck12875 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form14 = rawRow12875 := by decide +kernel

def row12875 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12875 : row12875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12875 := by decide +kernel

theorem rowEval12875 (x : Key → ℝ) : Integer.Sparse.eval row12875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12875, Integer.Sparse.eval_collectBalanced, rawRowCheck12875]

def rawRow12876 : Integer.Sparse Key := [(key498, 6), (key504, 6), (key498, 6), (key666, 6), (key232, -6), (key562, -6), (key504, -6), (key562, -6)]

theorem rawRowCheck12876 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form14 = rawRow12876 := by decide +kernel

def row12876 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12876 : row12876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12876 := by decide +kernel

theorem rowEval12876 (x : Key → ℝ) : Integer.Sparse.eval row12876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12876, Integer.Sparse.eval_collectBalanced, rawRowCheck12876]

def rawRow12877 : Integer.Sparse Key := [(key504, 6), (key498, 6), (key498, 6), (key666, 6), (key232, -6), (key562, -6), (key562, -6), (key504, -6)]

theorem rawRowCheck12877 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form14 = rawRow12877 := by decide +kernel

def row12877 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12877 : row12877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12877 := by decide +kernel

theorem rowEval12877 (x : Key → ℝ) : Integer.Sparse.eval row12877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12877, Integer.Sparse.eval_collectBalanced, rawRowCheck12877]

def rawRow12878 : Integer.Sparse Key := [(key498, 6), (key498, 6), (key666, 6), (key504, 6), (key504, -6), (key232, -6), (key562, -6), (key562, -6)]

theorem rawRowCheck12878 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form14 = rawRow12878 := by decide +kernel

def row12878 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12878 : row12878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12878 := by decide +kernel

theorem rowEval12878 (x : Key → ℝ) : Integer.Sparse.eval row12878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12878, Integer.Sparse.eval_collectBalanced, rawRowCheck12878]

def rawRow12879 : Integer.Sparse Key := [(key498, 6), (key666, 6), (key498, 6), (key504, 6), (key504, -6), (key562, -6), (key232, -6), (key562, -6)]

theorem rawRowCheck12879 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form14 = rawRow12879 := by decide +kernel

def row12879 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12879 : row12879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12879 := by decide +kernel

theorem rowEval12879 (x : Key → ℝ) : Integer.Sparse.eval row12879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12879, Integer.Sparse.eval_collectBalanced, rawRowCheck12879]

def rawRow12880 : Integer.Sparse Key := [(key666, 6), (key498, 6), (key498, 6), (key504, 6), (key504, -6), (key562, -6), (key562, -6), (key232, -6)]

theorem rawRowCheck12880 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form14 = rawRow12880 := by decide +kernel

def row12880 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12880 : row12880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12880 := by decide +kernel

theorem rowEval12880 (x : Key → ℝ) : Integer.Sparse.eval row12880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12880, Integer.Sparse.eval_collectBalanced, rawRowCheck12880]

def rawRow12881 : Integer.Sparse Key := [(key498, 6), (key504, 6), (key666, 6), (key498, 6), (key562, -6), (key232, -6), (key504, -6), (key562, -6)]

theorem rawRowCheck12881 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form14 = rawRow12881 := by decide +kernel

def row12881 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12881 : row12881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12881 := by decide +kernel

theorem rowEval12881 (x : Key → ℝ) : Integer.Sparse.eval row12881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12881, Integer.Sparse.eval_collectBalanced, rawRowCheck12881]

def rawRow12882 : Integer.Sparse Key := [(key504, 6), (key498, 6), (key666, 6), (key498, 6), (key562, -6), (key232, -6), (key562, -6), (key504, -6)]

theorem rawRowCheck12882 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form14 = rawRow12882 := by decide +kernel

def row12882 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12882 : row12882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12882 := by decide +kernel

theorem rowEval12882 (x : Key → ℝ) : Integer.Sparse.eval row12882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12882, Integer.Sparse.eval_collectBalanced, rawRowCheck12882]

def rawRow12883 : Integer.Sparse Key := [(key498, 6), (key666, 6), (key504, 6), (key498, 6), (key562, -6), (key504, -6), (key232, -6), (key562, -6)]

theorem rawRowCheck12883 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form14 = rawRow12883 := by decide +kernel

def row12883 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12883 : row12883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12883 := by decide +kernel

theorem rowEval12883 (x : Key → ℝ) : Integer.Sparse.eval row12883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12883, Integer.Sparse.eval_collectBalanced, rawRowCheck12883]

def rawRow12884 : Integer.Sparse Key := [(key666, 6), (key498, 6), (key504, 6), (key498, 6), (key562, -6), (key504, -6), (key562, -6), (key232, -6)]

theorem rawRowCheck12884 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form14 = rawRow12884 := by decide +kernel

def row12884 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12884 : row12884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12884 := by decide +kernel

theorem rowEval12884 (x : Key → ℝ) : Integer.Sparse.eval row12884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12884, Integer.Sparse.eval_collectBalanced, rawRowCheck12884]

def rawRow12885 : Integer.Sparse Key := [(key504, 6), (key666, 6), (key498, 6), (key498, 6), (key562, -6), (key562, -6), (key232, -6), (key504, -6)]

theorem rawRowCheck12885 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form14 = rawRow12885 := by decide +kernel

def row12885 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12885 : row12885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12885 := by decide +kernel

theorem rowEval12885 (x : Key → ℝ) : Integer.Sparse.eval row12885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12885, Integer.Sparse.eval_collectBalanced, rawRowCheck12885]

def rawRow12886 : Integer.Sparse Key := [(key666, 6), (key504, 6), (key498, 6), (key498, 6), (key562, -6), (key562, -6), (key504, -6), (key232, -6)]

theorem rawRowCheck12886 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form14 = rawRow12886 := by decide +kernel

def row12886 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

theorem rowCheck12886 : row12886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12886 := by decide +kernel

theorem rowEval12886 (x : Key → ℝ) : Integer.Sparse.eval row12886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12886, Integer.Sparse.eval_collectBalanced, rawRowCheck12886]

def rawRow12887 : Integer.Sparse Key := [(key552, 6), (key562, 6), (key562, 6), (key683, 6), (key226, -6), (key498, -6), (key498, -6), (key552, -6)]

theorem rawRowCheck12887 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form14 = rawRow12887 := by decide +kernel

def row12887 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12887 : row12887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12887 := by decide +kernel

theorem rowEval12887 (x : Key → ℝ) : Integer.Sparse.eval row12887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12887, Integer.Sparse.eval_collectBalanced, rawRowCheck12887]

def rawRow12888 : Integer.Sparse Key := [(key562, 6), (key552, 6), (key562, 6), (key683, 6), (key226, -6), (key498, -6), (key552, -6), (key498, -6)]

theorem rawRowCheck12888 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form14 = rawRow12888 := by decide +kernel

def row12888 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12888 : row12888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12888 := by decide +kernel

theorem rowEval12888 (x : Key → ℝ) : Integer.Sparse.eval row12888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12888, Integer.Sparse.eval_collectBalanced, rawRowCheck12888]

def rawRow12889 : Integer.Sparse Key := [(key562, 6), (key562, 6), (key552, 6), (key683, 6), (key226, -6), (key552, -6), (key498, -6), (key498, -6)]

theorem rawRowCheck12889 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form14 = rawRow12889 := by decide +kernel

def row12889 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12889 : row12889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12889 := by decide +kernel

theorem rowEval12889 (x : Key → ℝ) : Integer.Sparse.eval row12889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12889, Integer.Sparse.eval_collectBalanced, rawRowCheck12889]

def rawRow12890 : Integer.Sparse Key := [(key552, 6), (key562, 6), (key683, 6), (key562, 6), (key498, -6), (key226, -6), (key498, -6), (key552, -6)]

theorem rawRowCheck12890 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form14 = rawRow12890 := by decide +kernel

def row12890 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12890 : row12890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12890 := by decide +kernel

theorem rowEval12890 (x : Key → ℝ) : Integer.Sparse.eval row12890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12890, Integer.Sparse.eval_collectBalanced, rawRowCheck12890]

def rawRow12891 : Integer.Sparse Key := [(key562, 6), (key552, 6), (key683, 6), (key562, 6), (key498, -6), (key226, -6), (key552, -6), (key498, -6)]

theorem rawRowCheck12891 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form14 = rawRow12891 := by decide +kernel

def row12891 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12891 : row12891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12891 := by decide +kernel

theorem rowEval12891 (x : Key → ℝ) : Integer.Sparse.eval row12891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12891, Integer.Sparse.eval_collectBalanced, rawRowCheck12891]

def rawRow12892 : Integer.Sparse Key := [(key552, 6), (key683, 6), (key562, 6), (key562, 6), (key498, -6), (key498, -6), (key226, -6), (key552, -6)]

theorem rawRowCheck12892 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form14 = rawRow12892 := by decide +kernel

def row12892 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12892 : row12892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12892 := by decide +kernel

theorem rowEval12892 (x : Key → ℝ) : Integer.Sparse.eval row12892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12892, Integer.Sparse.eval_collectBalanced, rawRowCheck12892]

def rawRow12893 : Integer.Sparse Key := [(key683, 6), (key552, 6), (key562, 6), (key562, 6), (key498, -6), (key498, -6), (key552, -6), (key226, -6)]

theorem rawRowCheck12893 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form14 = rawRow12893 := by decide +kernel

def row12893 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12893 : row12893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12893 := by decide +kernel

theorem rowEval12893 (x : Key → ℝ) : Integer.Sparse.eval row12893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12893, Integer.Sparse.eval_collectBalanced, rawRowCheck12893]

def rawRow12894 : Integer.Sparse Key := [(key562, 6), (key683, 6), (key552, 6), (key562, 6), (key498, -6), (key552, -6), (key226, -6), (key498, -6)]

theorem rawRowCheck12894 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form14 = rawRow12894 := by decide +kernel

def row12894 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12894 : row12894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12894 := by decide +kernel

theorem rowEval12894 (x : Key → ℝ) : Integer.Sparse.eval row12894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12894, Integer.Sparse.eval_collectBalanced, rawRowCheck12894]

def rawRow12895 : Integer.Sparse Key := [(key683, 6), (key562, 6), (key552, 6), (key562, 6), (key498, -6), (key552, -6), (key498, -6), (key226, -6)]

theorem rawRowCheck12895 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form14 = rawRow12895 := by decide +kernel

def row12895 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12895 : row12895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12895 := by decide +kernel

theorem rowEval12895 (x : Key → ℝ) : Integer.Sparse.eval row12895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12895, Integer.Sparse.eval_collectBalanced, rawRowCheck12895]

def rawRow12896 : Integer.Sparse Key := [(key562, 6), (key562, 6), (key683, 6), (key552, 6), (key552, -6), (key226, -6), (key498, -6), (key498, -6)]

theorem rawRowCheck12896 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form14 = rawRow12896 := by decide +kernel

def row12896 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12896 : row12896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12896 := by decide +kernel

theorem rowEval12896 (x : Key → ℝ) : Integer.Sparse.eval row12896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12896, Integer.Sparse.eval_collectBalanced, rawRowCheck12896]

def rawRow12897 : Integer.Sparse Key := [(key562, 6), (key683, 6), (key562, 6), (key552, 6), (key552, -6), (key498, -6), (key226, -6), (key498, -6)]

theorem rawRowCheck12897 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form14 = rawRow12897 := by decide +kernel

def row12897 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12897 : row12897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12897 := by decide +kernel

theorem rowEval12897 (x : Key → ℝ) : Integer.Sparse.eval row12897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12897, Integer.Sparse.eval_collectBalanced, rawRowCheck12897]

def rawRow12898 : Integer.Sparse Key := [(key683, 6), (key562, 6), (key562, 6), (key552, 6), (key552, -6), (key498, -6), (key498, -6), (key226, -6)]

theorem rawRowCheck12898 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form14 = rawRow12898 := by decide +kernel

def row12898 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

theorem rowCheck12898 : row12898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12898 := by decide +kernel

theorem rowEval12898 (x : Key → ℝ) : Integer.Sparse.eval row12898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12898, Integer.Sparse.eval_collectBalanced, rawRowCheck12898]

def rawRow12899 : Integer.Sparse Key := [(key1704, -6), (key1704, -6), (key1708, -6), (key1857, -6), (key1281, 2), (key1281, 2), (key1285, 2), (key1704, 2), (key1704, 2), (key1753, 2), (key1753, 2), (key1758, 2), (key1758, 2), (key1857, 2), (key1888, 2), (key1888, 2)]

theorem rawRowCheck12899 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form15 = rawRow12899 := by decide +kernel

def row12899 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12899 : row12899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12899 := by decide +kernel

theorem rowEval12899 (x : Key → ℝ) : Integer.Sparse.eval row12899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12899, Integer.Sparse.eval_collectBalanced, rawRowCheck12899]

def rawRow12900 : Integer.Sparse Key := [(key1704, -6), (key1708, -6), (key1704, -6), (key1857, -6), (key1281, 2), (key1285, 2), (key1281, 2), (key1753, 2), (key1758, 2), (key1704, 2), (key1758, 2), (key1704, 2), (key1753, 2), (key1888, 2), (key1857, 2), (key1888, 2)]

theorem rawRowCheck12900 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form15 = rawRow12900 := by decide +kernel

def row12900 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12900 : row12900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12900 := by decide +kernel

theorem rowEval12900 (x : Key → ℝ) : Integer.Sparse.eval row12900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12900, Integer.Sparse.eval_collectBalanced, rawRowCheck12900]

def rawRow12901 : Integer.Sparse Key := [(key1708, -6), (key1704, -6), (key1704, -6), (key1857, -6), (key1285, 2), (key1281, 2), (key1281, 2), (key1758, 2), (key1753, 2), (key1758, 2), (key1704, 2), (key1753, 2), (key1704, 2), (key1888, 2), (key1888, 2), (key1857, 2)]

theorem rawRowCheck12901 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form15 = rawRow12901 := by decide +kernel

def row12901 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12901 : row12901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12901 := by decide +kernel

theorem rowEval12901 (x : Key → ℝ) : Integer.Sparse.eval row12901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12901, Integer.Sparse.eval_collectBalanced, rawRowCheck12901]

def rawRow12902 : Integer.Sparse Key := [(key1704, -6), (key1704, -6), (key1857, -6), (key1708, -6), (key1704, 2), (key1704, 2), (key1857, 2), (key1281, 2), (key1281, 2), (key1753, 2), (key1753, 2), (key1888, 2), (key1888, 2), (key1285, 2), (key1758, 2), (key1758, 2)]

theorem rawRowCheck12902 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form15 = rawRow12902 := by decide +kernel

def row12902 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12902 : row12902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12902 := by decide +kernel

theorem rowEval12902 (x : Key → ℝ) : Integer.Sparse.eval row12902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12902, Integer.Sparse.eval_collectBalanced, rawRowCheck12902]

def rawRow12903 : Integer.Sparse Key := [(key1704, -6), (key1857, -6), (key1704, -6), (key1708, -6), (key1704, 2), (key1857, 2), (key1704, 2), (key1753, 2), (key1888, 2), (key1281, 2), (key1888, 2), (key1281, 2), (key1753, 2), (key1758, 2), (key1285, 2), (key1758, 2)]

theorem rawRowCheck12903 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form15 = rawRow12903 := by decide +kernel

def row12903 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12903 : row12903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12903 := by decide +kernel

theorem rowEval12903 (x : Key → ℝ) : Integer.Sparse.eval row12903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12903, Integer.Sparse.eval_collectBalanced, rawRowCheck12903]

def rawRow12904 : Integer.Sparse Key := [(key1857, -6), (key1704, -6), (key1704, -6), (key1708, -6), (key1857, 2), (key1704, 2), (key1704, 2), (key1888, 2), (key1753, 2), (key1888, 2), (key1281, 2), (key1753, 2), (key1281, 2), (key1758, 2), (key1758, 2), (key1285, 2)]

theorem rawRowCheck12904 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form15 = rawRow12904 := by decide +kernel

def row12904 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12904 : row12904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12904 := by decide +kernel

theorem rowEval12904 (x : Key → ℝ) : Integer.Sparse.eval row12904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12904, Integer.Sparse.eval_collectBalanced, rawRowCheck12904]

def rawRow12905 : Integer.Sparse Key := [(key1704, -6), (key1708, -6), (key1857, -6), (key1704, -6), (key1753, 2), (key1758, 2), (key1888, 2), (key1281, 2), (key1285, 2), (key1704, 2), (key1758, 2), (key1857, 2), (key1888, 2), (key1281, 2), (key1704, 2), (key1753, 2)]

theorem rawRowCheck12905 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form15 = rawRow12905 := by decide +kernel

def row12905 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12905 : row12905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12905 := by decide +kernel

theorem rowEval12905 (x : Key → ℝ) : Integer.Sparse.eval row12905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12905, Integer.Sparse.eval_collectBalanced, rawRowCheck12905]

def rawRow12906 : Integer.Sparse Key := [(key1708, -6), (key1704, -6), (key1857, -6), (key1704, -6), (key1758, 2), (key1753, 2), (key1888, 2), (key1285, 2), (key1281, 2), (key1758, 2), (key1704, 2), (key1888, 2), (key1857, 2), (key1281, 2), (key1753, 2), (key1704, 2)]

theorem rawRowCheck12906 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form15 = rawRow12906 := by decide +kernel

def row12906 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12906 : row12906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12906 := by decide +kernel

theorem rowEval12906 (x : Key → ℝ) : Integer.Sparse.eval row12906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12906, Integer.Sparse.eval_collectBalanced, rawRowCheck12906]

def rawRow12907 : Integer.Sparse Key := [(key1704, -6), (key1857, -6), (key1708, -6), (key1704, -6), (key1753, 2), (key1888, 2), (key1758, 2), (key1704, 2), (key1857, 2), (key1281, 2), (key1888, 2), (key1285, 2), (key1758, 2), (key1704, 2), (key1281, 2), (key1753, 2)]

theorem rawRowCheck12907 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form15 = rawRow12907 := by decide +kernel

def row12907 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12907 : row12907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12907 := by decide +kernel

theorem rowEval12907 (x : Key → ℝ) : Integer.Sparse.eval row12907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12907, Integer.Sparse.eval_collectBalanced, rawRowCheck12907]

def rawRow12908 : Integer.Sparse Key := [(key1857, -6), (key1704, -6), (key1708, -6), (key1704, -6), (key1888, 2), (key1753, 2), (key1758, 2), (key1857, 2), (key1704, 2), (key1888, 2), (key1281, 2), (key1758, 2), (key1285, 2), (key1704, 2), (key1753, 2), (key1281, 2)]

theorem rawRowCheck12908 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form15 = rawRow12908 := by decide +kernel

def row12908 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12908 : row12908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12908 := by decide +kernel

theorem rowEval12908 (x : Key → ℝ) : Integer.Sparse.eval row12908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12908, Integer.Sparse.eval_collectBalanced, rawRowCheck12908]

def rawRow12909 : Integer.Sparse Key := [(key1708, -6), (key1857, -6), (key1704, -6), (key1704, -6), (key1758, 2), (key1888, 2), (key1753, 2), (key1758, 2), (key1888, 2), (key1285, 2), (key1857, 2), (key1281, 2), (key1704, 2), (key1753, 2), (key1281, 2), (key1704, 2)]

theorem rawRowCheck12909 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form15 = rawRow12909 := by decide +kernel

def row12909 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12909 : row12909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12909 := by decide +kernel

theorem rowEval12909 (x : Key → ℝ) : Integer.Sparse.eval row12909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12909, Integer.Sparse.eval_collectBalanced, rawRowCheck12909]

def rawRow12910 : Integer.Sparse Key := [(key1857, -6), (key1708, -6), (key1704, -6), (key1704, -6), (key1888, 2), (key1758, 2), (key1753, 2), (key1888, 2), (key1758, 2), (key1857, 2), (key1285, 2), (key1704, 2), (key1281, 2), (key1753, 2), (key1704, 2), (key1281, 2)]

theorem rawRowCheck12910 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form15 = rawRow12910 := by decide +kernel

def row12910 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

theorem rowCheck12910 : row12910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12910 := by decide +kernel

theorem rowEval12910 (x : Key → ℝ) : Integer.Sparse.eval row12910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12910, Integer.Sparse.eval_collectBalanced, rawRowCheck12910]

def rawRow12911 : Integer.Sparse Key := [(key1753, -6), (key1758, -6), (key1758, -6), (key1888, -6), (key1281, 2), (key1285, 2), (key1285, 2), (key1704, 2), (key1708, 2), (key1704, 2), (key1758, 2), (key1708, 2), (key1758, 2), (key1857, 2), (key1857, 2), (key1888, 2)]

theorem rawRowCheck12911 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form15 = rawRow12911 := by decide +kernel

def row12911 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12911 : row12911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12911 := by decide +kernel

theorem rowEval12911 (x : Key → ℝ) : Integer.Sparse.eval row12911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12911, Integer.Sparse.eval_collectBalanced, rawRowCheck12911]

def rawRow12912 : Integer.Sparse Key := [(key1758, -6), (key1753, -6), (key1758, -6), (key1888, -6), (key1285, 2), (key1281, 2), (key1285, 2), (key1708, 2), (key1704, 2), (key1758, 2), (key1704, 2), (key1758, 2), (key1708, 2), (key1857, 2), (key1888, 2), (key1857, 2)]

theorem rawRowCheck12912 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form15 = rawRow12912 := by decide +kernel

def row12912 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12912 : row12912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12912 := by decide +kernel

theorem rowEval12912 (x : Key → ℝ) : Integer.Sparse.eval row12912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12912, Integer.Sparse.eval_collectBalanced, rawRowCheck12912]

def rawRow12913 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1753, -6), (key1888, -6), (key1285, 2), (key1285, 2), (key1281, 2), (key1758, 2), (key1758, 2), (key1708, 2), (key1708, 2), (key1704, 2), (key1704, 2), (key1888, 2), (key1857, 2), (key1857, 2)]

theorem rawRowCheck12913 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form15 = rawRow12913 := by decide +kernel

def row12913 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12913 : row12913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12913 := by decide +kernel

theorem rowEval12913 (x : Key → ℝ) : Integer.Sparse.eval row12913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12913, Integer.Sparse.eval_collectBalanced, rawRowCheck12913]

def rawRow12914 : Integer.Sparse Key := [(key1753, -6), (key1758, -6), (key1888, -6), (key1758, -6), (key1704, 2), (key1708, 2), (key1857, 2), (key1281, 2), (key1285, 2), (key1704, 2), (key1758, 2), (key1857, 2), (key1888, 2), (key1285, 2), (key1708, 2), (key1758, 2)]

theorem rawRowCheck12914 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form15 = rawRow12914 := by decide +kernel

def row12914 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12914 : row12914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12914 := by decide +kernel

theorem rowEval12914 (x : Key → ℝ) : Integer.Sparse.eval row12914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12914, Integer.Sparse.eval_collectBalanced, rawRowCheck12914]

def rawRow12915 : Integer.Sparse Key := [(key1758, -6), (key1753, -6), (key1888, -6), (key1758, -6), (key1708, 2), (key1704, 2), (key1857, 2), (key1285, 2), (key1281, 2), (key1758, 2), (key1704, 2), (key1888, 2), (key1857, 2), (key1285, 2), (key1758, 2), (key1708, 2)]

theorem rawRowCheck12915 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form15 = rawRow12915 := by decide +kernel

def row12915 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12915 : row12915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12915 := by decide +kernel

theorem rowEval12915 (x : Key → ℝ) : Integer.Sparse.eval row12915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12915, Integer.Sparse.eval_collectBalanced, rawRowCheck12915]

def rawRow12916 : Integer.Sparse Key := [(key1753, -6), (key1888, -6), (key1758, -6), (key1758, -6), (key1704, 2), (key1857, 2), (key1708, 2), (key1704, 2), (key1857, 2), (key1281, 2), (key1888, 2), (key1285, 2), (key1758, 2), (key1708, 2), (key1285, 2), (key1758, 2)]

theorem rawRowCheck12916 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form15 = rawRow12916 := by decide +kernel

def row12916 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12916 : row12916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12916 := by decide +kernel

theorem rowEval12916 (x : Key → ℝ) : Integer.Sparse.eval row12916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12916, Integer.Sparse.eval_collectBalanced, rawRowCheck12916]

def rawRow12917 : Integer.Sparse Key := [(key1888, -6), (key1753, -6), (key1758, -6), (key1758, -6), (key1857, 2), (key1704, 2), (key1708, 2), (key1857, 2), (key1704, 2), (key1888, 2), (key1281, 2), (key1758, 2), (key1285, 2), (key1708, 2), (key1758, 2), (key1285, 2)]

theorem rawRowCheck12917 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form15 = rawRow12917 := by decide +kernel

def row12917 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12917 : row12917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12917 := by decide +kernel

theorem rowEval12917 (x : Key → ℝ) : Integer.Sparse.eval row12917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12917, Integer.Sparse.eval_collectBalanced, rawRowCheck12917]

def rawRow12918 : Integer.Sparse Key := [(key1758, -6), (key1888, -6), (key1753, -6), (key1758, -6), (key1708, 2), (key1857, 2), (key1704, 2), (key1758, 2), (key1888, 2), (key1285, 2), (key1857, 2), (key1281, 2), (key1704, 2), (key1758, 2), (key1285, 2), (key1708, 2)]

theorem rawRowCheck12918 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form15 = rawRow12918 := by decide +kernel

def row12918 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12918 : row12918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12918 := by decide +kernel

theorem rowEval12918 (x : Key → ℝ) : Integer.Sparse.eval row12918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12918, Integer.Sparse.eval_collectBalanced, rawRowCheck12918]

def rawRow12919 : Integer.Sparse Key := [(key1888, -6), (key1758, -6), (key1753, -6), (key1758, -6), (key1857, 2), (key1708, 2), (key1704, 2), (key1888, 2), (key1758, 2), (key1857, 2), (key1285, 2), (key1704, 2), (key1281, 2), (key1758, 2), (key1708, 2), (key1285, 2)]

theorem rawRowCheck12919 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form15 = rawRow12919 := by decide +kernel

def row12919 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12919 : row12919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12919 := by decide +kernel

theorem rowEval12919 (x : Key → ℝ) : Integer.Sparse.eval row12919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12919, Integer.Sparse.eval_collectBalanced, rawRowCheck12919]

def rawRow12920 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1888, -6), (key1753, -6), (key1758, 2), (key1758, 2), (key1888, 2), (key1285, 2), (key1285, 2), (key1708, 2), (key1708, 2), (key1857, 2), (key1857, 2), (key1281, 2), (key1704, 2), (key1704, 2)]

theorem rawRowCheck12920 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form15 = rawRow12920 := by decide +kernel

def row12920 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12920 : row12920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12920 := by decide +kernel

theorem rowEval12920 (x : Key → ℝ) : Integer.Sparse.eval row12920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12920, Integer.Sparse.eval_collectBalanced, rawRowCheck12920]

def rawRow12921 : Integer.Sparse Key := [(key1758, -6), (key1888, -6), (key1758, -6), (key1753, -6), (key1758, 2), (key1888, 2), (key1758, 2), (key1708, 2), (key1857, 2), (key1285, 2), (key1857, 2), (key1285, 2), (key1708, 2), (key1704, 2), (key1281, 2), (key1704, 2)]

theorem rawRowCheck12921 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form15 = rawRow12921 := by decide +kernel

def row12921 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12921 : row12921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12921 := by decide +kernel

theorem rowEval12921 (x : Key → ℝ) : Integer.Sparse.eval row12921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12921, Integer.Sparse.eval_collectBalanced, rawRowCheck12921]

def rawRow12922 : Integer.Sparse Key := [(key1888, -6), (key1758, -6), (key1758, -6), (key1753, -6), (key1888, 2), (key1758, 2), (key1758, 2), (key1857, 2), (key1708, 2), (key1857, 2), (key1285, 2), (key1708, 2), (key1285, 2), (key1704, 2), (key1704, 2), (key1281, 2)]

theorem rawRowCheck12922 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form15 = rawRow12922 := by decide +kernel

def row12922 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

theorem rowCheck12922 : row12922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12922 := by decide +kernel

theorem rowEval12922 (x : Key → ℝ) : Integer.Sparse.eval row12922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12922, Integer.Sparse.eval_collectBalanced, rawRowCheck12922]

def rawRow12923 : Integer.Sparse Key := [(key1494, -6), (key1720, -6), (key1726, -6), (key1726, -6), (key1368, 6), (key1720, 6), (key1744, 6), (key1744, 6)]

theorem rawRowCheck12923 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form16 = rawRow12923 := by decide +kernel

def row12923 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12923 : row12923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12923 := by decide +kernel

theorem rowEval12923 (x : Key → ℝ) : Integer.Sparse.eval row12923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12923, Integer.Sparse.eval_collectBalanced, rawRowCheck12923]

def rawRow12924 : Integer.Sparse Key := [(key1494, -6), (key1726, -6), (key1720, -6), (key1726, -6), (key1368, 6), (key1744, 6), (key1720, 6), (key1744, 6)]

theorem rawRowCheck12924 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form16 = rawRow12924 := by decide +kernel

def row12924 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12924 : row12924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12924 := by decide +kernel

theorem rowEval12924 (x : Key → ℝ) : Integer.Sparse.eval row12924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12924, Integer.Sparse.eval_collectBalanced, rawRowCheck12924]

def rawRow12925 : Integer.Sparse Key := [(key1494, -6), (key1726, -6), (key1726, -6), (key1720, -6), (key1368, 6), (key1744, 6), (key1744, 6), (key1720, 6)]

theorem rawRowCheck12925 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form16 = rawRow12925 := by decide +kernel

def row12925 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12925 : row12925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12925 := by decide +kernel

theorem rowEval12925 (x : Key → ℝ) : Integer.Sparse.eval row12925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12925, Integer.Sparse.eval_collectBalanced, rawRowCheck12925]

def rawRow12926 : Integer.Sparse Key := [(key1720, -6), (key1494, -6), (key1726, -6), (key1726, -6), (key1720, 6), (key1368, 6), (key1744, 6), (key1744, 6)]

theorem rawRowCheck12926 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form16 = rawRow12926 := by decide +kernel

def row12926 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12926 : row12926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12926 := by decide +kernel

theorem rowEval12926 (x : Key → ℝ) : Integer.Sparse.eval row12926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12926, Integer.Sparse.eval_collectBalanced, rawRowCheck12926]

def rawRow12927 : Integer.Sparse Key := [(key1720, -6), (key1726, -6), (key1494, -6), (key1726, -6), (key1720, 6), (key1744, 6), (key1368, 6), (key1744, 6)]

theorem rawRowCheck12927 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form16 = rawRow12927 := by decide +kernel

def row12927 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12927 : row12927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12927 := by decide +kernel

theorem rowEval12927 (x : Key → ℝ) : Integer.Sparse.eval row12927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12927, Integer.Sparse.eval_collectBalanced, rawRowCheck12927]

end MUB6.Certificate.GramRows

end OAI

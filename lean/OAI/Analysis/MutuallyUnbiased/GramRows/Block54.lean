import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3840 : Integer.Sparse Key := [(key1620, -6), (key1418, 2), (key1616, 2), (key1567, 2), (key1629, 6), (key1310, -2), (key1616, -2), (key1540, -2), (key1440, -2), (key1629, -2), (key1589, -2), (key1322, 2), (key1620, 2), (key1552, 2)]

theorem rawRowCheck3840 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form4 = rawRow3840 := by decide +kernel

def row3840 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

theorem rowCheck3840 : row3840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3840 := by decide +kernel

theorem rowEval3840 (x : Key → ℝ) : Integer.Sparse.eval row3840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3840, Integer.Sparse.eval_collectBalanced, rawRowCheck3840]

def rawRow3841 : Integer.Sparse Key := [(key1620, -6), (key1567, 2), (key1418, 2), (key1616, 2), (key1629, 6), (key1540, -2), (key1310, -2), (key1616, -2), (key1589, -2), (key1440, -2), (key1629, -2), (key1552, 2), (key1322, 2), (key1620, 2)]

theorem rawRowCheck3841 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form4 = rawRow3841 := by decide +kernel

def row3841 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

theorem rowCheck3841 : row3841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3841 := by decide +kernel

theorem rowEval3841 (x : Key → ℝ) : Integer.Sparse.eval row3841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3841, Integer.Sparse.eval_collectBalanced, rawRowCheck3841]

def rawRow3842 : Integer.Sparse Key := [(key1620, -6), (key1567, 2), (key1616, 2), (key1418, 2), (key1629, 6), (key1540, -2), (key1616, -2), (key1310, -2), (key1589, -2), (key1629, -2), (key1440, -2), (key1552, 2), (key1620, 2), (key1322, 2)]

theorem rawRowCheck3842 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form4 = rawRow3842 := by decide +kernel

def row3842 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

theorem rowCheck3842 : row3842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3842 := by decide +kernel

theorem rowEval3842 (x : Key → ℝ) : Integer.Sparse.eval row3842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3842, Integer.Sparse.eval_collectBalanced, rawRowCheck3842]

def rawRow3843 : Integer.Sparse Key := [(key1620, -6), (key1616, 2), (key1418, 2), (key1567, 2), (key1629, 6), (key1616, -2), (key1310, -2), (key1540, -2), (key1629, -2), (key1440, -2), (key1589, -2), (key1620, 2), (key1322, 2), (key1552, 2)]

theorem rawRowCheck3843 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form4 = rawRow3843 := by decide +kernel

def row3843 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

theorem rowCheck3843 : row3843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3843 := by decide +kernel

theorem rowEval3843 (x : Key → ℝ) : Integer.Sparse.eval row3843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3843, Integer.Sparse.eval_collectBalanced, rawRowCheck3843]

def rawRow3844 : Integer.Sparse Key := [(key1620, -6), (key1616, 2), (key1567, 2), (key1418, 2), (key1629, 6), (key1616, -2), (key1540, -2), (key1310, -2), (key1629, -2), (key1589, -2), (key1440, -2), (key1620, 2), (key1552, 2), (key1322, 2)]

theorem rawRowCheck3844 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form4 = rawRow3844 := by decide +kernel

def row3844 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

theorem rowCheck3844 : row3844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3844 := by decide +kernel

theorem rowEval3844 (x : Key → ℝ) : Integer.Sparse.eval row3844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3844, Integer.Sparse.eval_collectBalanced, rawRowCheck3844]

def rawRow3845 : Integer.Sparse Key := [(key1589, -6), (key1440, 2), (key1629, 2), (key1629, 2), (key1552, 6), (key1322, -2), (key1620, -2), (key1620, -2), (key1385, -2), (key1540, -2), (key1540, -2), (key1290, 2), (key1567, 2), (key1567, 2)]

theorem rawRowCheck3845 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow3845 := by decide +kernel

def row3845 : Integer.Sparse Key := [(key1290, 2), (key1322, -2), (key1385, -2), (key1440, 2), (key1540, -4), (key1552, 6), (key1567, 4), (key1589, -6), (key1620, -4), (key1629, 4)]

theorem rowCheck3845 : row3845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3845 := by decide +kernel

theorem rowEval3845 (x : Key → ℝ) : Integer.Sparse.eval row3845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3845, Integer.Sparse.eval_collectBalanced, rawRowCheck3845]

def rawRow3846 : Integer.Sparse Key := [(key1589, -6), (key1629, 2), (key1440, 2), (key1629, 2), (key1552, 6), (key1620, -2), (key1322, -2), (key1620, -2), (key1540, -2), (key1385, -2), (key1540, -2), (key1567, 2), (key1290, 2), (key1567, 2)]

theorem rawRowCheck3846 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow3846 := by decide +kernel

def row3846 : Integer.Sparse Key := [(key1290, 2), (key1322, -2), (key1385, -2), (key1440, 2), (key1540, -4), (key1552, 6), (key1567, 4), (key1589, -6), (key1620, -4), (key1629, 4)]

theorem rowCheck3846 : row3846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3846 := by decide +kernel

theorem rowEval3846 (x : Key → ℝ) : Integer.Sparse.eval row3846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3846, Integer.Sparse.eval_collectBalanced, rawRowCheck3846]

def rawRow3847 : Integer.Sparse Key := [(key1589, -6), (key1629, 2), (key1629, 2), (key1440, 2), (key1552, 6), (key1620, -2), (key1620, -2), (key1322, -2), (key1540, -2), (key1540, -2), (key1385, -2), (key1567, 2), (key1567, 2), (key1290, 2)]

theorem rawRowCheck3847 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow3847 := by decide +kernel

def row3847 : Integer.Sparse Key := [(key1290, 2), (key1322, -2), (key1385, -2), (key1440, 2), (key1540, -4), (key1552, 6), (key1567, 4), (key1589, -6), (key1620, -4), (key1629, 4)]

theorem rowCheck3847 : row3847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3847 := by decide +kernel

theorem rowEval3847 (x : Key → ℝ) : Integer.Sparse.eval row3847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3847, Integer.Sparse.eval_collectBalanced, rawRowCheck3847]

def rawRow3848 : Integer.Sparse Key := [(key1629, -6), (key1440, 2), (key1589, 2), (key1629, 2), (key1620, 6), (key1322, -2), (key1552, -2), (key1620, -2), (key1418, -2), (key1567, -2), (key1616, -2), (key1310, 2), (key1540, 2), (key1616, 2)]

theorem rawRowCheck3848 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form4 = rawRow3848 := by decide +kernel

def row3848 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

theorem rowCheck3848 : row3848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3848 := by decide +kernel

theorem rowEval3848 (x : Key → ℝ) : Integer.Sparse.eval row3848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3848, Integer.Sparse.eval_collectBalanced, rawRowCheck3848]

def rawRow3849 : Integer.Sparse Key := [(key1629, -6), (key1440, 2), (key1629, 2), (key1589, 2), (key1620, 6), (key1322, -2), (key1620, -2), (key1552, -2), (key1418, -2), (key1616, -2), (key1567, -2), (key1310, 2), (key1616, 2), (key1540, 2)]

theorem rawRowCheck3849 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form4 = rawRow3849 := by decide +kernel

def row3849 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

theorem rowCheck3849 : row3849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3849 := by decide +kernel

theorem rowEval3849 (x : Key → ℝ) : Integer.Sparse.eval row3849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3849, Integer.Sparse.eval_collectBalanced, rawRowCheck3849]

def rawRow3850 : Integer.Sparse Key := [(key1629, -6), (key1589, 2), (key1440, 2), (key1629, 2), (key1620, 6), (key1552, -2), (key1322, -2), (key1620, -2), (key1567, -2), (key1418, -2), (key1616, -2), (key1540, 2), (key1310, 2), (key1616, 2)]

theorem rawRowCheck3850 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form4 = rawRow3850 := by decide +kernel

def row3850 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

theorem rowCheck3850 : row3850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3850 := by decide +kernel

theorem rowEval3850 (x : Key → ℝ) : Integer.Sparse.eval row3850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3850, Integer.Sparse.eval_collectBalanced, rawRowCheck3850]

def rawRow3851 : Integer.Sparse Key := [(key1629, -6), (key1589, 2), (key1629, 2), (key1440, 2), (key1620, 6), (key1552, -2), (key1620, -2), (key1322, -2), (key1567, -2), (key1616, -2), (key1418, -2), (key1540, 2), (key1616, 2), (key1310, 2)]

theorem rawRowCheck3851 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form4 = rawRow3851 := by decide +kernel

def row3851 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

theorem rowCheck3851 : row3851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3851 := by decide +kernel

theorem rowEval3851 (x : Key → ℝ) : Integer.Sparse.eval row3851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3851, Integer.Sparse.eval_collectBalanced, rawRowCheck3851]

def rawRow3852 : Integer.Sparse Key := [(key1629, -6), (key1629, 2), (key1440, 2), (key1589, 2), (key1620, 6), (key1620, -2), (key1322, -2), (key1552, -2), (key1616, -2), (key1418, -2), (key1567, -2), (key1616, 2), (key1310, 2), (key1540, 2)]

theorem rawRowCheck3852 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form4 = rawRow3852 := by decide +kernel

def row3852 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

theorem rowCheck3852 : row3852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3852 := by decide +kernel

theorem rowEval3852 (x : Key → ℝ) : Integer.Sparse.eval row3852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3852, Integer.Sparse.eval_collectBalanced, rawRowCheck3852]

def rawRow3853 : Integer.Sparse Key := [(key1629, -6), (key1629, 2), (key1589, 2), (key1440, 2), (key1620, 6), (key1620, -2), (key1552, -2), (key1322, -2), (key1616, -2), (key1567, -2), (key1418, -2), (key1616, 2), (key1540, 2), (key1310, 2)]

theorem rawRowCheck3853 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form4 = rawRow3853 := by decide +kernel

def row3853 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

theorem rowCheck3853 : row3853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3853 := by decide +kernel

theorem rowEval3853 (x : Key → ℝ) : Integer.Sparse.eval row3853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3853, Integer.Sparse.eval_collectBalanced, rawRowCheck3853]

def rawRow3854 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key407, -1), (key579, -1), (key420, -1), (key585, -1), (key240, 2), (key410, 2), (key579, 2), (key249, 1), (key252, 1), (key436, 1), (key594, 1), (key452, 1), (key603, 1), (key252, -1), (key268, -1), (key389, -1), (key569, -1), (key468, -1), (key594, -1), (key262, -2), (key444, -2), (key597, -2), (key262, 1), (key273, 1), (key399, 1), (key574, 1), (key471, 1), (key597, 1)]

theorem rawRowCheck3854 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form5 = rawRow3854 := by decide +kernel

def row3854 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

theorem rowCheck3854 : row3854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3854 := by decide +kernel

theorem rowEval3854 (x : Key → ℝ) : Integer.Sparse.eval row3854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3854, Integer.Sparse.eval_collectBalanced, rawRowCheck3854]

def rawRow3855 : Integer.Sparse Key := [(key240, -1), (key237, -1), (key579, -1), (key407, -1), (key585, -1), (key420, -1), (key240, 2), (key579, 2), (key410, 2), (key252, 1), (key249, 1), (key594, 1), (key436, 1), (key603, 1), (key452, 1), (key268, -1), (key252, -1), (key569, -1), (key389, -1), (key594, -1), (key468, -1), (key262, -2), (key597, -2), (key444, -2), (key273, 1), (key262, 1), (key574, 1), (key399, 1), (key597, 1), (key471, 1)]

theorem rawRowCheck3855 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form5 = rawRow3855 := by decide +kernel

def row3855 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

theorem rowCheck3855 : row3855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3855 := by decide +kernel

theorem rowEval3855 (x : Key → ℝ) : Integer.Sparse.eval row3855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3855, Integer.Sparse.eval_collectBalanced, rawRowCheck3855]

def rawRow3856 : Integer.Sparse Key := [(key407, -1), (key420, -1), (key237, -1), (key585, -1), (key240, -1), (key579, -1), (key410, 2), (key240, 2), (key579, 2), (key436, 1), (key452, 1), (key249, 1), (key603, 1), (key252, 1), (key594, 1), (key389, -1), (key468, -1), (key252, -1), (key594, -1), (key268, -1), (key569, -1), (key444, -2), (key262, -2), (key597, -2), (key399, 1), (key471, 1), (key262, 1), (key597, 1), (key273, 1), (key574, 1)]

theorem rawRowCheck3856 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form5 = rawRow3856 := by decide +kernel

def row3856 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

theorem rowCheck3856 : row3856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3856 := by decide +kernel

theorem rowEval3856 (x : Key → ℝ) : Integer.Sparse.eval row3856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3856, Integer.Sparse.eval_collectBalanced, rawRowCheck3856]

def rawRow3857 : Integer.Sparse Key := [(key420, -1), (key407, -1), (key585, -1), (key237, -1), (key579, -1), (key240, -1), (key410, 2), (key579, 2), (key240, 2), (key452, 1), (key436, 1), (key603, 1), (key249, 1), (key594, 1), (key252, 1), (key468, -1), (key389, -1), (key594, -1), (key252, -1), (key569, -1), (key268, -1), (key444, -2), (key597, -2), (key262, -2), (key471, 1), (key399, 1), (key597, 1), (key262, 1), (key574, 1), (key273, 1)]

theorem rawRowCheck3857 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form5 = rawRow3857 := by decide +kernel

def row3857 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

theorem rowCheck3857 : row3857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3857 := by decide +kernel

theorem rowEval3857 (x : Key → ℝ) : Integer.Sparse.eval row3857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3857, Integer.Sparse.eval_collectBalanced, rawRowCheck3857]

def rawRow3858 : Integer.Sparse Key := [(key579, -1), (key585, -1), (key240, -1), (key420, -1), (key237, -1), (key407, -1), (key579, 2), (key240, 2), (key410, 2), (key594, 1), (key603, 1), (key252, 1), (key452, 1), (key249, 1), (key436, 1), (key569, -1), (key594, -1), (key268, -1), (key468, -1), (key252, -1), (key389, -1), (key597, -2), (key262, -2), (key444, -2), (key574, 1), (key597, 1), (key273, 1), (key471, 1), (key262, 1), (key399, 1)]

theorem rawRowCheck3858 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form5 = rawRow3858 := by decide +kernel

def row3858 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

theorem rowCheck3858 : row3858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3858 := by decide +kernel

theorem rowEval3858 (x : Key → ℝ) : Integer.Sparse.eval row3858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3858, Integer.Sparse.eval_collectBalanced, rawRowCheck3858]

def rawRow3859 : Integer.Sparse Key := [(key585, -1), (key579, -1), (key420, -1), (key240, -1), (key407, -1), (key237, -1), (key579, 2), (key410, 2), (key240, 2), (key603, 1), (key594, 1), (key452, 1), (key252, 1), (key436, 1), (key249, 1), (key594, -1), (key569, -1), (key468, -1), (key268, -1), (key389, -1), (key252, -1), (key597, -2), (key444, -2), (key262, -2), (key597, 1), (key574, 1), (key471, 1), (key273, 1), (key399, 1), (key262, 1)]

theorem rawRowCheck3859 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form5 = rawRow3859 := by decide +kernel

def row3859 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

theorem rowCheck3859 : row3859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3859 := by decide +kernel

theorem rowEval3859 (x : Key → ℝ) : Integer.Sparse.eval row3859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3859, Integer.Sparse.eval_collectBalanced, rawRowCheck3859]

def rawRow3860 : Integer.Sparse Key := [(key240, -1), (key240, -1), (key410, -1), (key410, -1), (key420, -1), (key420, -1), (key237, 2), (key407, 2), (key407, 2), (key268, 1), (key268, 1), (key468, 1), (key468, 1), (key477, 1), (key477, 1), (key249, -1), (key249, -1), (key386, -1), (key386, -1), (key436, -1), (key436, -1), (key273, -2), (key471, -2), (key471, -2), (key262, 1), (key262, 1), (key399, 1), (key399, 1), (key444, 1), (key444, 1)]

theorem rawRowCheck3860 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow3860 := by decide +kernel

def row3860 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key262, 2), (key268, 2), (key273, -2), (key386, -2), (key399, 2), (key407, 4), (key410, -2), (key420, -2), (key436, -2), (key444, 2), (key468, 2), (key471, -4), (key477, 2)]

theorem rowCheck3860 : row3860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3860 := by decide +kernel

theorem rowEval3860 (x : Key → ℝ) : Integer.Sparse.eval row3860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3860, Integer.Sparse.eval_collectBalanced, rawRowCheck3860]

def rawRow3861 : Integer.Sparse Key := [(key410, -1), (key420, -1), (key240, -1), (key420, -1), (key240, -1), (key410, -1), (key407, 2), (key237, 2), (key407, 2), (key468, 1), (key477, 1), (key268, 1), (key477, 1), (key268, 1), (key468, 1), (key386, -1), (key436, -1), (key249, -1), (key436, -1), (key249, -1), (key386, -1), (key471, -2), (key273, -2), (key471, -2), (key399, 1), (key444, 1), (key262, 1), (key444, 1), (key262, 1), (key399, 1)]

theorem rawRowCheck3861 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow3861 := by decide +kernel

def row3861 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key262, 2), (key268, 2), (key273, -2), (key386, -2), (key399, 2), (key407, 4), (key410, -2), (key420, -2), (key436, -2), (key444, 2), (key468, 2), (key471, -4), (key477, 2)]

theorem rowCheck3861 : row3861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3861 := by decide +kernel

theorem rowEval3861 (x : Key → ℝ) : Integer.Sparse.eval row3861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3861, Integer.Sparse.eval_collectBalanced, rawRowCheck3861]

def rawRow3862 : Integer.Sparse Key := [(key420, -1), (key410, -1), (key420, -1), (key240, -1), (key410, -1), (key240, -1), (key407, 2), (key407, 2), (key237, 2), (key477, 1), (key468, 1), (key477, 1), (key268, 1), (key468, 1), (key268, 1), (key436, -1), (key386, -1), (key436, -1), (key249, -1), (key386, -1), (key249, -1), (key471, -2), (key471, -2), (key273, -2), (key444, 1), (key399, 1), (key444, 1), (key262, 1), (key399, 1), (key262, 1)]

theorem rawRowCheck3862 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow3862 := by decide +kernel

def row3862 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key262, 2), (key268, 2), (key273, -2), (key386, -2), (key399, 2), (key407, 4), (key410, -2), (key420, -2), (key436, -2), (key444, 2), (key468, 2), (key471, -4), (key477, 2)]

theorem rowCheck3862 : row3862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3862 := by decide +kernel

theorem rowEval3862 (x : Key → ℝ) : Integer.Sparse.eval row3862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3862, Integer.Sparse.eval_collectBalanced, rawRowCheck3862]

def rawRow3863 : Integer.Sparse Key := [(key249, -1), (key252, -1), (key436, -1), (key594, -1), (key452, -1), (key603, -1), (key262, 2), (key444, 2), (key597, 2), (key237, 1), (key240, 1), (key407, 1), (key579, 1), (key420, 1), (key585, 1), (key262, -1), (key273, -1), (key399, -1), (key574, -1), (key471, -1), (key597, -1), (key240, -2), (key410, -2), (key579, -2), (key252, 1), (key268, 1), (key389, 1), (key569, 1), (key468, 1), (key594, 1)]

theorem rawRowCheck3863 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form5 = rawRow3863 := by decide +kernel

def row3863 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

theorem rowCheck3863 : row3863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3863 := by decide +kernel

theorem rowEval3863 (x : Key → ℝ) : Integer.Sparse.eval row3863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3863, Integer.Sparse.eval_collectBalanced, rawRowCheck3863]

def rawRow3864 : Integer.Sparse Key := [(key252, -1), (key249, -1), (key594, -1), (key436, -1), (key603, -1), (key452, -1), (key262, 2), (key597, 2), (key444, 2), (key240, 1), (key237, 1), (key579, 1), (key407, 1), (key585, 1), (key420, 1), (key273, -1), (key262, -1), (key574, -1), (key399, -1), (key597, -1), (key471, -1), (key240, -2), (key579, -2), (key410, -2), (key268, 1), (key252, 1), (key569, 1), (key389, 1), (key594, 1), (key468, 1)]

theorem rawRowCheck3864 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form5 = rawRow3864 := by decide +kernel

def row3864 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

theorem rowCheck3864 : row3864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3864 := by decide +kernel

theorem rowEval3864 (x : Key → ℝ) : Integer.Sparse.eval row3864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3864, Integer.Sparse.eval_collectBalanced, rawRowCheck3864]

def rawRow3865 : Integer.Sparse Key := [(key436, -1), (key452, -1), (key249, -1), (key603, -1), (key252, -1), (key594, -1), (key444, 2), (key262, 2), (key597, 2), (key407, 1), (key420, 1), (key237, 1), (key585, 1), (key240, 1), (key579, 1), (key399, -1), (key471, -1), (key262, -1), (key597, -1), (key273, -1), (key574, -1), (key410, -2), (key240, -2), (key579, -2), (key389, 1), (key468, 1), (key252, 1), (key594, 1), (key268, 1), (key569, 1)]

theorem rawRowCheck3865 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form5 = rawRow3865 := by decide +kernel

def row3865 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

theorem rowCheck3865 : row3865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3865 := by decide +kernel

theorem rowEval3865 (x : Key → ℝ) : Integer.Sparse.eval row3865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3865, Integer.Sparse.eval_collectBalanced, rawRowCheck3865]

def rawRow3866 : Integer.Sparse Key := [(key452, -1), (key436, -1), (key603, -1), (key249, -1), (key594, -1), (key252, -1), (key444, 2), (key597, 2), (key262, 2), (key420, 1), (key407, 1), (key585, 1), (key237, 1), (key579, 1), (key240, 1), (key471, -1), (key399, -1), (key597, -1), (key262, -1), (key574, -1), (key273, -1), (key410, -2), (key579, -2), (key240, -2), (key468, 1), (key389, 1), (key594, 1), (key252, 1), (key569, 1), (key268, 1)]

theorem rawRowCheck3866 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form5 = rawRow3866 := by decide +kernel

def row3866 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

theorem rowCheck3866 : row3866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3866 := by decide +kernel

theorem rowEval3866 (x : Key → ℝ) : Integer.Sparse.eval row3866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3866, Integer.Sparse.eval_collectBalanced, rawRowCheck3866]

def rawRow3867 : Integer.Sparse Key := [(key594, -1), (key603, -1), (key252, -1), (key452, -1), (key249, -1), (key436, -1), (key597, 2), (key262, 2), (key444, 2), (key579, 1), (key585, 1), (key240, 1), (key420, 1), (key237, 1), (key407, 1), (key574, -1), (key597, -1), (key273, -1), (key471, -1), (key262, -1), (key399, -1), (key579, -2), (key240, -2), (key410, -2), (key569, 1), (key594, 1), (key268, 1), (key468, 1), (key252, 1), (key389, 1)]

theorem rawRowCheck3867 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form5 = rawRow3867 := by decide +kernel

def row3867 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

theorem rowCheck3867 : row3867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3867 := by decide +kernel

theorem rowEval3867 (x : Key → ℝ) : Integer.Sparse.eval row3867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3867, Integer.Sparse.eval_collectBalanced, rawRowCheck3867]

def rawRow3868 : Integer.Sparse Key := [(key603, -1), (key594, -1), (key452, -1), (key252, -1), (key436, -1), (key249, -1), (key597, 2), (key444, 2), (key262, 2), (key585, 1), (key579, 1), (key420, 1), (key240, 1), (key407, 1), (key237, 1), (key597, -1), (key574, -1), (key471, -1), (key273, -1), (key399, -1), (key262, -1), (key579, -2), (key410, -2), (key240, -2), (key594, 1), (key569, 1), (key468, 1), (key268, 1), (key389, 1), (key252, 1)]

theorem rawRowCheck3868 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form5 = rawRow3868 := by decide +kernel

def row3868 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

theorem rowCheck3868 : row3868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3868 := by decide +kernel

theorem rowEval3868 (x : Key → ℝ) : Integer.Sparse.eval row3868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3868, Integer.Sparse.eval_collectBalanced, rawRowCheck3868]

def rawRow3869 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key320, -1), (key444, -1), (key330, -1), (key452, -1), (key249, 2), (key317, 2), (key436, 2), (key268, 1), (key273, 1), (key336, 1), (key471, 1), (key342, 1), (key477, 1), (key237, -1), (key249, -1), (key303, -1), (key386, -1), (key317, -1), (key407, -1), (key268, -2), (key336, -2), (key468, -2), (key240, 1), (key252, 1), (key306, 1), (key389, 1), (key320, 1), (key410, 1)]

theorem rawRowCheck3869 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form5 = rawRow3869 := by decide +kernel

def row3869 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

theorem rowCheck3869 : row3869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3869 := by decide +kernel

theorem rowEval3869 (x : Key → ℝ) : Integer.Sparse.eval row3869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3869, Integer.Sparse.eval_collectBalanced, rawRowCheck3869]

def rawRow3870 : Integer.Sparse Key := [(key262, -1), (key252, -1), (key444, -1), (key320, -1), (key452, -1), (key330, -1), (key249, 2), (key436, 2), (key317, 2), (key273, 1), (key268, 1), (key471, 1), (key336, 1), (key477, 1), (key342, 1), (key249, -1), (key237, -1), (key386, -1), (key303, -1), (key407, -1), (key317, -1), (key268, -2), (key468, -2), (key336, -2), (key252, 1), (key240, 1), (key389, 1), (key306, 1), (key410, 1), (key320, 1)]

theorem rawRowCheck3870 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form5 = rawRow3870 := by decide +kernel

def row3870 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

theorem rowCheck3870 : row3870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3870 := by decide +kernel

theorem rowEval3870 (x : Key → ℝ) : Integer.Sparse.eval row3870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3870, Integer.Sparse.eval_collectBalanced, rawRowCheck3870]

def rawRow3871 : Integer.Sparse Key := [(key320, -1), (key330, -1), (key252, -1), (key452, -1), (key262, -1), (key444, -1), (key317, 2), (key249, 2), (key436, 2), (key336, 1), (key342, 1), (key268, 1), (key477, 1), (key273, 1), (key471, 1), (key303, -1), (key317, -1), (key237, -1), (key407, -1), (key249, -1), (key386, -1), (key336, -2), (key268, -2), (key468, -2), (key306, 1), (key320, 1), (key240, 1), (key410, 1), (key252, 1), (key389, 1)]

theorem rawRowCheck3871 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form5 = rawRow3871 := by decide +kernel

def row3871 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

theorem rowCheck3871 : row3871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3871 := by decide +kernel

theorem rowEval3871 (x : Key → ℝ) : Integer.Sparse.eval row3871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3871, Integer.Sparse.eval_collectBalanced, rawRowCheck3871]

def rawRow3872 : Integer.Sparse Key := [(key330, -1), (key320, -1), (key452, -1), (key252, -1), (key444, -1), (key262, -1), (key317, 2), (key436, 2), (key249, 2), (key342, 1), (key336, 1), (key477, 1), (key268, 1), (key471, 1), (key273, 1), (key317, -1), (key303, -1), (key407, -1), (key237, -1), (key386, -1), (key249, -1), (key336, -2), (key468, -2), (key268, -2), (key320, 1), (key306, 1), (key410, 1), (key240, 1), (key389, 1), (key252, 1)]

theorem rawRowCheck3872 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form5 = rawRow3872 := by decide +kernel

def row3872 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

theorem rowCheck3872 : row3872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3872 := by decide +kernel

theorem rowEval3872 (x : Key → ℝ) : Integer.Sparse.eval row3872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3872, Integer.Sparse.eval_collectBalanced, rawRowCheck3872]

def rawRow3873 : Integer.Sparse Key := [(key444, -1), (key452, -1), (key262, -1), (key330, -1), (key252, -1), (key320, -1), (key436, 2), (key249, 2), (key317, 2), (key471, 1), (key477, 1), (key273, 1), (key342, 1), (key268, 1), (key336, 1), (key386, -1), (key407, -1), (key249, -1), (key317, -1), (key237, -1), (key303, -1), (key468, -2), (key268, -2), (key336, -2), (key389, 1), (key410, 1), (key252, 1), (key320, 1), (key240, 1), (key306, 1)]

theorem rawRowCheck3873 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form5 = rawRow3873 := by decide +kernel

def row3873 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

theorem rowCheck3873 : row3873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3873 := by decide +kernel

theorem rowEval3873 (x : Key → ℝ) : Integer.Sparse.eval row3873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3873, Integer.Sparse.eval_collectBalanced, rawRowCheck3873]

def rawRow3874 : Integer.Sparse Key := [(key452, -1), (key444, -1), (key330, -1), (key262, -1), (key320, -1), (key252, -1), (key436, 2), (key317, 2), (key249, 2), (key477, 1), (key471, 1), (key342, 1), (key273, 1), (key336, 1), (key268, 1), (key407, -1), (key386, -1), (key317, -1), (key249, -1), (key303, -1), (key237, -1), (key468, -2), (key336, -2), (key268, -2), (key410, 1), (key389, 1), (key320, 1), (key252, 1), (key306, 1), (key240, 1)]

theorem rawRowCheck3874 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form5 = rawRow3874 := by decide +kernel

def row3874 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

theorem rowCheck3874 : row3874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3874 := by decide +kernel

theorem rowEval3874 (x : Key → ℝ) : Integer.Sparse.eval row3874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3874, Integer.Sparse.eval_collectBalanced, rawRowCheck3874]

def rawRow3875 : Integer.Sparse Key := [(key268, -1), (key268, -1), (key468, -1), (key468, -1), (key477, -1), (key477, -1), (key273, 2), (key471, 2), (key471, 2), (key240, 1), (key240, 1), (key410, 1), (key410, 1), (key420, 1), (key420, 1), (key262, -1), (key262, -1), (key399, -1), (key399, -1), (key444, -1), (key444, -1), (key237, -2), (key407, -2), (key407, -2), (key249, 1), (key249, 1), (key386, 1), (key386, 1), (key436, 1), (key436, 1)]

theorem rawRowCheck3875 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow3875 := by decide +kernel

def row3875 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key262, -2), (key268, -2), (key273, 2), (key386, 2), (key399, -2), (key407, -4), (key410, 2), (key420, 2), (key436, 2), (key444, -2), (key468, -2), (key471, 4), (key477, -2)]

theorem rowCheck3875 : row3875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3875 := by decide +kernel

theorem rowEval3875 (x : Key → ℝ) : Integer.Sparse.eval row3875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3875, Integer.Sparse.eval_collectBalanced, rawRowCheck3875]

def rawRow3876 : Integer.Sparse Key := [(key468, -1), (key477, -1), (key268, -1), (key477, -1), (key268, -1), (key468, -1), (key471, 2), (key273, 2), (key471, 2), (key410, 1), (key420, 1), (key240, 1), (key420, 1), (key240, 1), (key410, 1), (key399, -1), (key444, -1), (key262, -1), (key444, -1), (key262, -1), (key399, -1), (key407, -2), (key237, -2), (key407, -2), (key386, 1), (key436, 1), (key249, 1), (key436, 1), (key249, 1), (key386, 1)]

theorem rawRowCheck3876 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow3876 := by decide +kernel

def row3876 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key262, -2), (key268, -2), (key273, 2), (key386, 2), (key399, -2), (key407, -4), (key410, 2), (key420, 2), (key436, 2), (key444, -2), (key468, -2), (key471, 4), (key477, -2)]

theorem rowCheck3876 : row3876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3876 := by decide +kernel

theorem rowEval3876 (x : Key → ℝ) : Integer.Sparse.eval row3876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3876, Integer.Sparse.eval_collectBalanced, rawRowCheck3876]

def rawRow3877 : Integer.Sparse Key := [(key477, -1), (key468, -1), (key477, -1), (key268, -1), (key468, -1), (key268, -1), (key471, 2), (key471, 2), (key273, 2), (key420, 1), (key410, 1), (key420, 1), (key240, 1), (key410, 1), (key240, 1), (key444, -1), (key399, -1), (key444, -1), (key262, -1), (key399, -1), (key262, -1), (key407, -2), (key407, -2), (key237, -2), (key436, 1), (key386, 1), (key436, 1), (key249, 1), (key386, 1), (key249, 1)]

theorem rawRowCheck3877 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow3877 := by decide +kernel

def row3877 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key262, -2), (key268, -2), (key273, 2), (key386, 2), (key399, -2), (key407, -4), (key410, 2), (key420, 2), (key436, 2), (key444, -2), (key468, -2), (key471, 4), (key477, -2)]

theorem rowCheck3877 : row3877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3877 := by decide +kernel

theorem rowEval3877 (x : Key → ℝ) : Integer.Sparse.eval row3877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3877, Integer.Sparse.eval_collectBalanced, rawRowCheck3877]

def rawRow3878 : Integer.Sparse Key := [(key268, -1), (key273, -1), (key336, -1), (key471, -1), (key342, -1), (key477, -1), (key268, 2), (key336, 2), (key468, 2), (key252, 1), (key262, 1), (key320, 1), (key444, 1), (key330, 1), (key452, 1), (key240, -1), (key252, -1), (key306, -1), (key389, -1), (key320, -1), (key410, -1), (key249, -2), (key317, -2), (key436, -2), (key237, 1), (key249, 1), (key303, 1), (key386, 1), (key317, 1), (key407, 1)]

theorem rawRowCheck3878 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form5 = rawRow3878 := by decide +kernel

def row3878 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

theorem rowCheck3878 : row3878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3878 := by decide +kernel

theorem rowEval3878 (x : Key → ℝ) : Integer.Sparse.eval row3878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3878, Integer.Sparse.eval_collectBalanced, rawRowCheck3878]

def rawRow3879 : Integer.Sparse Key := [(key273, -1), (key268, -1), (key471, -1), (key336, -1), (key477, -1), (key342, -1), (key268, 2), (key468, 2), (key336, 2), (key262, 1), (key252, 1), (key444, 1), (key320, 1), (key452, 1), (key330, 1), (key252, -1), (key240, -1), (key389, -1), (key306, -1), (key410, -1), (key320, -1), (key249, -2), (key436, -2), (key317, -2), (key249, 1), (key237, 1), (key386, 1), (key303, 1), (key407, 1), (key317, 1)]

theorem rawRowCheck3879 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form5 = rawRow3879 := by decide +kernel

def row3879 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

theorem rowCheck3879 : row3879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3879 := by decide +kernel

theorem rowEval3879 (x : Key → ℝ) : Integer.Sparse.eval row3879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3879, Integer.Sparse.eval_collectBalanced, rawRowCheck3879]

def rawRow3880 : Integer.Sparse Key := [(key336, -1), (key342, -1), (key268, -1), (key477, -1), (key273, -1), (key471, -1), (key336, 2), (key268, 2), (key468, 2), (key320, 1), (key330, 1), (key252, 1), (key452, 1), (key262, 1), (key444, 1), (key306, -1), (key320, -1), (key240, -1), (key410, -1), (key252, -1), (key389, -1), (key317, -2), (key249, -2), (key436, -2), (key303, 1), (key317, 1), (key237, 1), (key407, 1), (key249, 1), (key386, 1)]

theorem rawRowCheck3880 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form5 = rawRow3880 := by decide +kernel

def row3880 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

theorem rowCheck3880 : row3880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3880 := by decide +kernel

theorem rowEval3880 (x : Key → ℝ) : Integer.Sparse.eval row3880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3880, Integer.Sparse.eval_collectBalanced, rawRowCheck3880]

def rawRow3881 : Integer.Sparse Key := [(key342, -1), (key336, -1), (key477, -1), (key268, -1), (key471, -1), (key273, -1), (key336, 2), (key468, 2), (key268, 2), (key330, 1), (key320, 1), (key452, 1), (key252, 1), (key444, 1), (key262, 1), (key320, -1), (key306, -1), (key410, -1), (key240, -1), (key389, -1), (key252, -1), (key317, -2), (key436, -2), (key249, -2), (key317, 1), (key303, 1), (key407, 1), (key237, 1), (key386, 1), (key249, 1)]

theorem rawRowCheck3881 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form5 = rawRow3881 := by decide +kernel

def row3881 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

theorem rowCheck3881 : row3881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3881 := by decide +kernel

theorem rowEval3881 (x : Key → ℝ) : Integer.Sparse.eval row3881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3881, Integer.Sparse.eval_collectBalanced, rawRowCheck3881]

def rawRow3882 : Integer.Sparse Key := [(key471, -1), (key477, -1), (key273, -1), (key342, -1), (key268, -1), (key336, -1), (key468, 2), (key268, 2), (key336, 2), (key444, 1), (key452, 1), (key262, 1), (key330, 1), (key252, 1), (key320, 1), (key389, -1), (key410, -1), (key252, -1), (key320, -1), (key240, -1), (key306, -1), (key436, -2), (key249, -2), (key317, -2), (key386, 1), (key407, 1), (key249, 1), (key317, 1), (key237, 1), (key303, 1)]

theorem rawRowCheck3882 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form5 = rawRow3882 := by decide +kernel

def row3882 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

theorem rowCheck3882 : row3882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3882 := by decide +kernel

theorem rowEval3882 (x : Key → ℝ) : Integer.Sparse.eval row3882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3882, Integer.Sparse.eval_collectBalanced, rawRowCheck3882]

def rawRow3883 : Integer.Sparse Key := [(key477, -1), (key471, -1), (key342, -1), (key273, -1), (key336, -1), (key268, -1), (key468, 2), (key336, 2), (key268, 2), (key452, 1), (key444, 1), (key330, 1), (key262, 1), (key320, 1), (key252, 1), (key410, -1), (key389, -1), (key320, -1), (key252, -1), (key306, -1), (key240, -1), (key436, -2), (key317, -2), (key249, -2), (key407, 1), (key386, 1), (key317, 1), (key249, 1), (key303, 1), (key237, 1)]

theorem rawRowCheck3883 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form5 = rawRow3883 := by decide +kernel

def row3883 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

theorem rowCheck3883 : row3883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3883 := by decide +kernel

theorem rowEval3883 (x : Key → ℝ) : Integer.Sparse.eval row3883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3883, Integer.Sparse.eval_collectBalanced, rawRowCheck3883]

def rawRow3884 : Integer.Sparse Key := [(key1406, -2), (key1413, -2), (key1909, -2), (key1409, 2), (key1413, 2), (key1587, 2), (key1434, 2), (key1438, 2), (key1924, 2), (key1438, -6), (key1476, -2), (key1478, -2), (key1687, -2), (key1478, 6)]

theorem rawRowCheck3884 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form6 = rawRow3884 := by decide +kernel

def row3884 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

theorem rowCheck3884 : row3884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3884 := by decide +kernel

theorem rowEval3884 (x : Key → ℝ) : Integer.Sparse.eval row3884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3884, Integer.Sparse.eval_collectBalanced, rawRowCheck3884]

def rawRow3885 : Integer.Sparse Key := [(key1413, -2), (key1406, -2), (key1909, -2), (key1413, 2), (key1409, 2), (key1587, 2), (key1438, 2), (key1434, 2), (key1924, 2), (key1438, -6), (key1478, -2), (key1476, -2), (key1687, -2), (key1478, 6)]

theorem rawRowCheck3885 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form6 = rawRow3885 := by decide +kernel

def row3885 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

theorem rowCheck3885 : row3885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3885 := by decide +kernel

theorem rowEval3885 (x : Key → ℝ) : Integer.Sparse.eval row3885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3885, Integer.Sparse.eval_collectBalanced, rawRowCheck3885]

def rawRow3886 : Integer.Sparse Key := [(key1406, -2), (key1909, -2), (key1413, -2), (key1409, 2), (key1587, 2), (key1413, 2), (key1434, 2), (key1924, 2), (key1438, 2), (key1438, -6), (key1476, -2), (key1687, -2), (key1478, -2), (key1478, 6)]

theorem rawRowCheck3886 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form6 = rawRow3886 := by decide +kernel

def row3886 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

theorem rowCheck3886 : row3886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3886 := by decide +kernel

theorem rowEval3886 (x : Key → ℝ) : Integer.Sparse.eval row3886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3886, Integer.Sparse.eval_collectBalanced, rawRowCheck3886]

def rawRow3887 : Integer.Sparse Key := [(key1909, -2), (key1406, -2), (key1413, -2), (key1587, 2), (key1409, 2), (key1413, 2), (key1924, 2), (key1434, 2), (key1438, 2), (key1438, -6), (key1687, -2), (key1476, -2), (key1478, -2), (key1478, 6)]

theorem rawRowCheck3887 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form6 = rawRow3887 := by decide +kernel

def row3887 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

theorem rowCheck3887 : row3887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3887 := by decide +kernel

theorem rowEval3887 (x : Key → ℝ) : Integer.Sparse.eval row3887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3887, Integer.Sparse.eval_collectBalanced, rawRowCheck3887]

def rawRow3888 : Integer.Sparse Key := [(key1413, -2), (key1909, -2), (key1406, -2), (key1413, 2), (key1587, 2), (key1409, 2), (key1438, 2), (key1924, 2), (key1434, 2), (key1438, -6), (key1478, -2), (key1687, -2), (key1476, -2), (key1478, 6)]

theorem rawRowCheck3888 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form6 = rawRow3888 := by decide +kernel

def row3888 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

theorem rowCheck3888 : row3888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3888 := by decide +kernel

theorem rowEval3888 (x : Key → ℝ) : Integer.Sparse.eval row3888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3888, Integer.Sparse.eval_collectBalanced, rawRowCheck3888]

def rawRow3889 : Integer.Sparse Key := [(key1909, -2), (key1413, -2), (key1406, -2), (key1587, 2), (key1413, 2), (key1409, 2), (key1924, 2), (key1438, 2), (key1434, 2), (key1438, -6), (key1687, -2), (key1478, -2), (key1476, -2), (key1478, 6)]

theorem rawRowCheck3889 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form6 = rawRow3889 := by decide +kernel

def row3889 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

theorem rowCheck3889 : row3889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3889 := by decide +kernel

theorem rowEval3889 (x : Key → ℝ) : Integer.Sparse.eval row3889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3889, Integer.Sparse.eval_collectBalanced, rawRowCheck3889]

def rawRow3890 : Integer.Sparse Key := [(key1409, -2), (key1409, -2), (key1907, -2), (key1406, 2), (key1406, 2), (key1583, 2), (key1438, 2), (key1438, 2), (key1924, 2), (key1434, -6), (key1478, -2), (key1478, -2), (key1687, -2), (key1476, 6)]

theorem rawRowCheck3890 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow3890 := by decide +kernel

def row3890 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -6), (key1438, 4), (key1476, 6), (key1478, -4), (key1583, 2), (key1687, -2), (key1907, -2), (key1924, 2)]

theorem rowCheck3890 : row3890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3890 := by decide +kernel

theorem rowEval3890 (x : Key → ℝ) : Integer.Sparse.eval row3890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3890, Integer.Sparse.eval_collectBalanced, rawRowCheck3890]

def rawRow3891 : Integer.Sparse Key := [(key1409, -2), (key1907, -2), (key1409, -2), (key1406, 2), (key1583, 2), (key1406, 2), (key1438, 2), (key1924, 2), (key1438, 2), (key1434, -6), (key1478, -2), (key1687, -2), (key1478, -2), (key1476, 6)]

theorem rawRowCheck3891 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow3891 := by decide +kernel

def row3891 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -6), (key1438, 4), (key1476, 6), (key1478, -4), (key1583, 2), (key1687, -2), (key1907, -2), (key1924, 2)]

theorem rowCheck3891 : row3891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3891 := by decide +kernel

theorem rowEval3891 (x : Key → ℝ) : Integer.Sparse.eval row3891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3891, Integer.Sparse.eval_collectBalanced, rawRowCheck3891]

def rawRow3892 : Integer.Sparse Key := [(key1907, -2), (key1409, -2), (key1409, -2), (key1583, 2), (key1406, 2), (key1406, 2), (key1924, 2), (key1438, 2), (key1438, 2), (key1434, -6), (key1687, -2), (key1478, -2), (key1478, -2), (key1476, 6)]

theorem rawRowCheck3892 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow3892 := by decide +kernel

def row3892 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -6), (key1438, 4), (key1476, 6), (key1478, -4), (key1583, 2), (key1687, -2), (key1907, -2), (key1924, 2)]

theorem rowCheck3892 : row3892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3892 := by decide +kernel

theorem rowEval3892 (x : Key → ℝ) : Integer.Sparse.eval row3892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3892, Integer.Sparse.eval_collectBalanced, rawRowCheck3892]

def rawRow3893 : Integer.Sparse Key := [(key1434, -2), (key1438, -2), (key1924, -2), (key1476, 2), (key1478, 2), (key1687, 2), (key1406, 2), (key1413, 2), (key1909, 2), (key1478, -6), (key1409, -2), (key1413, -2), (key1587, -2), (key1438, 6)]

theorem rawRowCheck3893 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form6 = rawRow3893 := by decide +kernel

def row3893 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

theorem rowCheck3893 : row3893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3893 := by decide +kernel

theorem rowEval3893 (x : Key → ℝ) : Integer.Sparse.eval row3893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3893, Integer.Sparse.eval_collectBalanced, rawRowCheck3893]

def rawRow3894 : Integer.Sparse Key := [(key1438, -2), (key1434, -2), (key1924, -2), (key1478, 2), (key1476, 2), (key1687, 2), (key1413, 2), (key1406, 2), (key1909, 2), (key1478, -6), (key1413, -2), (key1409, -2), (key1587, -2), (key1438, 6)]

theorem rawRowCheck3894 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form6 = rawRow3894 := by decide +kernel

def row3894 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

theorem rowCheck3894 : row3894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3894 := by decide +kernel

theorem rowEval3894 (x : Key → ℝ) : Integer.Sparse.eval row3894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3894, Integer.Sparse.eval_collectBalanced, rawRowCheck3894]

def rawRow3895 : Integer.Sparse Key := [(key1434, -2), (key1924, -2), (key1438, -2), (key1476, 2), (key1687, 2), (key1478, 2), (key1406, 2), (key1909, 2), (key1413, 2), (key1478, -6), (key1409, -2), (key1587, -2), (key1413, -2), (key1438, 6)]

theorem rawRowCheck3895 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form6 = rawRow3895 := by decide +kernel

def row3895 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

theorem rowCheck3895 : row3895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3895 := by decide +kernel

theorem rowEval3895 (x : Key → ℝ) : Integer.Sparse.eval row3895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3895, Integer.Sparse.eval_collectBalanced, rawRowCheck3895]

def rawRow3896 : Integer.Sparse Key := [(key1924, -2), (key1434, -2), (key1438, -2), (key1687, 2), (key1476, 2), (key1478, 2), (key1909, 2), (key1406, 2), (key1413, 2), (key1478, -6), (key1587, -2), (key1409, -2), (key1413, -2), (key1438, 6)]

theorem rawRowCheck3896 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form6 = rawRow3896 := by decide +kernel

def row3896 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

theorem rowCheck3896 : row3896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3896 := by decide +kernel

theorem rowEval3896 (x : Key → ℝ) : Integer.Sparse.eval row3896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3896, Integer.Sparse.eval_collectBalanced, rawRowCheck3896]

def rawRow3897 : Integer.Sparse Key := [(key1438, -2), (key1924, -2), (key1434, -2), (key1478, 2), (key1687, 2), (key1476, 2), (key1413, 2), (key1909, 2), (key1406, 2), (key1478, -6), (key1413, -2), (key1587, -2), (key1409, -2), (key1438, 6)]

theorem rawRowCheck3897 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form6 = rawRow3897 := by decide +kernel

def row3897 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

theorem rowCheck3897 : row3897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3897 := by decide +kernel

theorem rowEval3897 (x : Key → ℝ) : Integer.Sparse.eval row3897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3897, Integer.Sparse.eval_collectBalanced, rawRowCheck3897]

def rawRow3898 : Integer.Sparse Key := [(key1924, -2), (key1438, -2), (key1434, -2), (key1687, 2), (key1478, 2), (key1476, 2), (key1909, 2), (key1413, 2), (key1406, 2), (key1478, -6), (key1587, -2), (key1413, -2), (key1409, -2), (key1438, 6)]

theorem rawRowCheck3898 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form6 = rawRow3898 := by decide +kernel

def row3898 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

theorem rowCheck3898 : row3898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3898 := by decide +kernel

theorem rowEval3898 (x : Key → ℝ) : Integer.Sparse.eval row3898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3898, Integer.Sparse.eval_collectBalanced, rawRowCheck3898]

def rawRow3899 : Integer.Sparse Key := [(key1409, -2), (key1476, -2), (key1907, -2), (key1406, 2), (key1434, 2), (key1583, 2), (key1413, 2), (key1478, 2), (key1909, 2), (key1406, -6), (key1413, -2), (key1438, -2), (key1587, -2), (key1409, 6)]

theorem rawRowCheck3899 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form6 = rawRow3899 := by decide +kernel

def row3899 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

theorem rowCheck3899 : row3899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3899 := by decide +kernel

theorem rowEval3899 (x : Key → ℝ) : Integer.Sparse.eval row3899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3899, Integer.Sparse.eval_collectBalanced, rawRowCheck3899]

def rawRow3900 : Integer.Sparse Key := [(key1476, -2), (key1409, -2), (key1907, -2), (key1434, 2), (key1406, 2), (key1583, 2), (key1478, 2), (key1413, 2), (key1909, 2), (key1406, -6), (key1438, -2), (key1413, -2), (key1587, -2), (key1409, 6)]

theorem rawRowCheck3900 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form6 = rawRow3900 := by decide +kernel

def row3900 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

theorem rowCheck3900 : row3900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3900 := by decide +kernel

theorem rowEval3900 (x : Key → ℝ) : Integer.Sparse.eval row3900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3900, Integer.Sparse.eval_collectBalanced, rawRowCheck3900]

def rawRow3901 : Integer.Sparse Key := [(key1409, -2), (key1907, -2), (key1476, -2), (key1406, 2), (key1583, 2), (key1434, 2), (key1413, 2), (key1909, 2), (key1478, 2), (key1406, -6), (key1413, -2), (key1587, -2), (key1438, -2), (key1409, 6)]

theorem rawRowCheck3901 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form6 = rawRow3901 := by decide +kernel

def row3901 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

theorem rowCheck3901 : row3901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3901 := by decide +kernel

theorem rowEval3901 (x : Key → ℝ) : Integer.Sparse.eval row3901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3901, Integer.Sparse.eval_collectBalanced, rawRowCheck3901]

def rawRow3902 : Integer.Sparse Key := [(key1907, -2), (key1409, -2), (key1476, -2), (key1583, 2), (key1406, 2), (key1434, 2), (key1909, 2), (key1413, 2), (key1478, 2), (key1406, -6), (key1587, -2), (key1413, -2), (key1438, -2), (key1409, 6)]

theorem rawRowCheck3902 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form6 = rawRow3902 := by decide +kernel

def row3902 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

theorem rowCheck3902 : row3902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3902 := by decide +kernel

theorem rowEval3902 (x : Key → ℝ) : Integer.Sparse.eval row3902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3902, Integer.Sparse.eval_collectBalanced, rawRowCheck3902]

def rawRow3903 : Integer.Sparse Key := [(key1476, -2), (key1907, -2), (key1409, -2), (key1434, 2), (key1583, 2), (key1406, 2), (key1478, 2), (key1909, 2), (key1413, 2), (key1406, -6), (key1438, -2), (key1587, -2), (key1413, -2), (key1409, 6)]

theorem rawRowCheck3903 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form6 = rawRow3903 := by decide +kernel

def row3903 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

theorem rowCheck3903 : row3903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3903 := by decide +kernel

theorem rowEval3903 (x : Key → ℝ) : Integer.Sparse.eval row3903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3903, Integer.Sparse.eval_collectBalanced, rawRowCheck3903]

def rawRow3904 : Integer.Sparse Key := [(key1907, -2), (key1476, -2), (key1409, -2), (key1583, 2), (key1434, 2), (key1406, 2), (key1909, 2), (key1478, 2), (key1413, 2), (key1406, -6), (key1587, -2), (key1438, -2), (key1413, -2), (key1409, 6)]

theorem rawRowCheck3904 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form6 = rawRow3904 := by decide +kernel

def row3904 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

theorem rowCheck3904 : row3904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3904 := by decide +kernel

theorem rowEval3904 (x : Key → ℝ) : Integer.Sparse.eval row3904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3904, Integer.Sparse.eval_collectBalanced, rawRowCheck3904]

def rawRow3905 : Integer.Sparse Key := [(key1438, -2), (key1438, -2), (key1924, -2), (key1478, 2), (key1478, 2), (key1687, 2), (key1409, 2), (key1409, 2), (key1907, 2), (key1476, -6), (key1406, -2), (key1406, -2), (key1583, -2), (key1434, 6)]

theorem rawRowCheck3905 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow3905 := by decide +kernel

def row3905 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 6), (key1438, -4), (key1476, -6), (key1478, 4), (key1583, -2), (key1687, 2), (key1907, 2), (key1924, -2)]

theorem rowCheck3905 : row3905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3905 := by decide +kernel

theorem rowEval3905 (x : Key → ℝ) : Integer.Sparse.eval row3905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3905, Integer.Sparse.eval_collectBalanced, rawRowCheck3905]

def rawRow3906 : Integer.Sparse Key := [(key1438, -2), (key1924, -2), (key1438, -2), (key1478, 2), (key1687, 2), (key1478, 2), (key1409, 2), (key1907, 2), (key1409, 2), (key1476, -6), (key1406, -2), (key1583, -2), (key1406, -2), (key1434, 6)]

theorem rawRowCheck3906 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow3906 := by decide +kernel

def row3906 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 6), (key1438, -4), (key1476, -6), (key1478, 4), (key1583, -2), (key1687, 2), (key1907, 2), (key1924, -2)]

theorem rowCheck3906 : row3906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3906 := by decide +kernel

theorem rowEval3906 (x : Key → ℝ) : Integer.Sparse.eval row3906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3906, Integer.Sparse.eval_collectBalanced, rawRowCheck3906]

def rawRow3907 : Integer.Sparse Key := [(key1924, -2), (key1438, -2), (key1438, -2), (key1687, 2), (key1478, 2), (key1478, 2), (key1907, 2), (key1409, 2), (key1409, 2), (key1476, -6), (key1583, -2), (key1406, -2), (key1406, -2), (key1434, 6)]

theorem rawRowCheck3907 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow3907 := by decide +kernel

def row3907 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 6), (key1438, -4), (key1476, -6), (key1478, 4), (key1583, -2), (key1687, 2), (key1907, 2), (key1924, -2)]

theorem rowCheck3907 : row3907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3907 := by decide +kernel

theorem rowEval3907 (x : Key → ℝ) : Integer.Sparse.eval row3907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3907, Integer.Sparse.eval_collectBalanced, rawRowCheck3907]

def rawRow3908 : Integer.Sparse Key := [(key1413, -2), (key1478, -2), (key1909, -2), (key1413, 2), (key1438, 2), (key1587, 2), (key1409, 2), (key1476, 2), (key1907, 2), (key1409, -6), (key1406, -2), (key1434, -2), (key1583, -2), (key1406, 6)]

theorem rawRowCheck3908 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form6 = rawRow3908 := by decide +kernel

def row3908 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

theorem rowCheck3908 : row3908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3908 := by decide +kernel

theorem rowEval3908 (x : Key → ℝ) : Integer.Sparse.eval row3908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3908, Integer.Sparse.eval_collectBalanced, rawRowCheck3908]

def rawRow3909 : Integer.Sparse Key := [(key1478, -2), (key1413, -2), (key1909, -2), (key1438, 2), (key1413, 2), (key1587, 2), (key1476, 2), (key1409, 2), (key1907, 2), (key1409, -6), (key1434, -2), (key1406, -2), (key1583, -2), (key1406, 6)]

theorem rawRowCheck3909 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form6 = rawRow3909 := by decide +kernel

def row3909 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

theorem rowCheck3909 : row3909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3909 := by decide +kernel

theorem rowEval3909 (x : Key → ℝ) : Integer.Sparse.eval row3909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3909, Integer.Sparse.eval_collectBalanced, rawRowCheck3909]

def rawRow3910 : Integer.Sparse Key := [(key1413, -2), (key1909, -2), (key1478, -2), (key1413, 2), (key1587, 2), (key1438, 2), (key1409, 2), (key1907, 2), (key1476, 2), (key1409, -6), (key1406, -2), (key1583, -2), (key1434, -2), (key1406, 6)]

theorem rawRowCheck3910 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form6 = rawRow3910 := by decide +kernel

def row3910 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

theorem rowCheck3910 : row3910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3910 := by decide +kernel

theorem rowEval3910 (x : Key → ℝ) : Integer.Sparse.eval row3910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3910, Integer.Sparse.eval_collectBalanced, rawRowCheck3910]

def rawRow3911 : Integer.Sparse Key := [(key1909, -2), (key1413, -2), (key1478, -2), (key1587, 2), (key1413, 2), (key1438, 2), (key1907, 2), (key1409, 2), (key1476, 2), (key1409, -6), (key1583, -2), (key1406, -2), (key1434, -2), (key1406, 6)]

theorem rawRowCheck3911 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form6 = rawRow3911 := by decide +kernel

def row3911 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

theorem rowCheck3911 : row3911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3911 := by decide +kernel

theorem rowEval3911 (x : Key → ℝ) : Integer.Sparse.eval row3911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3911, Integer.Sparse.eval_collectBalanced, rawRowCheck3911]

def rawRow3912 : Integer.Sparse Key := [(key1478, -2), (key1909, -2), (key1413, -2), (key1438, 2), (key1587, 2), (key1413, 2), (key1476, 2), (key1907, 2), (key1409, 2), (key1409, -6), (key1434, -2), (key1583, -2), (key1406, -2), (key1406, 6)]

theorem rawRowCheck3912 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form6 = rawRow3912 := by decide +kernel

def row3912 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

theorem rowCheck3912 : row3912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3912 := by decide +kernel

theorem rowEval3912 (x : Key → ℝ) : Integer.Sparse.eval row3912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3912, Integer.Sparse.eval_collectBalanced, rawRowCheck3912]

def rawRow3913 : Integer.Sparse Key := [(key1909, -2), (key1478, -2), (key1413, -2), (key1587, 2), (key1438, 2), (key1413, 2), (key1907, 2), (key1476, 2), (key1409, 2), (key1409, -6), (key1583, -2), (key1434, -2), (key1406, -2), (key1406, 6)]

theorem rawRowCheck3913 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form6 = rawRow3913 := by decide +kernel

def row3913 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

theorem rowCheck3913 : row3913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3913 := by decide +kernel

theorem rowEval3913 (x : Key → ℝ) : Integer.Sparse.eval row3913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3913, Integer.Sparse.eval_collectBalanced, rawRowCheck3913]

def rawRow3914 : Integer.Sparse Key := [(key317, -2), (key320, -2), (key330, -2), (key303, 1), (key306, 1), (key317, 1), (key336, 1), (key330, 1), (key342, 1), (key407, 2), (key410, 2), (key420, 2), (key237, -1), (key240, -1), (key407, -1), (key579, -1), (key420, -1), (key585, -1), (key386, -1), (key389, -1), (key436, -1), (key468, -1), (key452, -1), (key477, -1), (key249, 1), (key252, 1), (key436, 1), (key594, 1), (key452, 1), (key603, 1)]

theorem rawRowCheck3914 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form7 = rawRow3914 := by decide +kernel

def row3914 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

theorem rowCheck3914 : row3914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3914 := by decide +kernel

theorem rowEval3914 (x : Key → ℝ) : Integer.Sparse.eval row3914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3914, Integer.Sparse.eval_collectBalanced, rawRowCheck3914]

def rawRow3915 : Integer.Sparse Key := [(key320, -2), (key317, -2), (key330, -2), (key306, 1), (key303, 1), (key336, 1), (key317, 1), (key342, 1), (key330, 1), (key410, 2), (key407, 2), (key420, 2), (key240, -1), (key237, -1), (key579, -1), (key407, -1), (key585, -1), (key420, -1), (key389, -1), (key386, -1), (key468, -1), (key436, -1), (key477, -1), (key452, -1), (key252, 1), (key249, 1), (key594, 1), (key436, 1), (key603, 1), (key452, 1)]

theorem rawRowCheck3915 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form7 = rawRow3915 := by decide +kernel

def row3915 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

theorem rowCheck3915 : row3915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3915 := by decide +kernel

theorem rowEval3915 (x : Key → ℝ) : Integer.Sparse.eval row3915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3915, Integer.Sparse.eval_collectBalanced, rawRowCheck3915]

def rawRow3916 : Integer.Sparse Key := [(key317, -2), (key330, -2), (key320, -2), (key317, 1), (key330, 1), (key303, 1), (key342, 1), (key306, 1), (key336, 1), (key407, 2), (key420, 2), (key410, 2), (key407, -1), (key420, -1), (key237, -1), (key585, -1), (key240, -1), (key579, -1), (key436, -1), (key452, -1), (key386, -1), (key477, -1), (key389, -1), (key468, -1), (key436, 1), (key452, 1), (key249, 1), (key603, 1), (key252, 1), (key594, 1)]

theorem rawRowCheck3916 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form7 = rawRow3916 := by decide +kernel

def row3916 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

theorem rowCheck3916 : row3916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3916 := by decide +kernel

theorem rowEval3916 (x : Key → ℝ) : Integer.Sparse.eval row3916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3916, Integer.Sparse.eval_collectBalanced, rawRowCheck3916]

def rawRow3917 : Integer.Sparse Key := [(key330, -2), (key317, -2), (key320, -2), (key330, 1), (key317, 1), (key342, 1), (key303, 1), (key336, 1), (key306, 1), (key420, 2), (key407, 2), (key410, 2), (key420, -1), (key407, -1), (key585, -1), (key237, -1), (key579, -1), (key240, -1), (key452, -1), (key436, -1), (key477, -1), (key386, -1), (key468, -1), (key389, -1), (key452, 1), (key436, 1), (key603, 1), (key249, 1), (key594, 1), (key252, 1)]

theorem rawRowCheck3917 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form7 = rawRow3917 := by decide +kernel

def row3917 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

theorem rowCheck3917 : row3917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3917 := by decide +kernel

theorem rowEval3917 (x : Key → ℝ) : Integer.Sparse.eval row3917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3917, Integer.Sparse.eval_collectBalanced, rawRowCheck3917]

def rawRow3918 : Integer.Sparse Key := [(key320, -2), (key330, -2), (key317, -2), (key336, 1), (key342, 1), (key306, 1), (key330, 1), (key303, 1), (key317, 1), (key410, 2), (key420, 2), (key407, 2), (key579, -1), (key585, -1), (key240, -1), (key420, -1), (key237, -1), (key407, -1), (key468, -1), (key477, -1), (key389, -1), (key452, -1), (key386, -1), (key436, -1), (key594, 1), (key603, 1), (key252, 1), (key452, 1), (key249, 1), (key436, 1)]

theorem rawRowCheck3918 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form7 = rawRow3918 := by decide +kernel

def row3918 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

theorem rowCheck3918 : row3918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3918 := by decide +kernel

theorem rowEval3918 (x : Key → ℝ) : Integer.Sparse.eval row3918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3918, Integer.Sparse.eval_collectBalanced, rawRowCheck3918]

def rawRow3919 : Integer.Sparse Key := [(key330, -2), (key320, -2), (key317, -2), (key342, 1), (key336, 1), (key330, 1), (key306, 1), (key317, 1), (key303, 1), (key420, 2), (key410, 2), (key407, 2), (key585, -1), (key579, -1), (key420, -1), (key240, -1), (key407, -1), (key237, -1), (key477, -1), (key468, -1), (key452, -1), (key389, -1), (key436, -1), (key386, -1), (key603, 1), (key594, 1), (key452, 1), (key252, 1), (key436, 1), (key249, 1)]

theorem rawRowCheck3919 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form7 = rawRow3919 := by decide +kernel

def row3919 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

theorem rowCheck3919 : row3919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3919 := by decide +kernel

theorem rowEval3919 (x : Key → ℝ) : Integer.Sparse.eval row3919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3919, Integer.Sparse.eval_collectBalanced, rawRowCheck3919]

def rawRow3920 : Integer.Sparse Key := [(key336, -2), (key336, -2), (key342, -2), (key306, 1), (key306, 1), (key320, 1), (key320, 1), (key330, 1), (key330, 1), (key579, 2), (key579, 2), (key585, 2), (key240, -1), (key240, -1), (key410, -1), (key410, -1), (key420, -1), (key420, -1), (key569, -1), (key569, -1), (key594, -1), (key594, -1), (key603, -1), (key603, -1), (key268, 1), (key268, 1), (key468, 1), (key468, 1), (key477, 1), (key477, 1)]

theorem rawRowCheck3920 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form7 = rawRow3920 := by decide +kernel

def row3920 : Integer.Sparse Key := [(key240, -2), (key268, 2), (key306, 2), (key320, 2), (key330, 2), (key336, -4), (key342, -2), (key410, -2), (key420, -2), (key468, 2), (key477, 2), (key569, -2), (key579, 4), (key585, 2), (key594, -2), (key603, -2)]

theorem rowCheck3920 : row3920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3920 := by decide +kernel

theorem rowEval3920 (x : Key → ℝ) : Integer.Sparse.eval row3920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3920, Integer.Sparse.eval_collectBalanced, rawRowCheck3920]

def rawRow3921 : Integer.Sparse Key := [(key336, -2), (key342, -2), (key336, -2), (key320, 1), (key330, 1), (key306, 1), (key330, 1), (key306, 1), (key320, 1), (key579, 2), (key585, 2), (key579, 2), (key410, -1), (key420, -1), (key240, -1), (key420, -1), (key240, -1), (key410, -1), (key594, -1), (key603, -1), (key569, -1), (key603, -1), (key569, -1), (key594, -1), (key468, 1), (key477, 1), (key268, 1), (key477, 1), (key268, 1), (key468, 1)]

theorem rawRowCheck3921 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form7 = rawRow3921 := by decide +kernel

def row3921 : Integer.Sparse Key := [(key240, -2), (key268, 2), (key306, 2), (key320, 2), (key330, 2), (key336, -4), (key342, -2), (key410, -2), (key420, -2), (key468, 2), (key477, 2), (key569, -2), (key579, 4), (key585, 2), (key594, -2), (key603, -2)]

theorem rowCheck3921 : row3921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3921 := by decide +kernel

theorem rowEval3921 (x : Key → ℝ) : Integer.Sparse.eval row3921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3921, Integer.Sparse.eval_collectBalanced, rawRowCheck3921]

def rawRow3922 : Integer.Sparse Key := [(key342, -2), (key336, -2), (key336, -2), (key330, 1), (key320, 1), (key330, 1), (key306, 1), (key320, 1), (key306, 1), (key585, 2), (key579, 2), (key579, 2), (key420, -1), (key410, -1), (key420, -1), (key240, -1), (key410, -1), (key240, -1), (key603, -1), (key594, -1), (key603, -1), (key569, -1), (key594, -1), (key569, -1), (key477, 1), (key468, 1), (key477, 1), (key268, 1), (key468, 1), (key268, 1)]

theorem rawRowCheck3922 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form7 = rawRow3922 := by decide +kernel

def row3922 : Integer.Sparse Key := [(key240, -2), (key268, 2), (key306, 2), (key320, 2), (key330, 2), (key336, -4), (key342, -2), (key410, -2), (key420, -2), (key468, 2), (key477, 2), (key569, -2), (key579, 4), (key585, 2), (key594, -2), (key603, -2)]

theorem rowCheck3922 : row3922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3922 := by decide +kernel

theorem rowEval3922 (x : Key → ℝ) : Integer.Sparse.eval row3922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3922, Integer.Sparse.eval_collectBalanced, rawRowCheck3922]

def rawRow3923 : Integer.Sparse Key := [(key407, -2), (key410, -2), (key420, -2), (key386, 1), (key389, 1), (key436, 1), (key468, 1), (key452, 1), (key477, 1), (key317, 2), (key320, 2), (key330, 2), (key249, -1), (key252, -1), (key436, -1), (key594, -1), (key452, -1), (key603, -1), (key303, -1), (key306, -1), (key317, -1), (key336, -1), (key330, -1), (key342, -1), (key237, 1), (key240, 1), (key407, 1), (key579, 1), (key420, 1), (key585, 1)]

theorem rawRowCheck3923 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form7 = rawRow3923 := by decide +kernel

def row3923 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

theorem rowCheck3923 : row3923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3923 := by decide +kernel

theorem rowEval3923 (x : Key → ℝ) : Integer.Sparse.eval row3923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3923, Integer.Sparse.eval_collectBalanced, rawRowCheck3923]

def rawRow3924 : Integer.Sparse Key := [(key410, -2), (key407, -2), (key420, -2), (key389, 1), (key386, 1), (key468, 1), (key436, 1), (key477, 1), (key452, 1), (key320, 2), (key317, 2), (key330, 2), (key252, -1), (key249, -1), (key594, -1), (key436, -1), (key603, -1), (key452, -1), (key306, -1), (key303, -1), (key336, -1), (key317, -1), (key342, -1), (key330, -1), (key240, 1), (key237, 1), (key579, 1), (key407, 1), (key585, 1), (key420, 1)]

theorem rawRowCheck3924 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form7 = rawRow3924 := by decide +kernel

def row3924 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

theorem rowCheck3924 : row3924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3924 := by decide +kernel

theorem rowEval3924 (x : Key → ℝ) : Integer.Sparse.eval row3924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3924, Integer.Sparse.eval_collectBalanced, rawRowCheck3924]

def rawRow3925 : Integer.Sparse Key := [(key407, -2), (key420, -2), (key410, -2), (key436, 1), (key452, 1), (key386, 1), (key477, 1), (key389, 1), (key468, 1), (key317, 2), (key330, 2), (key320, 2), (key436, -1), (key452, -1), (key249, -1), (key603, -1), (key252, -1), (key594, -1), (key317, -1), (key330, -1), (key303, -1), (key342, -1), (key306, -1), (key336, -1), (key407, 1), (key420, 1), (key237, 1), (key585, 1), (key240, 1), (key579, 1)]

theorem rawRowCheck3925 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form7 = rawRow3925 := by decide +kernel

def row3925 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

theorem rowCheck3925 : row3925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3925 := by decide +kernel

theorem rowEval3925 (x : Key → ℝ) : Integer.Sparse.eval row3925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3925, Integer.Sparse.eval_collectBalanced, rawRowCheck3925]

def rawRow3926 : Integer.Sparse Key := [(key420, -2), (key407, -2), (key410, -2), (key452, 1), (key436, 1), (key477, 1), (key386, 1), (key468, 1), (key389, 1), (key330, 2), (key317, 2), (key320, 2), (key452, -1), (key436, -1), (key603, -1), (key249, -1), (key594, -1), (key252, -1), (key330, -1), (key317, -1), (key342, -1), (key303, -1), (key336, -1), (key306, -1), (key420, 1), (key407, 1), (key585, 1), (key237, 1), (key579, 1), (key240, 1)]

theorem rawRowCheck3926 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form7 = rawRow3926 := by decide +kernel

def row3926 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

theorem rowCheck3926 : row3926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3926 := by decide +kernel

theorem rowEval3926 (x : Key → ℝ) : Integer.Sparse.eval row3926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3926, Integer.Sparse.eval_collectBalanced, rawRowCheck3926]

def rawRow3927 : Integer.Sparse Key := [(key410, -2), (key420, -2), (key407, -2), (key468, 1), (key477, 1), (key389, 1), (key452, 1), (key386, 1), (key436, 1), (key320, 2), (key330, 2), (key317, 2), (key594, -1), (key603, -1), (key252, -1), (key452, -1), (key249, -1), (key436, -1), (key336, -1), (key342, -1), (key306, -1), (key330, -1), (key303, -1), (key317, -1), (key579, 1), (key585, 1), (key240, 1), (key420, 1), (key237, 1), (key407, 1)]

theorem rawRowCheck3927 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form7 = rawRow3927 := by decide +kernel

def row3927 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

theorem rowCheck3927 : row3927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3927 := by decide +kernel

theorem rowEval3927 (x : Key → ℝ) : Integer.Sparse.eval row3927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3927, Integer.Sparse.eval_collectBalanced, rawRowCheck3927]

def rawRow3928 : Integer.Sparse Key := [(key420, -2), (key410, -2), (key407, -2), (key477, 1), (key468, 1), (key452, 1), (key389, 1), (key436, 1), (key386, 1), (key330, 2), (key320, 2), (key317, 2), (key603, -1), (key594, -1), (key452, -1), (key252, -1), (key436, -1), (key249, -1), (key342, -1), (key336, -1), (key330, -1), (key306, -1), (key317, -1), (key303, -1), (key585, 1), (key579, 1), (key420, 1), (key240, 1), (key407, 1), (key237, 1)]

theorem rawRowCheck3928 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form7 = rawRow3928 := by decide +kernel

def row3928 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

theorem rowCheck3928 : row3928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3928 := by decide +kernel

theorem rowEval3928 (x : Key → ℝ) : Integer.Sparse.eval row3928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3928, Integer.Sparse.eval_collectBalanced, rawRowCheck3928]

def rawRow3929 : Integer.Sparse Key := [(key468, -2), (key471, -2), (key477, -2), (key389, 1), (key399, 1), (key410, 1), (key444, 1), (key420, 1), (key452, 1), (key594, 2), (key597, 2), (key603, 2), (key252, -1), (key262, -1), (key320, -1), (key444, -1), (key330, -1), (key452, -1), (key569, -1), (key574, -1), (key579, -1), (key597, -1), (key585, -1), (key603, -1), (key268, 1), (key273, 1), (key336, 1), (key471, 1), (key342, 1), (key477, 1)]

theorem rawRowCheck3929 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form7 = rawRow3929 := by decide +kernel

def row3929 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

theorem rowCheck3929 : row3929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3929 := by decide +kernel

theorem rowEval3929 (x : Key → ℝ) : Integer.Sparse.eval row3929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3929, Integer.Sparse.eval_collectBalanced, rawRowCheck3929]

def rawRow3930 : Integer.Sparse Key := [(key471, -2), (key468, -2), (key477, -2), (key399, 1), (key389, 1), (key444, 1), (key410, 1), (key452, 1), (key420, 1), (key597, 2), (key594, 2), (key603, 2), (key262, -1), (key252, -1), (key444, -1), (key320, -1), (key452, -1), (key330, -1), (key574, -1), (key569, -1), (key597, -1), (key579, -1), (key603, -1), (key585, -1), (key273, 1), (key268, 1), (key471, 1), (key336, 1), (key477, 1), (key342, 1)]

theorem rawRowCheck3930 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form7 = rawRow3930 := by decide +kernel

def row3930 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

theorem rowCheck3930 : row3930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3930 := by decide +kernel

theorem rowEval3930 (x : Key → ℝ) : Integer.Sparse.eval row3930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3930, Integer.Sparse.eval_collectBalanced, rawRowCheck3930]

def rawRow3931 : Integer.Sparse Key := [(key468, -2), (key477, -2), (key471, -2), (key410, 1), (key420, 1), (key389, 1), (key452, 1), (key399, 1), (key444, 1), (key594, 2), (key603, 2), (key597, 2), (key320, -1), (key330, -1), (key252, -1), (key452, -1), (key262, -1), (key444, -1), (key579, -1), (key585, -1), (key569, -1), (key603, -1), (key574, -1), (key597, -1), (key336, 1), (key342, 1), (key268, 1), (key477, 1), (key273, 1), (key471, 1)]

theorem rawRowCheck3931 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form7 = rawRow3931 := by decide +kernel

def row3931 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

theorem rowCheck3931 : row3931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3931 := by decide +kernel

theorem rowEval3931 (x : Key → ℝ) : Integer.Sparse.eval row3931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3931, Integer.Sparse.eval_collectBalanced, rawRowCheck3931]

def rawRow3932 : Integer.Sparse Key := [(key477, -2), (key468, -2), (key471, -2), (key420, 1), (key410, 1), (key452, 1), (key389, 1), (key444, 1), (key399, 1), (key603, 2), (key594, 2), (key597, 2), (key330, -1), (key320, -1), (key452, -1), (key252, -1), (key444, -1), (key262, -1), (key585, -1), (key579, -1), (key603, -1), (key569, -1), (key597, -1), (key574, -1), (key342, 1), (key336, 1), (key477, 1), (key268, 1), (key471, 1), (key273, 1)]

theorem rawRowCheck3932 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form7 = rawRow3932 := by decide +kernel

def row3932 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

theorem rowCheck3932 : row3932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3932 := by decide +kernel

theorem rowEval3932 (x : Key → ℝ) : Integer.Sparse.eval row3932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3932, Integer.Sparse.eval_collectBalanced, rawRowCheck3932]

def rawRow3933 : Integer.Sparse Key := [(key471, -2), (key477, -2), (key468, -2), (key444, 1), (key452, 1), (key399, 1), (key420, 1), (key389, 1), (key410, 1), (key597, 2), (key603, 2), (key594, 2), (key444, -1), (key452, -1), (key262, -1), (key330, -1), (key252, -1), (key320, -1), (key597, -1), (key603, -1), (key574, -1), (key585, -1), (key569, -1), (key579, -1), (key471, 1), (key477, 1), (key273, 1), (key342, 1), (key268, 1), (key336, 1)]

theorem rawRowCheck3933 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form7 = rawRow3933 := by decide +kernel

def row3933 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

theorem rowCheck3933 : row3933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3933 := by decide +kernel

theorem rowEval3933 (x : Key → ℝ) : Integer.Sparse.eval row3933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3933, Integer.Sparse.eval_collectBalanced, rawRowCheck3933]

def rawRow3934 : Integer.Sparse Key := [(key477, -2), (key471, -2), (key468, -2), (key452, 1), (key444, 1), (key420, 1), (key399, 1), (key410, 1), (key389, 1), (key603, 2), (key597, 2), (key594, 2), (key452, -1), (key444, -1), (key330, -1), (key262, -1), (key320, -1), (key252, -1), (key603, -1), (key597, -1), (key585, -1), (key574, -1), (key579, -1), (key569, -1), (key477, 1), (key471, 1), (key342, 1), (key273, 1), (key336, 1), (key268, 1)]

theorem rawRowCheck3934 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form7 = rawRow3934 := by decide +kernel

def row3934 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

theorem rowCheck3934 : row3934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3934 := by decide +kernel

theorem rowEval3934 (x : Key → ℝ) : Integer.Sparse.eval row3934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3934, Integer.Sparse.eval_collectBalanced, rawRowCheck3934]

def rawRow3935 : Integer.Sparse Key := [(key579, -2), (key579, -2), (key585, -2), (key569, 1), (key569, 1), (key594, 1), (key594, 1), (key603, 1), (key603, 1), (key336, 2), (key336, 2), (key342, 2), (key268, -1), (key268, -1), (key468, -1), (key468, -1), (key477, -1), (key477, -1), (key306, -1), (key306, -1), (key320, -1), (key320, -1), (key330, -1), (key330, -1), (key240, 1), (key240, 1), (key410, 1), (key410, 1), (key420, 1), (key420, 1)]

theorem rawRowCheck3935 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form7 = rawRow3935 := by decide +kernel

def row3935 : Integer.Sparse Key := [(key240, 2), (key268, -2), (key306, -2), (key320, -2), (key330, -2), (key336, 4), (key342, 2), (key410, 2), (key420, 2), (key468, -2), (key477, -2), (key569, 2), (key579, -4), (key585, -2), (key594, 2), (key603, 2)]

theorem rowCheck3935 : row3935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3935 := by decide +kernel

theorem rowEval3935 (x : Key → ℝ) : Integer.Sparse.eval row3935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3935, Integer.Sparse.eval_collectBalanced, rawRowCheck3935]

def rawRow3936 : Integer.Sparse Key := [(key579, -2), (key585, -2), (key579, -2), (key594, 1), (key603, 1), (key569, 1), (key603, 1), (key569, 1), (key594, 1), (key336, 2), (key342, 2), (key336, 2), (key468, -1), (key477, -1), (key268, -1), (key477, -1), (key268, -1), (key468, -1), (key320, -1), (key330, -1), (key306, -1), (key330, -1), (key306, -1), (key320, -1), (key410, 1), (key420, 1), (key240, 1), (key420, 1), (key240, 1), (key410, 1)]

theorem rawRowCheck3936 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form7 = rawRow3936 := by decide +kernel

def row3936 : Integer.Sparse Key := [(key240, 2), (key268, -2), (key306, -2), (key320, -2), (key330, -2), (key336, 4), (key342, 2), (key410, 2), (key420, 2), (key468, -2), (key477, -2), (key569, 2), (key579, -4), (key585, -2), (key594, 2), (key603, 2)]

theorem rowCheck3936 : row3936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3936 := by decide +kernel

theorem rowEval3936 (x : Key → ℝ) : Integer.Sparse.eval row3936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3936, Integer.Sparse.eval_collectBalanced, rawRowCheck3936]

def rawRow3937 : Integer.Sparse Key := [(key585, -2), (key579, -2), (key579, -2), (key603, 1), (key594, 1), (key603, 1), (key569, 1), (key594, 1), (key569, 1), (key342, 2), (key336, 2), (key336, 2), (key477, -1), (key468, -1), (key477, -1), (key268, -1), (key468, -1), (key268, -1), (key330, -1), (key320, -1), (key330, -1), (key306, -1), (key320, -1), (key306, -1), (key420, 1), (key410, 1), (key420, 1), (key240, 1), (key410, 1), (key240, 1)]

theorem rawRowCheck3937 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form7 = rawRow3937 := by decide +kernel

def row3937 : Integer.Sparse Key := [(key240, 2), (key268, -2), (key306, -2), (key320, -2), (key330, -2), (key336, 4), (key342, 2), (key410, 2), (key420, 2), (key468, -2), (key477, -2), (key569, 2), (key579, -4), (key585, -2), (key594, 2), (key603, 2)]

theorem rowCheck3937 : row3937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3937 := by decide +kernel

theorem rowEval3937 (x : Key → ℝ) : Integer.Sparse.eval row3937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3937, Integer.Sparse.eval_collectBalanced, rawRowCheck3937]

def rawRow3938 : Integer.Sparse Key := [(key594, -2), (key597, -2), (key603, -2), (key569, 1), (key574, 1), (key579, 1), (key597, 1), (key585, 1), (key603, 1), (key468, 2), (key471, 2), (key477, 2), (key268, -1), (key273, -1), (key336, -1), (key471, -1), (key342, -1), (key477, -1), (key389, -1), (key399, -1), (key410, -1), (key444, -1), (key420, -1), (key452, -1), (key252, 1), (key262, 1), (key320, 1), (key444, 1), (key330, 1), (key452, 1)]

theorem rawRowCheck3938 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form7 = rawRow3938 := by decide +kernel

def row3938 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

theorem rowCheck3938 : row3938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3938 := by decide +kernel

theorem rowEval3938 (x : Key → ℝ) : Integer.Sparse.eval row3938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3938, Integer.Sparse.eval_collectBalanced, rawRowCheck3938]

def rawRow3939 : Integer.Sparse Key := [(key597, -2), (key594, -2), (key603, -2), (key574, 1), (key569, 1), (key597, 1), (key579, 1), (key603, 1), (key585, 1), (key471, 2), (key468, 2), (key477, 2), (key273, -1), (key268, -1), (key471, -1), (key336, -1), (key477, -1), (key342, -1), (key399, -1), (key389, -1), (key444, -1), (key410, -1), (key452, -1), (key420, -1), (key262, 1), (key252, 1), (key444, 1), (key320, 1), (key452, 1), (key330, 1)]

theorem rawRowCheck3939 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form7 = rawRow3939 := by decide +kernel

def row3939 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

theorem rowCheck3939 : row3939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3939 := by decide +kernel

theorem rowEval3939 (x : Key → ℝ) : Integer.Sparse.eval row3939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3939, Integer.Sparse.eval_collectBalanced, rawRowCheck3939]

def rawRow3940 : Integer.Sparse Key := [(key594, -2), (key603, -2), (key597, -2), (key579, 1), (key585, 1), (key569, 1), (key603, 1), (key574, 1), (key597, 1), (key468, 2), (key477, 2), (key471, 2), (key336, -1), (key342, -1), (key268, -1), (key477, -1), (key273, -1), (key471, -1), (key410, -1), (key420, -1), (key389, -1), (key452, -1), (key399, -1), (key444, -1), (key320, 1), (key330, 1), (key252, 1), (key452, 1), (key262, 1), (key444, 1)]

theorem rawRowCheck3940 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form7 = rawRow3940 := by decide +kernel

def row3940 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

theorem rowCheck3940 : row3940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3940 := by decide +kernel

theorem rowEval3940 (x : Key → ℝ) : Integer.Sparse.eval row3940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3940, Integer.Sparse.eval_collectBalanced, rawRowCheck3940]

def rawRow3941 : Integer.Sparse Key := [(key603, -2), (key594, -2), (key597, -2), (key585, 1), (key579, 1), (key603, 1), (key569, 1), (key597, 1), (key574, 1), (key477, 2), (key468, 2), (key471, 2), (key342, -1), (key336, -1), (key477, -1), (key268, -1), (key471, -1), (key273, -1), (key420, -1), (key410, -1), (key452, -1), (key389, -1), (key444, -1), (key399, -1), (key330, 1), (key320, 1), (key452, 1), (key252, 1), (key444, 1), (key262, 1)]

theorem rawRowCheck3941 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form7 = rawRow3941 := by decide +kernel

def row3941 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

theorem rowCheck3941 : row3941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3941 := by decide +kernel

theorem rowEval3941 (x : Key → ℝ) : Integer.Sparse.eval row3941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3941, Integer.Sparse.eval_collectBalanced, rawRowCheck3941]

def rawRow3942 : Integer.Sparse Key := [(key597, -2), (key603, -2), (key594, -2), (key597, 1), (key603, 1), (key574, 1), (key585, 1), (key569, 1), (key579, 1), (key471, 2), (key477, 2), (key468, 2), (key471, -1), (key477, -1), (key273, -1), (key342, -1), (key268, -1), (key336, -1), (key444, -1), (key452, -1), (key399, -1), (key420, -1), (key389, -1), (key410, -1), (key444, 1), (key452, 1), (key262, 1), (key330, 1), (key252, 1), (key320, 1)]

theorem rawRowCheck3942 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form7 = rawRow3942 := by decide +kernel

def row3942 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

theorem rowCheck3942 : row3942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3942 := by decide +kernel

theorem rowEval3942 (x : Key → ℝ) : Integer.Sparse.eval row3942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3942, Integer.Sparse.eval_collectBalanced, rawRowCheck3942]

def rawRow3943 : Integer.Sparse Key := [(key603, -2), (key597, -2), (key594, -2), (key603, 1), (key597, 1), (key585, 1), (key574, 1), (key579, 1), (key569, 1), (key477, 2), (key471, 2), (key468, 2), (key477, -1), (key471, -1), (key342, -1), (key273, -1), (key336, -1), (key268, -1), (key452, -1), (key444, -1), (key420, -1), (key399, -1), (key410, -1), (key389, -1), (key452, 1), (key444, 1), (key330, 1), (key262, 1), (key320, 1), (key252, 1)]

theorem rawRowCheck3943 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form7 = rawRow3943 := by decide +kernel

def row3943 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

theorem rowCheck3943 : row3943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3943 := by decide +kernel

theorem rowEval3943 (x : Key → ℝ) : Integer.Sparse.eval row3943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3943, Integer.Sparse.eval_collectBalanced, rawRowCheck3943]

def rawRow3944 : Integer.Sparse Key := [(key43, -2), (key46, -2), (key71, -2), (key46, 6), (key426, 2), (key429, 2), (key589, 2), (key209, -2), (key429, -2), (key457, -2), (key463, -6), (key214, 2), (key463, 2), (key480, 2)]

theorem rawRowCheck3944 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form8 = rawRow3944 := by decide +kernel

def row3944 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

theorem rowCheck3944 : row3944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3944 := by decide +kernel

theorem rowEval3944 (x : Key → ℝ) : Integer.Sparse.eval row3944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3944, Integer.Sparse.eval_collectBalanced, rawRowCheck3944]

def rawRow3945 : Integer.Sparse Key := [(key46, -2), (key43, -2), (key71, -2), (key46, 6), (key429, 2), (key426, 2), (key589, 2), (key209, -2), (key457, -2), (key429, -2), (key463, -6), (key214, 2), (key480, 2), (key463, 2)]

theorem rawRowCheck3945 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form8 = rawRow3945 := by decide +kernel

def row3945 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

theorem rowCheck3945 : row3945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3945 := by decide +kernel

theorem rowEval3945 (x : Key → ℝ) : Integer.Sparse.eval row3945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3945, Integer.Sparse.eval_collectBalanced, rawRowCheck3945]

def rawRow3946 : Integer.Sparse Key := [(key43, -2), (key71, -2), (key46, -2), (key46, 6), (key426, 2), (key589, 2), (key429, 2), (key429, -2), (key209, -2), (key457, -2), (key463, -6), (key463, 2), (key214, 2), (key480, 2)]

theorem rawRowCheck3946 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form8 = rawRow3946 := by decide +kernel

def row3946 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

theorem rowCheck3946 : row3946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3946 := by decide +kernel

theorem rowEval3946 (x : Key → ℝ) : Integer.Sparse.eval row3946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3946, Integer.Sparse.eval_collectBalanced, rawRowCheck3946]

def rawRow3947 : Integer.Sparse Key := [(key71, -2), (key43, -2), (key46, -2), (key46, 6), (key589, 2), (key426, 2), (key429, 2), (key429, -2), (key457, -2), (key209, -2), (key463, -6), (key463, 2), (key480, 2), (key214, 2)]

theorem rawRowCheck3947 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form8 = rawRow3947 := by decide +kernel

def row3947 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

theorem rowCheck3947 : row3947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3947 := by decide +kernel

theorem rowEval3947 (x : Key → ℝ) : Integer.Sparse.eval row3947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3947, Integer.Sparse.eval_collectBalanced, rawRowCheck3947]

def rawRow3948 : Integer.Sparse Key := [(key46, -2), (key71, -2), (key43, -2), (key46, 6), (key429, 2), (key589, 2), (key426, 2), (key457, -2), (key209, -2), (key429, -2), (key463, -6), (key480, 2), (key214, 2), (key463, 2)]

theorem rawRowCheck3948 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form8 = rawRow3948 := by decide +kernel

def row3948 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

theorem rowCheck3948 : row3948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3948 := by decide +kernel

theorem rowEval3948 (x : Key → ℝ) : Integer.Sparse.eval row3948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3948, Integer.Sparse.eval_collectBalanced, rawRowCheck3948]

def rawRow3949 : Integer.Sparse Key := [(key71, -2), (key46, -2), (key43, -2), (key46, 6), (key589, 2), (key429, 2), (key426, 2), (key457, -2), (key429, -2), (key209, -2), (key463, -6), (key480, 2), (key463, 2), (key214, 2)]

theorem rawRowCheck3949 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form8 = rawRow3949 := by decide +kernel

def row3949 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

theorem rowCheck3949 : row3949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3949 := by decide +kernel

theorem rowEval3949 (x : Key → ℝ) : Integer.Sparse.eval row3949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3949, Integer.Sparse.eval_collectBalanced, rawRowCheck3949]

def rawRow3950 : Integer.Sparse Key := [(key46, -2), (key46, -2), (key71, -2), (key43, 6), (key457, 2), (key457, 2), (key606, 2), (key206, -2), (key426, -2), (key426, -2), (key480, -6), (key214, 2), (key463, 2), (key463, 2)]

theorem rawRowCheck3950 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow3950 := by decide +kernel

def row3950 : Integer.Sparse Key := [(key43, 6), (key46, -4), (key71, -2), (key206, -2), (key214, 2), (key426, -4), (key457, 4), (key463, 4), (key480, -6), (key606, 2)]

theorem rowCheck3950 : row3950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3950 := by decide +kernel

theorem rowEval3950 (x : Key → ℝ) : Integer.Sparse.eval row3950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3950, Integer.Sparse.eval_collectBalanced, rawRowCheck3950]

def rawRow3951 : Integer.Sparse Key := [(key46, -2), (key71, -2), (key46, -2), (key43, 6), (key457, 2), (key606, 2), (key457, 2), (key426, -2), (key206, -2), (key426, -2), (key480, -6), (key463, 2), (key214, 2), (key463, 2)]

theorem rawRowCheck3951 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow3951 := by decide +kernel

def row3951 : Integer.Sparse Key := [(key43, 6), (key46, -4), (key71, -2), (key206, -2), (key214, 2), (key426, -4), (key457, 4), (key463, 4), (key480, -6), (key606, 2)]

theorem rowCheck3951 : row3951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3951 := by decide +kernel

theorem rowEval3951 (x : Key → ℝ) : Integer.Sparse.eval row3951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3951, Integer.Sparse.eval_collectBalanced, rawRowCheck3951]

def rawRow3952 : Integer.Sparse Key := [(key71, -2), (key46, -2), (key46, -2), (key43, 6), (key606, 2), (key457, 2), (key457, 2), (key426, -2), (key426, -2), (key206, -2), (key480, -6), (key463, 2), (key463, 2), (key214, 2)]

theorem rawRowCheck3952 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow3952 := by decide +kernel

def row3952 : Integer.Sparse Key := [(key43, 6), (key46, -4), (key71, -2), (key206, -2), (key214, 2), (key426, -4), (key457, 4), (key463, 4), (key480, -6), (key606, 2)]

theorem rowCheck3952 : row3952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3952 := by decide +kernel

theorem rowEval3952 (x : Key → ℝ) : Integer.Sparse.eval row3952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3952, Integer.Sparse.eval_collectBalanced, rawRowCheck3952]

def rawRow3953 : Integer.Sparse Key := [(key100, -2), (key103, -2), (key134, -2), (key112, 6), (key43, 2), (key46, 2), (key71, 2), (key214, -2), (key463, -2), (key480, -2), (key378, -6), (key209, 2), (key429, 2), (key457, 2)]

theorem rawRowCheck3953 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form8 = rawRow3953 := by decide +kernel

def row3953 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

theorem rowCheck3953 : row3953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3953 := by decide +kernel

theorem rowEval3953 (x : Key → ℝ) : Integer.Sparse.eval row3953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3953, Integer.Sparse.eval_collectBalanced, rawRowCheck3953]

def rawRow3954 : Integer.Sparse Key := [(key103, -2), (key100, -2), (key134, -2), (key112, 6), (key46, 2), (key43, 2), (key71, 2), (key214, -2), (key480, -2), (key463, -2), (key378, -6), (key209, 2), (key457, 2), (key429, 2)]

theorem rawRowCheck3954 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form8 = rawRow3954 := by decide +kernel

def row3954 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

theorem rowCheck3954 : row3954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3954 := by decide +kernel

theorem rowEval3954 (x : Key → ℝ) : Integer.Sparse.eval row3954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3954, Integer.Sparse.eval_collectBalanced, rawRowCheck3954]

def rawRow3955 : Integer.Sparse Key := [(key100, -2), (key134, -2), (key103, -2), (key112, 6), (key43, 2), (key71, 2), (key46, 2), (key463, -2), (key214, -2), (key480, -2), (key378, -6), (key429, 2), (key209, 2), (key457, 2)]

theorem rawRowCheck3955 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form8 = rawRow3955 := by decide +kernel

def row3955 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

theorem rowCheck3955 : row3955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3955 := by decide +kernel

theorem rowEval3955 (x : Key → ℝ) : Integer.Sparse.eval row3955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3955, Integer.Sparse.eval_collectBalanced, rawRowCheck3955]

def rawRow3956 : Integer.Sparse Key := [(key134, -2), (key100, -2), (key103, -2), (key112, 6), (key71, 2), (key43, 2), (key46, 2), (key463, -2), (key480, -2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key209, 2)]

theorem rawRowCheck3956 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form8 = rawRow3956 := by decide +kernel

def row3956 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

theorem rowCheck3956 : row3956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3956 := by decide +kernel

theorem rowEval3956 (x : Key → ℝ) : Integer.Sparse.eval row3956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3956, Integer.Sparse.eval_collectBalanced, rawRowCheck3956]

def rawRow3957 : Integer.Sparse Key := [(key103, -2), (key134, -2), (key100, -2), (key112, 6), (key46, 2), (key71, 2), (key43, 2), (key480, -2), (key214, -2), (key463, -2), (key378, -6), (key457, 2), (key209, 2), (key429, 2)]

theorem rawRowCheck3957 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form8 = rawRow3957 := by decide +kernel

def row3957 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

theorem rowCheck3957 : row3957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3957 := by decide +kernel

theorem rowEval3957 (x : Key → ℝ) : Integer.Sparse.eval row3957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3957, Integer.Sparse.eval_collectBalanced, rawRowCheck3957]

def rawRow3958 : Integer.Sparse Key := [(key134, -2), (key103, -2), (key100, -2), (key112, 6), (key71, 2), (key46, 2), (key43, 2), (key480, -2), (key463, -2), (key214, -2), (key378, -6), (key457, 2), (key429, 2), (key209, 2)]

theorem rawRowCheck3958 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form8 = rawRow3958 := by decide +kernel

def row3958 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

theorem rowCheck3958 : row3958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3958 := by decide +kernel

theorem rowEval3958 (x : Key → ℝ) : Integer.Sparse.eval row3958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3958, Integer.Sparse.eval_collectBalanced, rawRowCheck3958]

def rawRow3959 : Integer.Sparse Key := [(key103, -2), (key112, -2), (key134, -2), (key100, 6), (key171, 2), (key174, 2), (key179, 2), (key18, -2), (key375, -2), (key426, -2), (key457, -6), (key209, 2), (key378, 2), (key429, 2)]

theorem rawRowCheck3959 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form8 = rawRow3959 := by decide +kernel

def row3959 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key209, 2), (key375, -2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

theorem rowCheck3959 : row3959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3959 := by decide +kernel

theorem rowEval3959 (x : Key → ℝ) : Integer.Sparse.eval row3959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3959, Integer.Sparse.eval_collectBalanced, rawRowCheck3959]

def rawRow3960 : Integer.Sparse Key := [(key112, -2), (key103, -2), (key134, -2), (key100, 6), (key174, 2), (key171, 2), (key179, 2), (key18, -2), (key426, -2), (key375, -2), (key457, -6), (key209, 2), (key429, 2), (key378, 2)]

theorem rawRowCheck3960 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form8 = rawRow3960 := by decide +kernel

def row3960 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key209, 2), (key375, -2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

theorem rowCheck3960 : row3960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3960 := by decide +kernel

theorem rowEval3960 (x : Key → ℝ) : Integer.Sparse.eval row3960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3960, Integer.Sparse.eval_collectBalanced, rawRowCheck3960]

def rawRow3961 : Integer.Sparse Key := [(key103, -2), (key134, -2), (key112, -2), (key100, 6), (key171, 2), (key179, 2), (key174, 2), (key43, -2), (key206, -2), (key426, -2), (key457, -6), (key378, 2), (key209, 2), (key429, 2)]

theorem rawRowCheck3961 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form8 = rawRow3961 := by decide +kernel

def row3961 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key206, -2), (key209, 2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

theorem rowCheck3961 : row3961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3961 := by decide +kernel

theorem rowEval3961 (x : Key → ℝ) : Integer.Sparse.eval row3961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3961, Integer.Sparse.eval_collectBalanced, rawRowCheck3961]

def rawRow3962 : Integer.Sparse Key := [(key134, -2), (key103, -2), (key112, -2), (key100, 6), (key179, 2), (key171, 2), (key174, 2), (key43, -2), (key426, -2), (key206, -2), (key457, -6), (key378, 2), (key429, 2), (key209, 2)]

theorem rawRowCheck3962 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form8 = rawRow3962 := by decide +kernel

def row3962 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key206, -2), (key209, 2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

theorem rowCheck3962 : row3962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3962 := by decide +kernel

theorem rowEval3962 (x : Key → ℝ) : Integer.Sparse.eval row3962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3962, Integer.Sparse.eval_collectBalanced, rawRowCheck3962]

def rawRow3963 : Integer.Sparse Key := [(key112, -2), (key134, -2), (key103, -2), (key100, 6), (key174, 2), (key179, 2), (key171, 2), (key100, -2), (key18, -2), (key375, -2), (key457, -6), (key429, 2), (key209, 2), (key378, 2)]

theorem rawRowCheck3963 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form8 = rawRow3963 := by decide +kernel

def row3963 : Integer.Sparse Key := [(key18, -2), (key100, 4), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key209, 2), (key375, -2), (key378, 2), (key429, 2), (key457, -6)]

theorem rowCheck3963 : row3963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3963 := by decide +kernel

theorem rowEval3963 (x : Key → ℝ) : Integer.Sparse.eval row3963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3963, Integer.Sparse.eval_collectBalanced, rawRowCheck3963]

def rawRow3964 : Integer.Sparse Key := [(key134, -2), (key112, -2), (key103, -2), (key100, 6), (key179, 2), (key174, 2), (key171, 2), (key100, -2), (key43, -2), (key206, -2), (key457, -6), (key429, 2), (key378, 2), (key209, 2)]

theorem rawRowCheck3964 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form8 = rawRow3964 := by decide +kernel

def row3964 : Integer.Sparse Key := [(key43, -2), (key100, 4), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key206, -2), (key209, 2), (key378, 2), (key429, 2), (key457, -6)]

theorem rowCheck3964 : row3964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3964 := by decide +kernel

theorem rowEval3964 (x : Key → ℝ) : Integer.Sparse.eval row3964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3964, Integer.Sparse.eval_collectBalanced, rawRowCheck3964]

def rawRow3965 : Integer.Sparse Key := [(key171, -2), (key171, -2), (key179, -2), (key174, 6), (key46, 2), (key46, 2), (key71, 2), (key32, -2), (key112, -2), (key112, -2), (key43, -6), (key206, 2), (key426, 2), (key426, 2)]

theorem rawRowCheck3965 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow3965 := by decide +kernel

def row3965 : Integer.Sparse Key := [(key32, -2), (key43, -6), (key46, 4), (key71, 2), (key112, -4), (key171, -4), (key174, 6), (key179, -2), (key206, 2), (key426, 4)]

theorem rowCheck3965 : row3965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3965 := by decide +kernel

theorem rowEval3965 (x : Key → ℝ) : Integer.Sparse.eval row3965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3965, Integer.Sparse.eval_collectBalanced, rawRowCheck3965]

def rawRow3966 : Integer.Sparse Key := [(key171, -2), (key179, -2), (key171, -2), (key174, 6), (key46, 2), (key71, 2), (key46, 2), (key112, -2), (key32, -2), (key112, -2), (key43, -6), (key426, 2), (key206, 2), (key426, 2)]

theorem rawRowCheck3966 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow3966 := by decide +kernel

def row3966 : Integer.Sparse Key := [(key32, -2), (key43, -6), (key46, 4), (key71, 2), (key112, -4), (key171, -4), (key174, 6), (key179, -2), (key206, 2), (key426, 4)]

theorem rowCheck3966 : row3966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3966 := by decide +kernel

theorem rowEval3966 (x : Key → ℝ) : Integer.Sparse.eval row3966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3966, Integer.Sparse.eval_collectBalanced, rawRowCheck3966]

def rawRow3967 : Integer.Sparse Key := [(key179, -2), (key171, -2), (key171, -2), (key174, 6), (key71, 2), (key46, 2), (key46, 2), (key112, -2), (key112, -2), (key32, -2), (key43, -6), (key426, 2), (key426, 2), (key206, 2)]

theorem rawRowCheck3967 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow3967 := by decide +kernel

def row3967 : Integer.Sparse Key := [(key32, -2), (key43, -6), (key46, 4), (key71, 2), (key112, -4), (key171, -4), (key174, 6), (key179, -2), (key206, 2), (key426, 4)]

theorem rowCheck3967 : row3967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3967 := by decide +kernel

theorem rowEval3967 (x : Key → ℝ) : Integer.Sparse.eval row3967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3967, Integer.Sparse.eval_collectBalanced, rawRowCheck3967]

end MUB6.Certificate.GramRows

end OAI

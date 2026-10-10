import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow672 : Integer.Sparse Key := [(key1811, -2), (key1314, -2), (key1811, -2), (key1653, 1), (key1838, 1), (key1335, 1), (key1838, 1), (key1335, 1), (key1653, 1), (key1786, 2), (key1294, 2), (key1786, 2), (key1453, -1), (key1838, -1), (key1335, -1), (key1838, -1), (key1335, -1), (key1453, -1), (key1571, -1), (key1786, -1), (key1294, -1), (key1786, -1), (key1294, -1), (key1571, -1), (key1422, 1), (key1811, 1), (key1314, 1), (key1811, 1), (key1314, 1), (key1422, 1)]

theorem rawRowCheck672 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow672 := by decide +kernel

def row672 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

theorem rowCheck672 : row672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow672 := by decide +kernel

theorem rowEval672 (x : Key → ℝ) : Integer.Sparse.eval row672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck672, Integer.Sparse.eval_collectBalanced, rawRowCheck672]

def rawRow673 : Integer.Sparse Key := [(key1811, -2), (key1811, -2), (key1314, -2), (key1838, 1), (key1653, 1), (key1838, 1), (key1335, 1), (key1653, 1), (key1335, 1), (key1786, 2), (key1786, 2), (key1294, 2), (key1838, -1), (key1453, -1), (key1838, -1), (key1335, -1), (key1453, -1), (key1335, -1), (key1786, -1), (key1571, -1), (key1786, -1), (key1294, -1), (key1571, -1), (key1294, -1), (key1811, 1), (key1422, 1), (key1811, 1), (key1314, 1), (key1422, 1), (key1314, 1)]

theorem rawRowCheck673 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow673 := by decide +kernel

def row673 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

theorem rowCheck673 : row673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow673 := by decide +kernel

theorem rowEval673 (x : Key → ℝ) : Integer.Sparse.eval row673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck673, Integer.Sparse.eval_collectBalanced, rawRowCheck673]

def rawRow674 : Integer.Sparse Key := [(key234, -6), (key246, 2), (key246, 2), (key246, 2), (key300, 6), (key314, -2), (key314, -2), (key314, -2), (key383, -2), (key383, -2), (key383, -2), (key404, 2), (key404, 2), (key404, 2)]

theorem rawRowCheck674 : GramPolynomial.normalizedRow 0 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow674 := by decide +kernel

def row674 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key300, 6), (key314, -6), (key383, -6), (key404, 6)]

theorem rowCheck674 : row674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow674 := by decide +kernel

theorem rowEval674 (x : Key → ℝ) : Integer.Sparse.eval row674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck674, Integer.Sparse.eval_collectBalanced, rawRowCheck674]

def rawRow675 : Integer.Sparse Key := [(key246, -6), (key234, 2), (key246, 2), (key246, 2), (key314, 6), (key300, -2), (key314, -2), (key314, -2), (key404, -2), (key433, -2), (key433, -2), (key383, 2), (key433, 2), (key433, 2)]

theorem rawRowCheck675 : GramPolynomial.normalizedRow 0 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form1 = rawRow675 := by decide +kernel

def row675 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

theorem rowCheck675 : row675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow675 := by decide +kernel

theorem rowEval675 (x : Key → ℝ) : Integer.Sparse.eval row675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck675, Integer.Sparse.eval_collectBalanced, rawRowCheck675]

def rawRow676 : Integer.Sparse Key := [(key246, -6), (key246, 2), (key234, 2), (key246, 2), (key314, 6), (key314, -2), (key300, -2), (key314, -2), (key433, -2), (key404, -2), (key433, -2), (key433, 2), (key383, 2), (key433, 2)]

theorem rawRowCheck676 : GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form1 = rawRow676 := by decide +kernel

def row676 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

theorem rowCheck676 : row676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow676 := by decide +kernel

theorem rowEval676 (x : Key → ℝ) : Integer.Sparse.eval row676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck676, Integer.Sparse.eval_collectBalanced, rawRowCheck676]

def rawRow677 : Integer.Sparse Key := [(key246, -6), (key246, 2), (key246, 2), (key234, 2), (key314, 6), (key314, -2), (key314, -2), (key300, -2), (key433, -2), (key433, -2), (key404, -2), (key433, 2), (key433, 2), (key383, 2)]

theorem rawRowCheck677 : GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form1 = rawRow677 := by decide +kernel

def row677 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

theorem rowCheck677 : row677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow677 := by decide +kernel

theorem rowEval677 (x : Key → ℝ) : Integer.Sparse.eval row677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck677, Integer.Sparse.eval_collectBalanced, rawRowCheck677]

def rawRow678 : Integer.Sparse Key := [(key300, -6), (key314, 2), (key314, 2), (key314, 2), (key234, 6), (key404, -2), (key404, -2), (key404, -2), (key246, -2), (key246, -2), (key246, -2), (key314, 2), (key314, 2), (key314, 2)]

theorem rawRowCheck678 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow678 := by decide +kernel

def row678 : Integer.Sparse Key := [(key234, 6), (key246, -6), (key300, -6), (key314, 12), (key404, -6)]

theorem rowCheck678 : row678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow678 := by decide +kernel

theorem rowEval678 (x : Key → ℝ) : Integer.Sparse.eval row678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck678, Integer.Sparse.eval_collectBalanced, rawRowCheck678]

def rawRow679 : Integer.Sparse Key := [(key314, -6), (key300, 2), (key314, 2), (key314, 2), (key404, 6), (key234, -2), (key404, -2), (key404, -2), (key314, -2), (key433, -2), (key433, -2), (key246, 2), (key433, 2), (key433, 2)]

theorem rawRowCheck679 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form1 = rawRow679 := by decide +kernel

def row679 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, -4), (key404, 2)]

theorem rowCheck679 : row679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow679 := by decide +kernel

theorem rowEval679 (x : Key → ℝ) : Integer.Sparse.eval row679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck679, Integer.Sparse.eval_collectBalanced, rawRowCheck679]

def rawRow680 : Integer.Sparse Key := [(key314, -6), (key314, 2), (key300, 2), (key314, 2), (key404, 6), (key404, -2), (key234, -2), (key404, -2), (key433, -2), (key314, -2), (key433, -2), (key433, 2), (key246, 2), (key433, 2)]

theorem rawRowCheck680 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form1 = rawRow680 := by decide +kernel

def row680 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, -4), (key404, 2)]

theorem rowCheck680 : row680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow680 := by decide +kernel

theorem rowEval680 (x : Key → ℝ) : Integer.Sparse.eval row680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck680, Integer.Sparse.eval_collectBalanced, rawRowCheck680]

def rawRow681 : Integer.Sparse Key := [(key314, -6), (key314, 2), (key314, 2), (key300, 2), (key404, 6), (key404, -2), (key404, -2), (key234, -2), (key433, -2), (key433, -2), (key314, -2), (key433, 2), (key433, 2), (key246, 2)]

theorem rawRowCheck681 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form1 = rawRow681 := by decide +kernel

def row681 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, -4), (key404, 2)]

theorem rowCheck681 : row681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow681 := by decide +kernel

theorem rowEval681 (x : Key → ℝ) : Integer.Sparse.eval row681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck681, Integer.Sparse.eval_collectBalanced, rawRowCheck681]

def rawRow682 : Integer.Sparse Key := [(key383, -6), (key404, 2), (key433, 2), (key433, 2), (key246, 6), (key314, -2), (key433, -2), (key433, -2), (key234, -2), (key246, -2), (key246, -2), (key300, 2), (key314, 2), (key314, 2)]

theorem rawRowCheck682 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form1 = rawRow682 := by decide +kernel

def row682 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, 2), (key383, -6), (key404, 2)]

theorem rowCheck682 : row682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow682 := by decide +kernel

theorem rowEval682 (x : Key → ℝ) : Integer.Sparse.eval row682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck682, Integer.Sparse.eval_collectBalanced, rawRowCheck682]

def rawRow683 : Integer.Sparse Key := [(key383, -6), (key433, 2), (key404, 2), (key433, 2), (key246, 6), (key433, -2), (key314, -2), (key433, -2), (key246, -2), (key234, -2), (key246, -2), (key314, 2), (key300, 2), (key314, 2)]

theorem rawRowCheck683 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form1 = rawRow683 := by decide +kernel

def row683 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, 2), (key383, -6), (key404, 2)]

theorem rowCheck683 : row683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow683 := by decide +kernel

theorem rowEval683 (x : Key → ℝ) : Integer.Sparse.eval row683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck683, Integer.Sparse.eval_collectBalanced, rawRowCheck683]

def rawRow684 : Integer.Sparse Key := [(key383, -6), (key433, 2), (key433, 2), (key404, 2), (key246, 6), (key433, -2), (key433, -2), (key314, -2), (key246, -2), (key246, -2), (key234, -2), (key314, 2), (key314, 2), (key300, 2)]

theorem rawRowCheck684 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form1 = rawRow684 := by decide +kernel

def row684 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, 2), (key383, -6), (key404, 2)]

theorem rowCheck684 : row684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow684 := by decide +kernel

theorem rowEval684 (x : Key → ℝ) : Integer.Sparse.eval row684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck684, Integer.Sparse.eval_collectBalanced, rawRowCheck684]

def rawRow685 : Integer.Sparse Key := [(key404, -6), (key383, 2), (key433, 2), (key433, 2), (key314, 6), (key246, -2), (key433, -2), (key433, -2), (key300, -2), (key314, -2), (key314, -2), (key234, 2), (key404, 2), (key404, 2)]

theorem rawRowCheck685 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow685 := by decide +kernel

def row685 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

theorem rowCheck685 : row685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow685 := by decide +kernel

theorem rowEval685 (x : Key → ℝ) : Integer.Sparse.eval row685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck685, Integer.Sparse.eval_collectBalanced, rawRowCheck685]

def rawRow686 : Integer.Sparse Key := [(key404, -6), (key433, 2), (key383, 2), (key433, 2), (key314, 6), (key433, -2), (key246, -2), (key433, -2), (key314, -2), (key300, -2), (key314, -2), (key404, 2), (key234, 2), (key404, 2)]

theorem rawRowCheck686 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow686 := by decide +kernel

def row686 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

theorem rowCheck686 : row686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow686 := by decide +kernel

theorem rowEval686 (x : Key → ℝ) : Integer.Sparse.eval row686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck686, Integer.Sparse.eval_collectBalanced, rawRowCheck686]

def rawRow687 : Integer.Sparse Key := [(key404, -6), (key433, 2), (key433, 2), (key383, 2), (key314, 6), (key433, -2), (key433, -2), (key246, -2), (key314, -2), (key314, -2), (key300, -2), (key404, 2), (key404, 2), (key234, 2)]

theorem rawRowCheck687 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow687 := by decide +kernel

def row687 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

theorem rowCheck687 : row687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow687 := by decide +kernel

theorem rowEval687 (x : Key → ℝ) : Integer.Sparse.eval row687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck687, Integer.Sparse.eval_collectBalanced, rawRowCheck687]

def rawRow688 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2735, 1), (key2737, 1), (key2735, 1), (key2747, 1), (key2737, 1), (key2747, 1), (key2805, 2), (key2805, 2), (key2831, 2), (key2893, -1), (key2897, -1), (key2893, -1), (key2904, -1), (key2897, -1), (key2904, -1), (key2948, -1), (key2950, -1), (key2948, -1), (key2960, -1), (key2950, -1), (key2960, -1), (key2972, 1), (key2976, 1), (key2972, 1), (key2983, 1), (key2976, 1), (key2983, 1)]

theorem rawRowCheck688 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form0 = rawRow688 := by decide +kernel

def row688 : Integer.Sparse Key := [(key2702, -4), (key2728, -2), (key2735, 2), (key2737, 2), (key2747, 2), (key2805, 4), (key2831, 2), (key2893, -2), (key2897, -2), (key2904, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, 2), (key2983, 2)]

theorem rowCheck688 : row688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow688 := by decide +kernel

theorem rowEval688 (x : Key → ℝ) : Integer.Sparse.eval row688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck688, Integer.Sparse.eval_collectBalanced, rawRowCheck688]

def rawRow689 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2737, 1), (key2735, 1), (key2747, 1), (key2735, 1), (key2747, 1), (key2737, 1), (key2805, 2), (key2831, 2), (key2805, 2), (key2897, -1), (key2893, -1), (key2904, -1), (key2893, -1), (key2904, -1), (key2897, -1), (key2950, -1), (key2948, -1), (key2960, -1), (key2948, -1), (key2960, -1), (key2950, -1), (key2976, 1), (key2972, 1), (key2983, 1), (key2972, 1), (key2983, 1), (key2976, 1)]

theorem rawRowCheck689 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form0 = rawRow689 := by decide +kernel

def row689 : Integer.Sparse Key := [(key2702, -4), (key2728, -2), (key2735, 2), (key2737, 2), (key2747, 2), (key2805, 4), (key2831, 2), (key2893, -2), (key2897, -2), (key2904, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, 2), (key2983, 2)]

theorem rowCheck689 : row689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow689 := by decide +kernel

theorem rowEval689 (x : Key → ℝ) : Integer.Sparse.eval row689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck689, Integer.Sparse.eval_collectBalanced, rawRowCheck689]

def rawRow690 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2747, 1), (key2747, 1), (key2737, 1), (key2737, 1), (key2735, 1), (key2735, 1), (key2831, 2), (key2805, 2), (key2805, 2), (key2904, -1), (key2904, -1), (key2897, -1), (key2897, -1), (key2893, -1), (key2893, -1), (key2960, -1), (key2960, -1), (key2950, -1), (key2950, -1), (key2948, -1), (key2948, -1), (key2983, 1), (key2983, 1), (key2976, 1), (key2976, 1), (key2972, 1), (key2972, 1)]

theorem rawRowCheck690 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form0 = rawRow690 := by decide +kernel

def row690 : Integer.Sparse Key := [(key2702, -4), (key2728, -2), (key2735, 2), (key2737, 2), (key2747, 2), (key2805, 4), (key2831, 2), (key2893, -2), (key2897, -2), (key2904, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, 2), (key2983, 2)]

theorem rowCheck690 : row690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow690 := by decide +kernel

theorem rowEval690 (x : Key → ℝ) : Integer.Sparse.eval row690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck690, Integer.Sparse.eval_collectBalanced, rawRowCheck690]

def rawRow691 : Integer.Sparse Key := [(key2667, -2), (key2735, -2), (key2747, -2), (key2667, 1), (key2673, 1), (key2702, 1), (key2728, 1), (key2737, 1), (key2747, 1), (key2782, 2), (key2893, 2), (key2904, 2), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, -1), (key2972, -1), (key2983, -1), (key2997, -1), (key3000, -1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2998, 1), (key3000, 1)]

theorem rawRowCheck691 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form0 = rawRow691 := by decide +kernel

def row691 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

theorem rowCheck691 : row691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow691 := by decide +kernel

theorem rowEval691 (x : Key → ℝ) : Integer.Sparse.eval row691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck691, Integer.Sparse.eval_collectBalanced, rawRowCheck691]

def rawRow692 : Integer.Sparse Key := [(key2667, -2), (key2747, -2), (key2735, -2), (key2673, 1), (key2667, 1), (key2728, 1), (key2702, 1), (key2747, 1), (key2737, 1), (key2782, 2), (key2904, 2), (key2893, 2), (key2795, -1), (key2782, -1), (key2831, -1), (key2805, -1), (key2904, -1), (key2897, -1), (key2938, -1), (key2936, -1), (key2983, -1), (key2972, -1), (key3000, -1), (key2997, -1), (key2943, 1), (key2936, 1), (key2960, 1), (key2948, 1), (key3000, 1), (key2998, 1)]

theorem rawRowCheck692 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form0 = rawRow692 := by decide +kernel

def row692 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

theorem rowCheck692 : row692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow692 := by decide +kernel

theorem rowEval692 (x : Key → ℝ) : Integer.Sparse.eval row692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck692, Integer.Sparse.eval_collectBalanced, rawRowCheck692]

def rawRow693 : Integer.Sparse Key := [(key2735, -2), (key2667, -2), (key2747, -2), (key2702, 1), (key2737, 1), (key2667, 1), (key2747, 1), (key2673, 1), (key2728, 1), (key2893, 2), (key2782, 2), (key2904, 2), (key2805, -1), (key2897, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2972, -1), (key2997, -1), (key2936, -1), (key3000, -1), (key2938, -1), (key2983, -1), (key2948, 1), (key2998, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2960, 1)]

theorem rawRowCheck693 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form0 = rawRow693 := by decide +kernel

def row693 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

theorem rowCheck693 : row693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow693 := by decide +kernel

theorem rowEval693 (x : Key → ℝ) : Integer.Sparse.eval row693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck693, Integer.Sparse.eval_collectBalanced, rawRowCheck693]

def rawRow694 : Integer.Sparse Key := [(key2735, -2), (key2747, -2), (key2667, -2), (key2737, 1), (key2702, 1), (key2747, 1), (key2667, 1), (key2728, 1), (key2673, 1), (key2893, 2), (key2904, 2), (key2782, 2), (key2897, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2831, -1), (key2795, -1), (key2997, -1), (key2972, -1), (key3000, -1), (key2936, -1), (key2983, -1), (key2938, -1), (key2998, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2960, 1), (key2943, 1)]

theorem rawRowCheck694 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form0 = rawRow694 := by decide +kernel

def row694 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

theorem rowCheck694 : row694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow694 := by decide +kernel

theorem rowEval694 (x : Key → ℝ) : Integer.Sparse.eval row694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck694, Integer.Sparse.eval_collectBalanced, rawRowCheck694]

def rawRow695 : Integer.Sparse Key := [(key2747, -2), (key2667, -2), (key2735, -2), (key2728, 1), (key2747, 1), (key2673, 1), (key2737, 1), (key2667, 1), (key2702, 1), (key2904, 2), (key2782, 2), (key2893, 2), (key2831, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2782, -1), (key2805, -1), (key2983, -1), (key3000, -1), (key2938, -1), (key2997, -1), (key2936, -1), (key2972, -1), (key2960, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2936, 1), (key2948, 1)]

theorem rawRowCheck695 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form0 = rawRow695 := by decide +kernel

def row695 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

theorem rowCheck695 : row695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow695 := by decide +kernel

theorem rowEval695 (x : Key → ℝ) : Integer.Sparse.eval row695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck695, Integer.Sparse.eval_collectBalanced, rawRowCheck695]

def rawRow696 : Integer.Sparse Key := [(key2747, -2), (key2735, -2), (key2667, -2), (key2747, 1), (key2728, 1), (key2737, 1), (key2673, 1), (key2702, 1), (key2667, 1), (key2904, 2), (key2893, 2), (key2782, 2), (key2904, -1), (key2831, -1), (key2897, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key3000, -1), (key2983, -1), (key2997, -1), (key2938, -1), (key2972, -1), (key2936, -1), (key3000, 1), (key2960, 1), (key2998, 1), (key2943, 1), (key2948, 1), (key2936, 1)]

theorem rawRowCheck696 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form0 = rawRow696 := by decide +kernel

def row696 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

theorem rowCheck696 : row696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow696 := by decide +kernel

theorem rowEval696 (x : Key → ℝ) : Integer.Sparse.eval row696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck696, Integer.Sparse.eval_collectBalanced, rawRowCheck696]

def rawRow697 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2948, 1), (key2950, 1), (key2948, 1), (key2960, 1), (key2950, 1), (key2960, 1), (key2702, 2), (key2702, 2), (key2728, 2), (key2972, -1), (key2976, -1), (key2972, -1), (key2983, -1), (key2976, -1), (key2983, -1), (key2735, -1), (key2737, -1), (key2735, -1), (key2747, -1), (key2737, -1), (key2747, -1), (key2893, 1), (key2897, 1), (key2893, 1), (key2904, 1), (key2897, 1), (key2904, 1)]

theorem rawRowCheck697 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form0 = rawRow697 := by decide +kernel

def row697 : Integer.Sparse Key := [(key2702, 4), (key2728, 2), (key2735, -2), (key2737, -2), (key2747, -2), (key2805, -4), (key2831, -2), (key2893, 2), (key2897, 2), (key2904, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2972, -2), (key2976, -2), (key2983, -2)]

theorem rowCheck697 : row697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow697 := by decide +kernel

theorem rowEval697 (x : Key → ℝ) : Integer.Sparse.eval row697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck697, Integer.Sparse.eval_collectBalanced, rawRowCheck697]

def rawRow698 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2950, 1), (key2948, 1), (key2960, 1), (key2948, 1), (key2960, 1), (key2950, 1), (key2702, 2), (key2728, 2), (key2702, 2), (key2976, -1), (key2972, -1), (key2983, -1), (key2972, -1), (key2983, -1), (key2976, -1), (key2737, -1), (key2735, -1), (key2747, -1), (key2735, -1), (key2747, -1), (key2737, -1), (key2897, 1), (key2893, 1), (key2904, 1), (key2893, 1), (key2904, 1), (key2897, 1)]

theorem rawRowCheck698 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form0 = rawRow698 := by decide +kernel

def row698 : Integer.Sparse Key := [(key2702, 4), (key2728, 2), (key2735, -2), (key2737, -2), (key2747, -2), (key2805, -4), (key2831, -2), (key2893, 2), (key2897, 2), (key2904, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2972, -2), (key2976, -2), (key2983, -2)]

theorem rowCheck698 : row698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow698 := by decide +kernel

theorem rowEval698 (x : Key → ℝ) : Integer.Sparse.eval row698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck698, Integer.Sparse.eval_collectBalanced, rawRowCheck698]

def rawRow699 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2960, 1), (key2960, 1), (key2950, 1), (key2950, 1), (key2948, 1), (key2948, 1), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, -1), (key2983, -1), (key2976, -1), (key2976, -1), (key2972, -1), (key2972, -1), (key2747, -1), (key2747, -1), (key2737, -1), (key2737, -1), (key2735, -1), (key2735, -1), (key2904, 1), (key2904, 1), (key2897, 1), (key2897, 1), (key2893, 1), (key2893, 1)]

theorem rawRowCheck699 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form0 = rawRow699 := by decide +kernel

def row699 : Integer.Sparse Key := [(key2702, 4), (key2728, 2), (key2735, -2), (key2737, -2), (key2747, -2), (key2805, -4), (key2831, -2), (key2893, 2), (key2897, 2), (key2904, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2972, -2), (key2976, -2), (key2983, -2)]

theorem rowCheck699 : row699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow699 := by decide +kernel

theorem rowEval699 (x : Key → ℝ) : Integer.Sparse.eval row699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck699, Integer.Sparse.eval_collectBalanced, rawRowCheck699]

def rawRow700 : Integer.Sparse Key := [(key2612, -2), (key2948, -2), (key2960, -2), (key2612, 1), (key2618, 1), (key2805, 1), (key2831, 1), (key2950, 1), (key2960, 1), (key2628, 2), (key2972, 2), (key2983, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2728, -1), (key2976, -1), (key2983, -1), (key2646, -1), (key2648, -1), (key2893, -1), (key2904, -1), (key2997, -1), (key3000, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2747, 1), (key2998, 1), (key3000, 1)]

theorem rawRowCheck700 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form0 = rawRow700 := by decide +kernel

def row700 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2831, 1), (key2893, -1), (key2904, -1), (key2948, -2), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

theorem rowCheck700 : row700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow700 := by decide +kernel

theorem rowEval700 (x : Key → ℝ) : Integer.Sparse.eval row700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck700, Integer.Sparse.eval_collectBalanced, rawRowCheck700]

def rawRow701 : Integer.Sparse Key := [(key2616, -2), (key2960, -2), (key2948, -2), (key2618, 1), (key2612, 1), (key2831, 1), (key2805, 1), (key2960, 1), (key2950, 1), (key2628, 2), (key2983, 2), (key2972, 2), (key2641, -1), (key2628, -1), (key2728, -1), (key2702, -1), (key2983, -1), (key2976, -1), (key2648, -1), (key2646, -1), (key2904, -1), (key2893, -1), (key3000, -1), (key2997, -1), (key2653, 1), (key2646, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2998, 1)]

theorem rawRowCheck701 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form0 = rawRow701 := by decide +kernel

def row701 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2831, 1), (key2893, -1), (key2904, -1), (key2948, -2), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

theorem rowCheck701 : row701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow701 := by decide +kernel

theorem rowEval701 (x : Key → ℝ) : Integer.Sparse.eval row701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck701, Integer.Sparse.eval_collectBalanced, rawRowCheck701]

def rawRow702 : Integer.Sparse Key := [(key2829, -2), (key2612, -2), (key2960, -2), (key2805, 1), (key2950, 1), (key2612, 1), (key2960, 1), (key2618, 1), (key2831, 1), (key2972, 2), (key2628, 2), (key2983, 2), (key2702, -1), (key2976, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2893, -1), (key2997, -1), (key2646, -1), (key3000, -1), (key2648, -1), (key2904, -1), (key2735, 1), (key2998, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2747, 1)]

theorem rawRowCheck702 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form0 = rawRow702 := by decide +kernel

def row702 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

theorem rowCheck702 : row702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow702 := by decide +kernel

theorem rowEval702 (x : Key → ℝ) : Integer.Sparse.eval row702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck702, Integer.Sparse.eval_collectBalanced, rawRowCheck702]

def rawRow703 : Integer.Sparse Key := [(key2829, -2), (key2960, -2), (key2612, -2), (key2950, 1), (key2805, 1), (key2960, 1), (key2612, 1), (key2831, 1), (key2618, 1), (key2972, 2), (key2983, 2), (key2628, 2), (key2976, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2728, -1), (key2641, -1), (key2997, -1), (key2893, -1), (key3000, -1), (key2646, -1), (key2904, -1), (key2648, -1), (key2998, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2747, 1), (key2653, 1)]

theorem rawRowCheck703 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form0 = rawRow703 := by decide +kernel

def row703 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

theorem rowCheck703 : row703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow703 := by decide +kernel

theorem rowEval703 (x : Key → ℝ) : Integer.Sparse.eval row703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck703, Integer.Sparse.eval_collectBalanced, rawRowCheck703]

end MUB6.Certificate.GramRows

end OAI

import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11648 : Integer.Sparse Key := [(key2200, -6), (key2193, -6), (key2194, -6), (key2194, -6), (key2310, 2), (key2302, 2), (key2303, 2), (key2310, 2), (key2302, 2), (key2347, 2), (key2091, 2), (key2341, 2), (key2092, 2), (key2303, 2), (key2341, 2), (key2092, 2)]

theorem rawRowCheck11648 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form13 = rawRow11648 := by decide +kernel

def row11648 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11648 : row11648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11648 := by decide +kernel

theorem rowEval11648 (x : Key → ℝ) : Integer.Sparse.eval row11648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11648, Integer.Sparse.eval_collectBalanced, rawRowCheck11648]

def rawRow11649 : Integer.Sparse Key := [(key2194, -6), (key2200, -6), (key2193, -6), (key2194, -6), (key2303, 2), (key2310, 2), (key2302, 2), (key2341, 2), (key2347, 2), (key2092, 2), (key2310, 2), (key2091, 2), (key2302, 2), (key2341, 2), (key2092, 2), (key2303, 2)]

theorem rawRowCheck11649 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form13 = rawRow11649 := by decide +kernel

def row11649 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11649 : row11649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11649 := by decide +kernel

theorem rowEval11649 (x : Key → ℝ) : Integer.Sparse.eval row11649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11649, Integer.Sparse.eval_collectBalanced, rawRowCheck11649]

def rawRow11650 : Integer.Sparse Key := [(key2200, -6), (key2194, -6), (key2193, -6), (key2194, -6), (key2310, 2), (key2303, 2), (key2302, 2), (key2347, 2), (key2341, 2), (key2310, 2), (key2092, 2), (key2302, 2), (key2091, 2), (key2341, 2), (key2303, 2), (key2092, 2)]

theorem rawRowCheck11650 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form13 = rawRow11650 := by decide +kernel

def row11650 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11650 : row11650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11650 := by decide +kernel

theorem rowEval11650 (x : Key → ℝ) : Integer.Sparse.eval row11650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11650, Integer.Sparse.eval_collectBalanced, rawRowCheck11650]

def rawRow11651 : Integer.Sparse Key := [(key2194, -6), (key2194, -6), (key2200, -6), (key2193, -6), (key2341, 2), (key2341, 2), (key2347, 2), (key2092, 2), (key2092, 2), (key2303, 2), (key2303, 2), (key2310, 2), (key2310, 2), (key2091, 2), (key2302, 2), (key2302, 2)]

theorem rawRowCheck11651 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form13 = rawRow11651 := by decide +kernel

def row11651 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11651 : row11651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11651 := by decide +kernel

theorem rowEval11651 (x : Key → ℝ) : Integer.Sparse.eval row11651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11651, Integer.Sparse.eval_collectBalanced, rawRowCheck11651]

def rawRow11652 : Integer.Sparse Key := [(key2194, -6), (key2200, -6), (key2194, -6), (key2193, -6), (key2341, 2), (key2347, 2), (key2341, 2), (key2303, 2), (key2310, 2), (key2092, 2), (key2310, 2), (key2092, 2), (key2303, 2), (key2302, 2), (key2091, 2), (key2302, 2)]

theorem rawRowCheck11652 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form13 = rawRow11652 := by decide +kernel

def row11652 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11652 : row11652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11652 := by decide +kernel

theorem rowEval11652 (x : Key → ℝ) : Integer.Sparse.eval row11652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11652, Integer.Sparse.eval_collectBalanced, rawRowCheck11652]

def rawRow11653 : Integer.Sparse Key := [(key2200, -6), (key2194, -6), (key2194, -6), (key2193, -6), (key2347, 2), (key2341, 2), (key2341, 2), (key2310, 2), (key2303, 2), (key2310, 2), (key2092, 2), (key2303, 2), (key2092, 2), (key2302, 2), (key2302, 2), (key2091, 2)]

theorem rawRowCheck11653 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form13 = rawRow11653 := by decide +kernel

def row11653 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11653 : row11653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11653 := by decide +kernel

theorem rowEval11653 (x : Key → ℝ) : Integer.Sparse.eval row11653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11653, Integer.Sparse.eval_collectBalanced, rawRowCheck11653]

def rawRow11654 : Integer.Sparse Key := [(key1029, 6), (key1034, 6), (key1034, 6), (key1069, 6), (key1013, -6), (key1121, -6), (key1121, -6), (key1197, -6)]

theorem rawRowCheck11654 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form14 = rawRow11654 := by decide +kernel

def row11654 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11654 : row11654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11654 := by decide +kernel

theorem rowEval11654 (x : Key → ℝ) : Integer.Sparse.eval row11654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11654, Integer.Sparse.eval_collectBalanced, rawRowCheck11654]

def rawRow11655 : Integer.Sparse Key := [(key1034, 6), (key1029, 6), (key1034, 6), (key1069, 6), (key1013, -6), (key1121, -6), (key1197, -6), (key1121, -6)]

theorem rawRowCheck11655 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form14 = rawRow11655 := by decide +kernel

def row11655 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11655 : row11655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11655 := by decide +kernel

theorem rowEval11655 (x : Key → ℝ) : Integer.Sparse.eval row11655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11655, Integer.Sparse.eval_collectBalanced, rawRowCheck11655]

def rawRow11656 : Integer.Sparse Key := [(key1034, 6), (key1034, 6), (key1029, 6), (key1069, 6), (key1013, -6), (key1197, -6), (key1121, -6), (key1121, -6)]

theorem rawRowCheck11656 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form14 = rawRow11656 := by decide +kernel

def row11656 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11656 : row11656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11656 := by decide +kernel

theorem rowEval11656 (x : Key → ℝ) : Integer.Sparse.eval row11656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11656, Integer.Sparse.eval_collectBalanced, rawRowCheck11656]

def rawRow11657 : Integer.Sparse Key := [(key1029, 6), (key1034, 6), (key1069, 6), (key1034, 6), (key1121, -6), (key1013, -6), (key1121, -6), (key1197, -6)]

theorem rawRowCheck11657 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form14 = rawRow11657 := by decide +kernel

def row11657 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11657 : row11657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11657 := by decide +kernel

theorem rowEval11657 (x : Key → ℝ) : Integer.Sparse.eval row11657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11657, Integer.Sparse.eval_collectBalanced, rawRowCheck11657]

def rawRow11658 : Integer.Sparse Key := [(key1034, 6), (key1029, 6), (key1069, 6), (key1034, 6), (key1121, -6), (key1013, -6), (key1197, -6), (key1121, -6)]

theorem rawRowCheck11658 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form14 = rawRow11658 := by decide +kernel

def row11658 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11658 : row11658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11658 := by decide +kernel

theorem rowEval11658 (x : Key → ℝ) : Integer.Sparse.eval row11658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11658, Integer.Sparse.eval_collectBalanced, rawRowCheck11658]

def rawRow11659 : Integer.Sparse Key := [(key1029, 6), (key1069, 6), (key1034, 6), (key1034, 6), (key1121, -6), (key1121, -6), (key1013, -6), (key1197, -6)]

theorem rawRowCheck11659 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form14 = rawRow11659 := by decide +kernel

def row11659 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11659 : row11659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11659 := by decide +kernel

theorem rowEval11659 (x : Key → ℝ) : Integer.Sparse.eval row11659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck11659, Integer.Sparse.eval_collectBalanced, rawRowCheck11659]

def rawRow11660 : Integer.Sparse Key := [(key1069, 6), (key1029, 6), (key1034, 6), (key1034, 6), (key1121, -6), (key1121, -6), (key1197, -6), (key1013, -6)]

theorem rawRowCheck11660 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form14 = rawRow11660 := by decide +kernel

def row11660 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11660 : row11660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11660 := by decide +kernel

theorem rowEval11660 (x : Key → ℝ) : Integer.Sparse.eval row11660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11660, Integer.Sparse.eval_collectBalanced, rawRowCheck11660]

def rawRow11661 : Integer.Sparse Key := [(key1034, 6), (key1069, 6), (key1029, 6), (key1034, 6), (key1121, -6), (key1197, -6), (key1013, -6), (key1121, -6)]

theorem rawRowCheck11661 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form14 = rawRow11661 := by decide +kernel

def row11661 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11661 : row11661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11661 := by decide +kernel

theorem rowEval11661 (x : Key → ℝ) : Integer.Sparse.eval row11661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11661, Integer.Sparse.eval_collectBalanced, rawRowCheck11661]

def rawRow11662 : Integer.Sparse Key := [(key1069, 6), (key1034, 6), (key1029, 6), (key1034, 6), (key1121, -6), (key1197, -6), (key1121, -6), (key1013, -6)]

theorem rawRowCheck11662 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form14 = rawRow11662 := by decide +kernel

def row11662 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11662 : row11662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11662 := by decide +kernel

theorem rowEval11662 (x : Key → ℝ) : Integer.Sparse.eval row11662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11662, Integer.Sparse.eval_collectBalanced, rawRowCheck11662]

def rawRow11663 : Integer.Sparse Key := [(key1034, 6), (key1034, 6), (key1069, 6), (key1029, 6), (key1197, -6), (key1013, -6), (key1121, -6), (key1121, -6)]

theorem rawRowCheck11663 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form14 = rawRow11663 := by decide +kernel

def row11663 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11663 : row11663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11663 := by decide +kernel

theorem rowEval11663 (x : Key → ℝ) : Integer.Sparse.eval row11663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11663, Integer.Sparse.eval_collectBalanced, rawRowCheck11663]

def rawRow11664 : Integer.Sparse Key := [(key1034, 6), (key1069, 6), (key1034, 6), (key1029, 6), (key1197, -6), (key1121, -6), (key1013, -6), (key1121, -6)]

theorem rawRowCheck11664 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form14 = rawRow11664 := by decide +kernel

def row11664 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11664 : row11664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11664 := by decide +kernel

theorem rowEval11664 (x : Key → ℝ) : Integer.Sparse.eval row11664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck11664, Integer.Sparse.eval_collectBalanced, rawRowCheck11664]

def rawRow11665 : Integer.Sparse Key := [(key1069, 6), (key1034, 6), (key1034, 6), (key1029, 6), (key1197, -6), (key1121, -6), (key1121, -6), (key1013, -6)]

theorem rawRowCheck11665 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form14 = rawRow11665 := by decide +kernel

def row11665 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

theorem rowCheck11665 : row11665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11665 := by decide +kernel

theorem rowEval11665 (x : Key → ℝ) : Integer.Sparse.eval row11665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck11665, Integer.Sparse.eval_collectBalanced, rawRowCheck11665]

def rawRow11666 : Integer.Sparse Key := [(key2398, -6), (key2401, -6), (key2401, -6), (key2433, -6), (key2583, 2), (key2586, 2), (key2586, 2), (key2839, 2), (key2842, 2), (key2839, 2), (key2874, 2), (key2842, 2), (key2874, 2), (key2965, 2), (key2965, 2), (key2987, 2)]

theorem rawRowCheck11666 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form15 = rawRow11666 := by decide +kernel

def row11666 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11666 : row11666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11666 := by decide +kernel

theorem rowEval11666 (x : Key → ℝ) : Integer.Sparse.eval row11666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11666, Integer.Sparse.eval_collectBalanced, rawRowCheck11666]

def rawRow11667 : Integer.Sparse Key := [(key2401, -6), (key2398, -6), (key2401, -6), (key2433, -6), (key2586, 2), (key2583, 2), (key2586, 2), (key2842, 2), (key2839, 2), (key2874, 2), (key2839, 2), (key2874, 2), (key2842, 2), (key2965, 2), (key2987, 2), (key2965, 2)]

theorem rawRowCheck11667 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form15 = rawRow11667 := by decide +kernel

def row11667 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11667 : row11667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11667 := by decide +kernel

theorem rowEval11667 (x : Key → ℝ) : Integer.Sparse.eval row11667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11667, Integer.Sparse.eval_collectBalanced, rawRowCheck11667]

def rawRow11668 : Integer.Sparse Key := [(key2401, -6), (key2401, -6), (key2398, -6), (key2433, -6), (key2586, 2), (key2586, 2), (key2583, 2), (key2874, 2), (key2874, 2), (key2842, 2), (key2842, 2), (key2839, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2965, 2)]

theorem rawRowCheck11668 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form15 = rawRow11668 := by decide +kernel

def row11668 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11668 : row11668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11668 := by decide +kernel

theorem rowEval11668 (x : Key → ℝ) : Integer.Sparse.eval row11668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11668, Integer.Sparse.eval_collectBalanced, rawRowCheck11668]

def rawRow11669 : Integer.Sparse Key := [(key2398, -6), (key2401, -6), (key2433, -6), (key2401, -6), (key2839, 2), (key2842, 2), (key2965, 2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2586, 2), (key2842, 2), (key2874, 2)]

theorem rawRowCheck11669 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form15 = rawRow11669 := by decide +kernel

def row11669 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11669 : row11669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11669 := by decide +kernel

theorem rowEval11669 (x : Key → ℝ) : Integer.Sparse.eval row11669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11669, Integer.Sparse.eval_collectBalanced, rawRowCheck11669]

def rawRow11670 : Integer.Sparse Key := [(key2401, -6), (key2398, -6), (key2433, -6), (key2401, -6), (key2842, 2), (key2839, 2), (key2965, 2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2586, 2), (key2874, 2), (key2842, 2)]

theorem rawRowCheck11670 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form15 = rawRow11670 := by decide +kernel

def row11670 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11670 : row11670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11670 := by decide +kernel

theorem rowEval11670 (x : Key → ℝ) : Integer.Sparse.eval row11670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11670, Integer.Sparse.eval_collectBalanced, rawRowCheck11670]

def rawRow11671 : Integer.Sparse Key := [(key2398, -6), (key2433, -6), (key2401, -6), (key2401, -6), (key2839, 2), (key2965, 2), (key2842, 2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2842, 2), (key2586, 2), (key2874, 2)]

theorem rawRowCheck11671 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form15 = rawRow11671 := by decide +kernel

def row11671 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11671 : row11671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11671 := by decide +kernel

theorem rowEval11671 (x : Key → ℝ) : Integer.Sparse.eval row11671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11671, Integer.Sparse.eval_collectBalanced, rawRowCheck11671]

def rawRow11672 : Integer.Sparse Key := [(key2433, -6), (key2398, -6), (key2401, -6), (key2401, -6), (key2965, 2), (key2839, 2), (key2842, 2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2842, 2), (key2874, 2), (key2586, 2)]

theorem rawRowCheck11672 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form15 = rawRow11672 := by decide +kernel

def row11672 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11672 : row11672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11672 := by decide +kernel

theorem rowEval11672 (x : Key → ℝ) : Integer.Sparse.eval row11672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11672, Integer.Sparse.eval_collectBalanced, rawRowCheck11672]

def rawRow11673 : Integer.Sparse Key := [(key2401, -6), (key2433, -6), (key2398, -6), (key2401, -6), (key2842, 2), (key2965, 2), (key2839, 2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2874, 2), (key2586, 2), (key2842, 2)]

theorem rawRowCheck11673 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form15 = rawRow11673 := by decide +kernel

def row11673 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11673 : row11673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11673 := by decide +kernel

theorem rowEval11673 (x : Key → ℝ) : Integer.Sparse.eval row11673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11673, Integer.Sparse.eval_collectBalanced, rawRowCheck11673]

def rawRow11674 : Integer.Sparse Key := [(key2433, -6), (key2401, -6), (key2398, -6), (key2401, -6), (key2965, 2), (key2842, 2), (key2839, 2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2874, 2), (key2842, 2), (key2586, 2)]

theorem rawRowCheck11674 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form15 = rawRow11674 := by decide +kernel

def row11674 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11674 : row11674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11674 := by decide +kernel

theorem rowEval11674 (x : Key → ℝ) : Integer.Sparse.eval row11674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11674, Integer.Sparse.eval_collectBalanced, rawRowCheck11674]

def rawRow11675 : Integer.Sparse Key := [(key2401, -6), (key2401, -6), (key2433, -6), (key2398, -6), (key2874, 2), (key2874, 2), (key2987, 2), (key2586, 2), (key2586, 2), (key2842, 2), (key2842, 2), (key2965, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2839, 2)]

theorem rawRowCheck11675 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form15 = rawRow11675 := by decide +kernel

def row11675 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11675 : row11675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11675 := by decide +kernel

theorem rowEval11675 (x : Key → ℝ) : Integer.Sparse.eval row11675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11675, Integer.Sparse.eval_collectBalanced, rawRowCheck11675]

def rawRow11676 : Integer.Sparse Key := [(key2401, -6), (key2433, -6), (key2401, -6), (key2398, -6), (key2874, 2), (key2987, 2), (key2874, 2), (key2842, 2), (key2965, 2), (key2586, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2839, 2), (key2583, 2), (key2839, 2)]

theorem rawRowCheck11676 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form15 = rawRow11676 := by decide +kernel

def row11676 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11676 : row11676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11676 := by decide +kernel

theorem rowEval11676 (x : Key → ℝ) : Integer.Sparse.eval row11676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11676, Integer.Sparse.eval_collectBalanced, rawRowCheck11676]

def rawRow11677 : Integer.Sparse Key := [(key2433, -6), (key2401, -6), (key2401, -6), (key2398, -6), (key2987, 2), (key2874, 2), (key2874, 2), (key2965, 2), (key2842, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2586, 2), (key2839, 2), (key2839, 2), (key2583, 2)]

theorem rawRowCheck11677 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form15 = rawRow11677 := by decide +kernel

def row11677 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

theorem rowCheck11677 : row11677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11677 := by decide +kernel

theorem rowEval11677 (x : Key → ℝ) : Integer.Sparse.eval row11677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11677, Integer.Sparse.eval_collectBalanced, rawRowCheck11677]

def rawRow11678 : Integer.Sparse Key := [(key2662, -6), (key2777, -6), (key2777, -6), (key2788, -6), (key2607, 6), (key2800, 6), (key2800, 6), (key2823, 6)]

theorem rawRowCheck11678 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form16 = rawRow11678 := by decide +kernel

def row11678 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11678 : row11678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11678 := by decide +kernel

theorem rowEval11678 (x : Key → ℝ) : Integer.Sparse.eval row11678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11678, Integer.Sparse.eval_collectBalanced, rawRowCheck11678]

def rawRow11679 : Integer.Sparse Key := [(key2662, -6), (key2777, -6), (key2788, -6), (key2777, -6), (key2607, 6), (key2800, 6), (key2823, 6), (key2800, 6)]

theorem rawRowCheck11679 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form16 = rawRow11679 := by decide +kernel

def row11679 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11679 : row11679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11679 := by decide +kernel

theorem rowEval11679 (x : Key → ℝ) : Integer.Sparse.eval row11679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11679, Integer.Sparse.eval_collectBalanced, rawRowCheck11679]

def rawRow11680 : Integer.Sparse Key := [(key2662, -6), (key2788, -6), (key2777, -6), (key2777, -6), (key2607, 6), (key2823, 6), (key2800, 6), (key2800, 6)]

theorem rawRowCheck11680 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form16 = rawRow11680 := by decide +kernel

def row11680 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11680 : row11680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11680 := by decide +kernel

theorem rowEval11680 (x : Key → ℝ) : Integer.Sparse.eval row11680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11680, Integer.Sparse.eval_collectBalanced, rawRowCheck11680]

def rawRow11681 : Integer.Sparse Key := [(key2777, -6), (key2662, -6), (key2777, -6), (key2788, -6), (key2800, 6), (key2607, 6), (key2800, 6), (key2823, 6)]

theorem rawRowCheck11681 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form16 = rawRow11681 := by decide +kernel

def row11681 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11681 : row11681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11681 := by decide +kernel

theorem rowEval11681 (x : Key → ℝ) : Integer.Sparse.eval row11681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11681, Integer.Sparse.eval_collectBalanced, rawRowCheck11681]

def rawRow11682 : Integer.Sparse Key := [(key2777, -6), (key2662, -6), (key2788, -6), (key2777, -6), (key2800, 6), (key2607, 6), (key2823, 6), (key2800, 6)]

theorem rawRowCheck11682 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form16 = rawRow11682 := by decide +kernel

def row11682 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11682 : row11682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11682 := by decide +kernel

theorem rowEval11682 (x : Key → ℝ) : Integer.Sparse.eval row11682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11682, Integer.Sparse.eval_collectBalanced, rawRowCheck11682]

def rawRow11683 : Integer.Sparse Key := [(key2777, -6), (key2777, -6), (key2662, -6), (key2788, -6), (key2800, 6), (key2800, 6), (key2607, 6), (key2823, 6)]

theorem rawRowCheck11683 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form16 = rawRow11683 := by decide +kernel

def row11683 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11683 : row11683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11683 := by decide +kernel

theorem rowEval11683 (x : Key → ℝ) : Integer.Sparse.eval row11683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11683, Integer.Sparse.eval_collectBalanced, rawRowCheck11683]

def rawRow11684 : Integer.Sparse Key := [(key2777, -6), (key2777, -6), (key2788, -6), (key2662, -6), (key2800, 6), (key2800, 6), (key2823, 6), (key2607, 6)]

theorem rawRowCheck11684 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form16 = rawRow11684 := by decide +kernel

def row11684 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11684 : row11684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11684 := by decide +kernel

theorem rowEval11684 (x : Key → ℝ) : Integer.Sparse.eval row11684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11684, Integer.Sparse.eval_collectBalanced, rawRowCheck11684]

def rawRow11685 : Integer.Sparse Key := [(key2777, -6), (key2788, -6), (key2662, -6), (key2777, -6), (key2800, 6), (key2823, 6), (key2607, 6), (key2800, 6)]

theorem rawRowCheck11685 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form16 = rawRow11685 := by decide +kernel

def row11685 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11685 : row11685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11685 := by decide +kernel

theorem rowEval11685 (x : Key → ℝ) : Integer.Sparse.eval row11685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11685, Integer.Sparse.eval_collectBalanced, rawRowCheck11685]

def rawRow11686 : Integer.Sparse Key := [(key2777, -6), (key2788, -6), (key2777, -6), (key2662, -6), (key2800, 6), (key2823, 6), (key2800, 6), (key2607, 6)]

theorem rawRowCheck11686 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form16 = rawRow11686 := by decide +kernel

def row11686 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11686 : row11686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11686 := by decide +kernel

theorem rowEval11686 (x : Key → ℝ) : Integer.Sparse.eval row11686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11686, Integer.Sparse.eval_collectBalanced, rawRowCheck11686]

def rawRow11687 : Integer.Sparse Key := [(key2788, -6), (key2662, -6), (key2777, -6), (key2777, -6), (key2823, 6), (key2607, 6), (key2800, 6), (key2800, 6)]

theorem rawRowCheck11687 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form16 = rawRow11687 := by decide +kernel

def row11687 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11687 : row11687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11687 := by decide +kernel

theorem rowEval11687 (x : Key → ℝ) : Integer.Sparse.eval row11687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11687, Integer.Sparse.eval_collectBalanced, rawRowCheck11687]

def rawRow11688 : Integer.Sparse Key := [(key2788, -6), (key2777, -6), (key2662, -6), (key2777, -6), (key2823, 6), (key2800, 6), (key2607, 6), (key2800, 6)]

theorem rawRowCheck11688 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form16 = rawRow11688 := by decide +kernel

def row11688 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11688 : row11688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11688 := by decide +kernel

theorem rowEval11688 (x : Key → ℝ) : Integer.Sparse.eval row11688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11688, Integer.Sparse.eval_collectBalanced, rawRowCheck11688]

def rawRow11689 : Integer.Sparse Key := [(key2788, -6), (key2777, -6), (key2777, -6), (key2662, -6), (key2823, 6), (key2800, 6), (key2800, 6), (key2607, 6)]

theorem rawRowCheck11689 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form16 = rawRow11689 := by decide +kernel

def row11689 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

theorem rowCheck11689 : row11689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11689 := by decide +kernel

theorem rowEval11689 (x : Key → ℝ) : Integer.Sparse.eval row11689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11689, Integer.Sparse.eval_collectBalanced, rawRowCheck11689]

def rawRow11690 : Integer.Sparse Key := [(key2616, -2), (key2616, -2), (key2619, -2), (key2809, -2), (key2809, -2), (key2951, -2), (key2829, -2), (key2832, -2), (key2829, -2), (key2961, -2), (key2832, -2), (key2961, -2), (key2632, 2), (key2632, 2), (key2649, 2), (key2786, 2), (key2786, 2), (key2939, 2), (key2870, 2), (key2905, 2), (key2870, 2), (key2984, 2), (key2905, 2), (key2984, 2)]

theorem rawRowCheck11690 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form17 = rawRow11690 := by decide +kernel

def row11690 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11690 : row11690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11690 := by decide +kernel

theorem rowEval11690 (x : Key → ℝ) : Integer.Sparse.eval row11690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11690, Integer.Sparse.eval_collectBalanced, rawRowCheck11690]

def rawRow11691 : Integer.Sparse Key := [(key2616, -2), (key2619, -2), (key2616, -2), (key2809, -2), (key2951, -2), (key2809, -2), (key2832, -2), (key2829, -2), (key2961, -2), (key2829, -2), (key2961, -2), (key2832, -2), (key2632, 2), (key2649, 2), (key2632, 2), (key2786, 2), (key2939, 2), (key2786, 2), (key2905, 2), (key2870, 2), (key2984, 2), (key2870, 2), (key2984, 2), (key2905, 2)]

theorem rawRowCheck11691 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form17 = rawRow11691 := by decide +kernel

def row11691 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11691 : row11691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11691 := by decide +kernel

theorem rowEval11691 (x : Key → ℝ) : Integer.Sparse.eval row11691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11691, Integer.Sparse.eval_collectBalanced, rawRowCheck11691]

def rawRow11692 : Integer.Sparse Key := [(key2619, -2), (key2616, -2), (key2616, -2), (key2951, -2), (key2809, -2), (key2809, -2), (key2961, -2), (key2961, -2), (key2832, -2), (key2832, -2), (key2829, -2), (key2829, -2), (key2649, 2), (key2632, 2), (key2632, 2), (key2939, 2), (key2786, 2), (key2786, 2), (key2984, 2), (key2984, 2), (key2905, 2), (key2905, 2), (key2870, 2), (key2870, 2)]

theorem rawRowCheck11692 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form17 = rawRow11692 := by decide +kernel

def row11692 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11692 : row11692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11692 := by decide +kernel

theorem rowEval11692 (x : Key → ℝ) : Integer.Sparse.eval row11692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11692, Integer.Sparse.eval_collectBalanced, rawRowCheck11692]

def rawRow11693 : Integer.Sparse Key := [(key2809, -2), (key2829, -2), (key2832, -2), (key2616, -2), (key2829, -2), (key2961, -2), (key2616, -2), (key2619, -2), (key2809, -2), (key2951, -2), (key2832, -2), (key2961, -2), (key2786, 2), (key2870, 2), (key2905, 2), (key2632, 2), (key2870, 2), (key2984, 2), (key2632, 2), (key2649, 2), (key2786, 2), (key2939, 2), (key2905, 2), (key2984, 2)]

theorem rawRowCheck11693 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form17 = rawRow11693 := by decide +kernel

def row11693 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11693 : row11693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11693 := by decide +kernel

theorem rowEval11693 (x : Key → ℝ) : Integer.Sparse.eval row11693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11693, Integer.Sparse.eval_collectBalanced, rawRowCheck11693]

def rawRow11694 : Integer.Sparse Key := [(key2809, -2), (key2832, -2), (key2829, -2), (key2616, -2), (key2961, -2), (key2829, -2), (key2619, -2), (key2616, -2), (key2951, -2), (key2809, -2), (key2961, -2), (key2832, -2), (key2786, 2), (key2905, 2), (key2870, 2), (key2632, 2), (key2984, 2), (key2870, 2), (key2649, 2), (key2632, 2), (key2939, 2), (key2786, 2), (key2984, 2), (key2905, 2)]

theorem rawRowCheck11694 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form17 = rawRow11694 := by decide +kernel

def row11694 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11694 : row11694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11694 := by decide +kernel

theorem rowEval11694 (x : Key → ℝ) : Integer.Sparse.eval row11694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11694, Integer.Sparse.eval_collectBalanced, rawRowCheck11694]

def rawRow11695 : Integer.Sparse Key := [(key2829, -2), (key2809, -2), (key2832, -2), (key2829, -2), (key2616, -2), (key2961, -2), (key2809, -2), (key2832, -2), (key2616, -2), (key2961, -2), (key2619, -2), (key2951, -2), (key2870, 2), (key2786, 2), (key2905, 2), (key2870, 2), (key2632, 2), (key2984, 2), (key2786, 2), (key2905, 2), (key2632, 2), (key2984, 2), (key2649, 2), (key2939, 2)]

theorem rawRowCheck11695 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form17 = rawRow11695 := by decide +kernel

def row11695 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11695 : row11695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11695 := by decide +kernel

theorem rowEval11695 (x : Key → ℝ) : Integer.Sparse.eval row11695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11695, Integer.Sparse.eval_collectBalanced, rawRowCheck11695]

def rawRow11696 : Integer.Sparse Key := [(key2829, -2), (key2832, -2), (key2809, -2), (key2829, -2), (key2961, -2), (key2616, -2), (key2832, -2), (key2809, -2), (key2961, -2), (key2616, -2), (key2951, -2), (key2619, -2), (key2870, 2), (key2905, 2), (key2786, 2), (key2870, 2), (key2984, 2), (key2632, 2), (key2905, 2), (key2786, 2), (key2984, 2), (key2632, 2), (key2939, 2), (key2649, 2)]

theorem rawRowCheck11696 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form17 = rawRow11696 := by decide +kernel

def row11696 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11696 : row11696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11696 := by decide +kernel

theorem rowEval11696 (x : Key → ℝ) : Integer.Sparse.eval row11696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11696, Integer.Sparse.eval_collectBalanced, rawRowCheck11696]

def rawRow11697 : Integer.Sparse Key := [(key2832, -2), (key2809, -2), (key2829, -2), (key2961, -2), (key2616, -2), (key2829, -2), (key2951, -2), (key2961, -2), (key2619, -2), (key2832, -2), (key2616, -2), (key2809, -2), (key2905, 2), (key2786, 2), (key2870, 2), (key2984, 2), (key2632, 2), (key2870, 2), (key2939, 2), (key2984, 2), (key2649, 2), (key2905, 2), (key2632, 2), (key2786, 2)]

theorem rawRowCheck11697 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form17 = rawRow11697 := by decide +kernel

def row11697 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11697 : row11697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11697 := by decide +kernel

theorem rowEval11697 (x : Key → ℝ) : Integer.Sparse.eval row11697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11697, Integer.Sparse.eval_collectBalanced, rawRowCheck11697]

def rawRow11698 : Integer.Sparse Key := [(key2832, -2), (key2829, -2), (key2809, -2), (key2961, -2), (key2829, -2), (key2616, -2), (key2961, -2), (key2951, -2), (key2832, -2), (key2619, -2), (key2809, -2), (key2616, -2), (key2905, 2), (key2870, 2), (key2786, 2), (key2984, 2), (key2870, 2), (key2632, 2), (key2984, 2), (key2939, 2), (key2905, 2), (key2649, 2), (key2786, 2), (key2632, 2)]

theorem rawRowCheck11698 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form17 = rawRow11698 := by decide +kernel

def row11698 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11698 : row11698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11698 := by decide +kernel

theorem rowEval11698 (x : Key → ℝ) : Integer.Sparse.eval row11698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11698, Integer.Sparse.eval_collectBalanced, rawRowCheck11698]

def rawRow11699 : Integer.Sparse Key := [(key2951, -2), (key2961, -2), (key2961, -2), (key2619, -2), (key2832, -2), (key2832, -2), (key2616, -2), (key2616, -2), (key2809, -2), (key2809, -2), (key2829, -2), (key2829, -2), (key2939, 2), (key2984, 2), (key2984, 2), (key2649, 2), (key2905, 2), (key2905, 2), (key2632, 2), (key2632, 2), (key2786, 2), (key2786, 2), (key2870, 2), (key2870, 2)]

theorem rawRowCheck11699 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form17 = rawRow11699 := by decide +kernel

def row11699 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11699 : row11699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11699 := by decide +kernel

theorem rowEval11699 (x : Key → ℝ) : Integer.Sparse.eval row11699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11699, Integer.Sparse.eval_collectBalanced, rawRowCheck11699]

def rawRow11700 : Integer.Sparse Key := [(key2961, -2), (key2951, -2), (key2961, -2), (key2832, -2), (key2619, -2), (key2832, -2), (key2809, -2), (key2829, -2), (key2616, -2), (key2829, -2), (key2616, -2), (key2809, -2), (key2984, 2), (key2939, 2), (key2984, 2), (key2905, 2), (key2649, 2), (key2905, 2), (key2786, 2), (key2870, 2), (key2632, 2), (key2870, 2), (key2632, 2), (key2786, 2)]

theorem rawRowCheck11700 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form17 = rawRow11700 := by decide +kernel

def row11700 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11700 : row11700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11700 := by decide +kernel

theorem rowEval11700 (x : Key → ℝ) : Integer.Sparse.eval row11700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11700, Integer.Sparse.eval_collectBalanced, rawRowCheck11700]

def rawRow11701 : Integer.Sparse Key := [(key2961, -2), (key2961, -2), (key2951, -2), (key2832, -2), (key2832, -2), (key2619, -2), (key2829, -2), (key2809, -2), (key2829, -2), (key2616, -2), (key2809, -2), (key2616, -2), (key2984, 2), (key2984, 2), (key2939, 2), (key2905, 2), (key2905, 2), (key2649, 2), (key2870, 2), (key2786, 2), (key2870, 2), (key2632, 2), (key2786, 2), (key2632, 2)]

theorem rawRowCheck11701 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form17 = rawRow11701 := by decide +kernel

def row11701 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

theorem rowCheck11701 : row11701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11701 := by decide +kernel

theorem rowEval11701 (x : Key → ℝ) : Integer.Sparse.eval row11701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11701, Integer.Sparse.eval_collectBalanced, rawRowCheck11701]

def rawRow11702 : Integer.Sparse Key := [(key1003, 2), (key1003, 2), (key1007, 2), (key1116, 2), (key1116, 2), (key1194, 2), (key1152, 2), (key1156, 2), (key1152, 2), (key1213, 2), (key1156, 2), (key1213, 2), (key1017, -2), (key1020, -2), (key1020, -2), (key1125, -2), (key1128, -2), (key1125, -2), (key1200, -2), (key1128, -2), (key1200, -2), (key1172, -2), (key1172, -2), (key1223, -2)]

theorem rawRowCheck11702 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form18 = rawRow11702 := by decide +kernel

def row11702 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11702 : row11702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11702 := by decide +kernel

theorem rowEval11702 (x : Key → ℝ) : Integer.Sparse.eval row11702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11702, Integer.Sparse.eval_collectBalanced, rawRowCheck11702]

def rawRow11703 : Integer.Sparse Key := [(key1003, 2), (key1007, 2), (key1003, 2), (key1116, 2), (key1194, 2), (key1116, 2), (key1156, 2), (key1152, 2), (key1213, 2), (key1152, 2), (key1213, 2), (key1156, 2), (key1020, -2), (key1017, -2), (key1020, -2), (key1128, -2), (key1125, -2), (key1200, -2), (key1125, -2), (key1200, -2), (key1128, -2), (key1172, -2), (key1223, -2), (key1172, -2)]

theorem rawRowCheck11703 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form18 = rawRow11703 := by decide +kernel

def row11703 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11703 : row11703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11703 := by decide +kernel

theorem rowEval11703 (x : Key → ℝ) : Integer.Sparse.eval row11703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11703, Integer.Sparse.eval_collectBalanced, rawRowCheck11703]

def rawRow11704 : Integer.Sparse Key := [(key1007, 2), (key1003, 2), (key1003, 2), (key1194, 2), (key1116, 2), (key1116, 2), (key1213, 2), (key1213, 2), (key1156, 2), (key1156, 2), (key1152, 2), (key1152, 2), (key1020, -2), (key1020, -2), (key1017, -2), (key1200, -2), (key1200, -2), (key1128, -2), (key1128, -2), (key1125, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1172, -2)]

theorem rawRowCheck11704 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form18 = rawRow11704 := by decide +kernel

def row11704 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11704 : row11704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11704 := by decide +kernel

theorem rowEval11704 (x : Key → ℝ) : Integer.Sparse.eval row11704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11704, Integer.Sparse.eval_collectBalanced, rawRowCheck11704]

def rawRow11705 : Integer.Sparse Key := [(key1116, 2), (key1152, 2), (key1156, 2), (key1003, 2), (key1152, 2), (key1213, 2), (key1003, 2), (key1007, 2), (key1116, 2), (key1194, 2), (key1156, 2), (key1213, 2), (key1125, -2), (key1128, -2), (key1172, -2), (key1017, -2), (key1020, -2), (key1125, -2), (key1200, -2), (key1172, -2), (key1223, -2), (key1020, -2), (key1128, -2), (key1200, -2)]

theorem rawRowCheck11705 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form18 = rawRow11705 := by decide +kernel

def row11705 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11705 : row11705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11705 := by decide +kernel

theorem rowEval11705 (x : Key → ℝ) : Integer.Sparse.eval row11705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11705, Integer.Sparse.eval_collectBalanced, rawRowCheck11705]

def rawRow11706 : Integer.Sparse Key := [(key1116, 2), (key1156, 2), (key1152, 2), (key1003, 2), (key1213, 2), (key1152, 2), (key1007, 2), (key1003, 2), (key1194, 2), (key1116, 2), (key1213, 2), (key1156, 2), (key1128, -2), (key1125, -2), (key1172, -2), (key1020, -2), (key1017, -2), (key1200, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1020, -2), (key1200, -2), (key1128, -2)]

theorem rawRowCheck11706 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form18 = rawRow11706 := by decide +kernel

def row11706 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11706 : row11706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11706 := by decide +kernel

theorem rowEval11706 (x : Key → ℝ) : Integer.Sparse.eval row11706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11706, Integer.Sparse.eval_collectBalanced, rawRowCheck11706]

def rawRow11707 : Integer.Sparse Key := [(key1152, 2), (key1116, 2), (key1156, 2), (key1152, 2), (key1003, 2), (key1213, 2), (key1116, 2), (key1156, 2), (key1003, 2), (key1213, 2), (key1007, 2), (key1194, 2), (key1125, -2), (key1172, -2), (key1128, -2), (key1125, -2), (key1172, -2), (key1017, -2), (key1223, -2), (key1020, -2), (key1200, -2), (key1128, -2), (key1020, -2), (key1200, -2)]

theorem rawRowCheck11707 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form18 = rawRow11707 := by decide +kernel

def row11707 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11707 : row11707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11707 := by decide +kernel

theorem rowEval11707 (x : Key → ℝ) : Integer.Sparse.eval row11707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11707, Integer.Sparse.eval_collectBalanced, rawRowCheck11707]

def rawRow11708 : Integer.Sparse Key := [(key1152, 2), (key1156, 2), (key1116, 2), (key1152, 2), (key1213, 2), (key1003, 2), (key1156, 2), (key1116, 2), (key1213, 2), (key1003, 2), (key1194, 2), (key1007, 2), (key1172, -2), (key1125, -2), (key1128, -2), (key1172, -2), (key1125, -2), (key1223, -2), (key1017, -2), (key1200, -2), (key1020, -2), (key1128, -2), (key1200, -2), (key1020, -2)]

theorem rawRowCheck11708 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form18 = rawRow11708 := by decide +kernel

def row11708 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11708 : row11708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11708 := by decide +kernel

theorem rowEval11708 (x : Key → ℝ) : Integer.Sparse.eval row11708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11708, Integer.Sparse.eval_collectBalanced, rawRowCheck11708]

def rawRow11709 : Integer.Sparse Key := [(key1156, 2), (key1116, 2), (key1152, 2), (key1213, 2), (key1003, 2), (key1152, 2), (key1194, 2), (key1213, 2), (key1007, 2), (key1156, 2), (key1003, 2), (key1116, 2), (key1128, -2), (key1172, -2), (key1125, -2), (key1200, -2), (key1223, -2), (key1020, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1200, -2), (key1020, -2), (key1128, -2)]

theorem rawRowCheck11709 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form18 = rawRow11709 := by decide +kernel

def row11709 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11709 : row11709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11709 := by decide +kernel

theorem rowEval11709 (x : Key → ℝ) : Integer.Sparse.eval row11709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11709, Integer.Sparse.eval_collectBalanced, rawRowCheck11709]

def rawRow11710 : Integer.Sparse Key := [(key1156, 2), (key1152, 2), (key1116, 2), (key1213, 2), (key1152, 2), (key1003, 2), (key1213, 2), (key1194, 2), (key1156, 2), (key1007, 2), (key1116, 2), (key1003, 2), (key1172, -2), (key1128, -2), (key1125, -2), (key1223, -2), (key1200, -2), (key1172, -2), (key1020, -2), (key1125, -2), (key1017, -2), (key1200, -2), (key1128, -2), (key1020, -2)]

theorem rawRowCheck11710 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form18 = rawRow11710 := by decide +kernel

def row11710 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11710 : row11710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11710 := by decide +kernel

theorem rowEval11710 (x : Key → ℝ) : Integer.Sparse.eval row11710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11710, Integer.Sparse.eval_collectBalanced, rawRowCheck11710]

def rawRow11711 : Integer.Sparse Key := [(key1194, 2), (key1213, 2), (key1213, 2), (key1007, 2), (key1156, 2), (key1156, 2), (key1003, 2), (key1003, 2), (key1116, 2), (key1116, 2), (key1152, 2), (key1152, 2), (key1200, -2), (key1200, -2), (key1223, -2), (key1020, -2), (key1020, -2), (key1128, -2), (key1128, -2), (key1172, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1125, -2)]

theorem rawRowCheck11711 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form18 = rawRow11711 := by decide +kernel

def row11711 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11711 : row11711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11711 := by decide +kernel

theorem rowEval11711 (x : Key → ℝ) : Integer.Sparse.eval row11711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11711, Integer.Sparse.eval_collectBalanced, rawRowCheck11711]

def rawRow11712 : Integer.Sparse Key := [(key1213, 2), (key1194, 2), (key1213, 2), (key1156, 2), (key1007, 2), (key1156, 2), (key1116, 2), (key1152, 2), (key1003, 2), (key1152, 2), (key1003, 2), (key1116, 2), (key1200, -2), (key1223, -2), (key1200, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1125, -2), (key1017, -2), (key1125, -2)]

theorem rawRowCheck11712 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form18 = rawRow11712 := by decide +kernel

def row11712 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11712 : row11712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11712 := by decide +kernel

theorem rowEval11712 (x : Key → ℝ) : Integer.Sparse.eval row11712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11712, Integer.Sparse.eval_collectBalanced, rawRowCheck11712]

def rawRow11713 : Integer.Sparse Key := [(key1213, 2), (key1213, 2), (key1194, 2), (key1156, 2), (key1156, 2), (key1007, 2), (key1152, 2), (key1116, 2), (key1152, 2), (key1003, 2), (key1116, 2), (key1003, 2), (key1223, -2), (key1200, -2), (key1200, -2), (key1172, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1020, -2), (key1125, -2), (key1125, -2), (key1017, -2)]

theorem rawRowCheck11713 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form18 = rawRow11713 := by decide +kernel

def row11713 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

theorem rowCheck11713 : row11713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11713 := by decide +kernel

theorem rowEval11713 (x : Key → ℝ) : Integer.Sparse.eval row11713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11713, Integer.Sparse.eval_collectBalanced, rawRowCheck11713]

def rawRow11714 : Integer.Sparse Key := [(key2678, -4), (key2678, -4), (key2687, -4), (key2812, -4), (key2816, -4), (key2816, -4), (key2709, 6), (key2713, 6), (key2713, 6), (key2862, 6)]

theorem rawRowCheck11714 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form19 = rawRow11714 := by decide +kernel

def row11714 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11714 : row11714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11714 := by decide +kernel

theorem rowEval11714 (x : Key → ℝ) : Integer.Sparse.eval row11714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11714, Integer.Sparse.eval_collectBalanced, rawRowCheck11714]

def rawRow11715 : Integer.Sparse Key := [(key2678, -4), (key2687, -4), (key2678, -4), (key2816, -4), (key2812, -4), (key2816, -4), (key2713, 6), (key2709, 6), (key2713, 6), (key2862, 6)]

theorem rawRowCheck11715 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form19 = rawRow11715 := by decide +kernel

def row11715 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11715 : row11715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11715 := by decide +kernel

theorem rowEval11715 (x : Key → ℝ) : Integer.Sparse.eval row11715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11715, Integer.Sparse.eval_collectBalanced, rawRowCheck11715]

def rawRow11716 : Integer.Sparse Key := [(key2687, -4), (key2678, -4), (key2678, -4), (key2816, -4), (key2816, -4), (key2812, -4), (key2713, 6), (key2713, 6), (key2709, 6), (key2862, 6)]

theorem rawRowCheck11716 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form19 = rawRow11716 := by decide +kernel

def row11716 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11716 : row11716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11716 := by decide +kernel

theorem rowEval11716 (x : Key → ℝ) : Integer.Sparse.eval row11716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11716, Integer.Sparse.eval_collectBalanced, rawRowCheck11716]

def rawRow11717 : Integer.Sparse Key := [(key2678, -4), (key2812, -4), (key2816, -4), (key2678, -4), (key2687, -4), (key2816, -4), (key2709, 6), (key2713, 6), (key2862, 6), (key2713, 6)]

theorem rawRowCheck11717 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form19 = rawRow11717 := by decide +kernel

def row11717 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11717 : row11717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11717 := by decide +kernel

theorem rowEval11717 (x : Key → ℝ) : Integer.Sparse.eval row11717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11717, Integer.Sparse.eval_collectBalanced, rawRowCheck11717]

def rawRow11718 : Integer.Sparse Key := [(key2678, -4), (key2816, -4), (key2812, -4), (key2687, -4), (key2678, -4), (key2816, -4), (key2713, 6), (key2709, 6), (key2862, 6), (key2713, 6)]

theorem rawRowCheck11718 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form19 = rawRow11718 := by decide +kernel

def row11718 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11718 : row11718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11718 := by decide +kernel

theorem rowEval11718 (x : Key → ℝ) : Integer.Sparse.eval row11718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11718, Integer.Sparse.eval_collectBalanced, rawRowCheck11718]

def rawRow11719 : Integer.Sparse Key := [(key2812, -4), (key2678, -4), (key2816, -4), (key2678, -4), (key2816, -4), (key2687, -4), (key2709, 6), (key2862, 6), (key2713, 6), (key2713, 6)]

theorem rawRowCheck11719 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form19 = rawRow11719 := by decide +kernel

def row11719 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11719 : row11719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11719 := by decide +kernel

theorem rowEval11719 (x : Key → ℝ) : Integer.Sparse.eval row11719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11719, Integer.Sparse.eval_collectBalanced, rawRowCheck11719]

def rawRow11720 : Integer.Sparse Key := [(key2812, -4), (key2816, -4), (key2678, -4), (key2816, -4), (key2678, -4), (key2687, -4), (key2862, 6), (key2709, 6), (key2713, 6), (key2713, 6)]

theorem rawRowCheck11720 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form19 = rawRow11720 := by decide +kernel

def row11720 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11720 : row11720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11720 := by decide +kernel

theorem rowEval11720 (x : Key → ℝ) : Integer.Sparse.eval row11720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11720, Integer.Sparse.eval_collectBalanced, rawRowCheck11720]

def rawRow11721 : Integer.Sparse Key := [(key2816, -4), (key2678, -4), (key2812, -4), (key2687, -4), (key2816, -4), (key2678, -4), (key2713, 6), (key2862, 6), (key2709, 6), (key2713, 6)]

theorem rawRowCheck11721 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form19 = rawRow11721 := by decide +kernel

def row11721 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11721 : row11721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11721 := by decide +kernel

theorem rowEval11721 (x : Key → ℝ) : Integer.Sparse.eval row11721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11721, Integer.Sparse.eval_collectBalanced, rawRowCheck11721]

def rawRow11722 : Integer.Sparse Key := [(key2816, -4), (key2812, -4), (key2678, -4), (key2816, -4), (key2687, -4), (key2678, -4), (key2862, 6), (key2713, 6), (key2709, 6), (key2713, 6)]

theorem rawRowCheck11722 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form19 = rawRow11722 := by decide +kernel

def row11722 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11722 : row11722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11722 := by decide +kernel

theorem rowEval11722 (x : Key → ℝ) : Integer.Sparse.eval row11722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11722, Integer.Sparse.eval_collectBalanced, rawRowCheck11722]

def rawRow11723 : Integer.Sparse Key := [(key2687, -4), (key2816, -4), (key2816, -4), (key2678, -4), (key2678, -4), (key2812, -4), (key2713, 6), (key2713, 6), (key2862, 6), (key2709, 6)]

theorem rawRowCheck11723 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form19 = rawRow11723 := by decide +kernel

def row11723 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11723 : row11723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11723 := by decide +kernel

theorem rowEval11723 (x : Key → ℝ) : Integer.Sparse.eval row11723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11723, Integer.Sparse.eval_collectBalanced, rawRowCheck11723]

def rawRow11724 : Integer.Sparse Key := [(key2816, -4), (key2687, -4), (key2816, -4), (key2678, -4), (key2812, -4), (key2678, -4), (key2713, 6), (key2862, 6), (key2713, 6), (key2709, 6)]

theorem rawRowCheck11724 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form19 = rawRow11724 := by decide +kernel

def row11724 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11724 : row11724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11724 := by decide +kernel

theorem rowEval11724 (x : Key → ℝ) : Integer.Sparse.eval row11724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11724, Integer.Sparse.eval_collectBalanced, rawRowCheck11724]

def rawRow11725 : Integer.Sparse Key := [(key2816, -4), (key2816, -4), (key2687, -4), (key2812, -4), (key2678, -4), (key2678, -4), (key2862, 6), (key2713, 6), (key2713, 6), (key2709, 6)]

theorem rawRowCheck11725 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form19 = rawRow11725 := by decide +kernel

def row11725 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

theorem rowCheck11725 : row11725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11725 := by decide +kernel

theorem rowEval11725 (x : Key → ℝ) : Integer.Sparse.eval row11725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11725, Integer.Sparse.eval_collectBalanced, rawRowCheck11725]

def rawRow11726 : Integer.Sparse Key := [(key1936, 6), (key1937, 6), (key1937, 6), (key1949, 6), (key1940, -24)]

theorem rawRowCheck11726 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form20 = rawRow11726 := by decide +kernel

def row11726 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11726 : row11726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11726 := by decide +kernel

theorem rowEval11726 (x : Key → ℝ) : Integer.Sparse.eval row11726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11726, Integer.Sparse.eval_collectBalanced, rawRowCheck11726]

def rawRow11727 : Integer.Sparse Key := [(key1937, 6), (key1936, 6), (key1937, 6), (key1949, 6), (key1940, -24)]

theorem rawRowCheck11727 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form20 = rawRow11727 := by decide +kernel

def row11727 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11727 : row11727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11727 := by decide +kernel

theorem rowEval11727 (x : Key → ℝ) : Integer.Sparse.eval row11727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11727, Integer.Sparse.eval_collectBalanced, rawRowCheck11727]

def rawRow11728 : Integer.Sparse Key := [(key1937, 6), (key1937, 6), (key1936, 6), (key1949, 6), (key1940, -24)]

theorem rawRowCheck11728 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form20 = rawRow11728 := by decide +kernel

def row11728 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11728 : row11728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11728 := by decide +kernel

theorem rowEval11728 (x : Key → ℝ) : Integer.Sparse.eval row11728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11728, Integer.Sparse.eval_collectBalanced, rawRowCheck11728]

def rawRow11729 : Integer.Sparse Key := [(key1936, 6), (key1937, 6), (key1949, 6), (key1937, 6), (key1940, -24)]

theorem rawRowCheck11729 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form20 = rawRow11729 := by decide +kernel

def row11729 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11729 : row11729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11729 := by decide +kernel

theorem rowEval11729 (x : Key → ℝ) : Integer.Sparse.eval row11729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11729, Integer.Sparse.eval_collectBalanced, rawRowCheck11729]

def rawRow11730 : Integer.Sparse Key := [(key1937, 6), (key1936, 6), (key1949, 6), (key1937, 6), (key1940, -24)]

theorem rawRowCheck11730 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form20 = rawRow11730 := by decide +kernel

def row11730 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11730 : row11730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11730 := by decide +kernel

theorem rowEval11730 (x : Key → ℝ) : Integer.Sparse.eval row11730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11730, Integer.Sparse.eval_collectBalanced, rawRowCheck11730]

def rawRow11731 : Integer.Sparse Key := [(key1936, 6), (key1949, 6), (key1937, 6), (key1937, 6), (key1940, -24)]

theorem rawRowCheck11731 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form20 = rawRow11731 := by decide +kernel

def row11731 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11731 : row11731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11731 := by decide +kernel

theorem rowEval11731 (x : Key → ℝ) : Integer.Sparse.eval row11731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck11731, Integer.Sparse.eval_collectBalanced, rawRowCheck11731]

def rawRow11732 : Integer.Sparse Key := [(key1949, 6), (key1936, 6), (key1937, 6), (key1937, 6), (key1940, -24)]

theorem rawRowCheck11732 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form20 = rawRow11732 := by decide +kernel

def row11732 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11732 : row11732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11732 := by decide +kernel

theorem rowEval11732 (x : Key → ℝ) : Integer.Sparse.eval row11732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11732, Integer.Sparse.eval_collectBalanced, rawRowCheck11732]

def rawRow11733 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1936, 6), (key1937, 6), (key1940, -24)]

theorem rawRowCheck11733 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form20 = rawRow11733 := by decide +kernel

def row11733 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11733 : row11733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11733 := by decide +kernel

theorem rowEval11733 (x : Key → ℝ) : Integer.Sparse.eval row11733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11733, Integer.Sparse.eval_collectBalanced, rawRowCheck11733]

def rawRow11734 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1936, 6), (key1937, 6), (key1940, -24)]

theorem rawRowCheck11734 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form20 = rawRow11734 := by decide +kernel

def row11734 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11734 : row11734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11734 := by decide +kernel

theorem rowEval11734 (x : Key → ℝ) : Integer.Sparse.eval row11734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11734, Integer.Sparse.eval_collectBalanced, rawRowCheck11734]

def rawRow11735 : Integer.Sparse Key := [(key1937, 6), (key1937, 6), (key1949, 6), (key1936, 6), (key1940, -24)]

theorem rawRowCheck11735 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form20 = rawRow11735 := by decide +kernel

def row11735 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11735 : row11735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11735 := by decide +kernel

theorem rowEval11735 (x : Key → ℝ) : Integer.Sparse.eval row11735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11735, Integer.Sparse.eval_collectBalanced, rawRowCheck11735]

def rawRow11736 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1937, 6), (key1936, 6), (key1940, -24)]

theorem rawRowCheck11736 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form20 = rawRow11736 := by decide +kernel

def row11736 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11736 : row11736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11736 := by decide +kernel

theorem rowEval11736 (x : Key → ℝ) : Integer.Sparse.eval row11736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck11736, Integer.Sparse.eval_collectBalanced, rawRowCheck11736]

def rawRow11737 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1937, 6), (key1936, 6), (key1940, -24)]

theorem rawRowCheck11737 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form20 = rawRow11737 := by decide +kernel

def row11737 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

theorem rowCheck11737 : row11737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11737 := by decide +kernel

theorem rowEval11737 (x : Key → ℝ) : Integer.Sparse.eval row11737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck11737, Integer.Sparse.eval_collectBalanced, rawRowCheck11737]

def rawRow11738 : Integer.Sparse Key := [(key2624, 1), (key2627, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2636, 1), (key2698, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2722, 1), (key2851, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2866, 1), (key2971, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2974, 1), (key2981, 1), (key2645, -2), (key2645, -2), (key2651, -2), (key2734, -2), (key2734, -2), (key2745, -2), (key2892, -2), (key2895, -2), (key2892, -2), (key2902, -2), (key2895, -2), (key2902, -2)]

theorem rawRowCheck11738 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form21 = rawRow11738 := by decide +kernel

def row11738 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11738 : row11738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11738 := by decide +kernel

theorem rowEval11738 (x : Key → ℝ) : Integer.Sparse.eval row11738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11738, Integer.Sparse.eval_collectBalanced, rawRowCheck11738]

def rawRow11739 : Integer.Sparse Key := [(key2627, 1), (key2624, 1), (key2636, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2971, 1), (key2981, 1), (key2974, 1), (key2645, -2), (key2651, -2), (key2645, -2), (key2734, -2), (key2745, -2), (key2734, -2), (key2895, -2), (key2892, -2), (key2902, -2), (key2892, -2), (key2902, -2), (key2895, -2)]

theorem rawRowCheck11739 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form21 = rawRow11739 := by decide +kernel

def row11739 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11739 : row11739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11739 := by decide +kernel

theorem rowEval11739 (x : Key → ℝ) : Integer.Sparse.eval row11739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11739, Integer.Sparse.eval_collectBalanced, rawRowCheck11739]

def rawRow11740 : Integer.Sparse Key := [(key2636, 1), (key2636, 1), (key2627, 1), (key2627, 1), (key2624, 1), (key2624, 1), (key2722, 1), (key2722, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1), (key2866, 1), (key2866, 1), (key2856, 1), (key2856, 1), (key2851, 1), (key2851, 1), (key2981, 1), (key2981, 1), (key2974, 1), (key2974, 1), (key2971, 1), (key2971, 1), (key2651, -2), (key2645, -2), (key2645, -2), (key2745, -2), (key2734, -2), (key2734, -2), (key2902, -2), (key2902, -2), (key2895, -2), (key2895, -2), (key2892, -2), (key2892, -2)]

theorem rawRowCheck11740 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form21 = rawRow11740 := by decide +kernel

def row11740 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11740 : row11740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11740 := by decide +kernel

theorem rowEval11740 (x : Key → ℝ) : Integer.Sparse.eval row11740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11740, Integer.Sparse.eval_collectBalanced, rawRowCheck11740]

def rawRow11741 : Integer.Sparse Key := [(key2698, 1), (key2701, 1), (key2851, 1), (key2856, 1), (key2971, 1), (key2974, 1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2627, 1), (key2636, 1), (key2701, 1), (key2722, 1), (key2856, 1), (key2866, 1), (key2734, -2), (key2892, -2), (key2895, -2), (key2645, -2), (key2892, -2), (key2902, -2), (key2645, -2), (key2651, -2), (key2734, -2), (key2745, -2), (key2895, -2), (key2902, -2)]

theorem rawRowCheck11741 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form21 = rawRow11741 := by decide +kernel

def row11741 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11741 : row11741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11741 := by decide +kernel

theorem rowEval11741 (x : Key → ℝ) : Integer.Sparse.eval row11741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11741, Integer.Sparse.eval_collectBalanced, rawRowCheck11741]

def rawRow11742 : Integer.Sparse Key := [(key2701, 1), (key2698, 1), (key2856, 1), (key2851, 1), (key2974, 1), (key2971, 1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2636, 1), (key2627, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2856, 1), (key2734, -2), (key2895, -2), (key2892, -2), (key2645, -2), (key2902, -2), (key2892, -2), (key2651, -2), (key2645, -2), (key2745, -2), (key2734, -2), (key2902, -2), (key2895, -2)]

theorem rawRowCheck11742 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form21 = rawRow11742 := by decide +kernel

def row11742 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11742 : row11742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11742 := by decide +kernel

theorem rowEval11742 (x : Key → ℝ) : Integer.Sparse.eval row11742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11742, Integer.Sparse.eval_collectBalanced, rawRowCheck11742]

def rawRow11743 : Integer.Sparse Key := [(key2851, 1), (key2971, 1), (key2698, 1), (key2974, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2892, -2), (key2734, -2), (key2895, -2), (key2892, -2), (key2645, -2), (key2902, -2), (key2734, -2), (key2895, -2), (key2645, -2), (key2902, -2), (key2651, -2), (key2745, -2)]

theorem rawRowCheck11743 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form21 = rawRow11743 := by decide +kernel

def row11743 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11743 : row11743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11743 := by decide +kernel

theorem rowEval11743 (x : Key → ℝ) : Integer.Sparse.eval row11743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck11743, Integer.Sparse.eval_collectBalanced, rawRowCheck11743]

def rawRow11744 : Integer.Sparse Key := [(key2971, 1), (key2851, 1), (key2974, 1), (key2698, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2722, 1), (key2636, 1), (key2892, -2), (key2895, -2), (key2734, -2), (key2892, -2), (key2902, -2), (key2645, -2), (key2895, -2), (key2734, -2), (key2902, -2), (key2645, -2), (key2745, -2), (key2651, -2)]

theorem rawRowCheck11744 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form21 = rawRow11744 := by decide +kernel

def row11744 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11744 : row11744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11744 := by decide +kernel

theorem rowEval11744 (x : Key → ℝ) : Integer.Sparse.eval row11744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11744, Integer.Sparse.eval_collectBalanced, rawRowCheck11744]

def rawRow11745 : Integer.Sparse Key := [(key2856, 1), (key2974, 1), (key2701, 1), (key2971, 1), (key2698, 1), (key2851, 1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2722, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2627, 1), (key2701, 1), (key2895, -2), (key2734, -2), (key2892, -2), (key2902, -2), (key2645, -2), (key2892, -2), (key2745, -2), (key2902, -2), (key2651, -2), (key2895, -2), (key2645, -2), (key2734, -2)]

theorem rawRowCheck11745 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form21 = rawRow11745 := by decide +kernel

def row11745 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11745 : row11745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11745 := by decide +kernel

theorem rowEval11745 (x : Key → ℝ) : Integer.Sparse.eval row11745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11745, Integer.Sparse.eval_collectBalanced, rawRowCheck11745]

def rawRow11746 : Integer.Sparse Key := [(key2974, 1), (key2856, 1), (key2971, 1), (key2701, 1), (key2851, 1), (key2698, 1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2866, 1), (key2722, 1), (key2856, 1), (key2636, 1), (key2701, 1), (key2627, 1), (key2895, -2), (key2892, -2), (key2734, -2), (key2902, -2), (key2892, -2), (key2645, -2), (key2902, -2), (key2745, -2), (key2895, -2), (key2651, -2), (key2734, -2), (key2645, -2)]

theorem rawRowCheck11746 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form21 = rawRow11746 := by decide +kernel

def row11746 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11746 : row11746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11746 := by decide +kernel

theorem rowEval11746 (x : Key → ℝ) : Integer.Sparse.eval row11746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11746, Integer.Sparse.eval_collectBalanced, rawRowCheck11746]

def rawRow11747 : Integer.Sparse Key := [(key2722, 1), (key2722, 1), (key2866, 1), (key2866, 1), (key2981, 1), (key2981, 1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2627, 1), (key2627, 1), (key2701, 1), (key2701, 1), (key2971, 1), (key2971, 1), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1), (key2745, -2), (key2902, -2), (key2902, -2), (key2651, -2), (key2895, -2), (key2895, -2), (key2645, -2), (key2645, -2), (key2734, -2), (key2734, -2), (key2892, -2), (key2892, -2)]

theorem rawRowCheck11747 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form21 = rawRow11747 := by decide +kernel

def row11747 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11747 : row11747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11747 := by decide +kernel

theorem rowEval11747 (x : Key → ℝ) : Integer.Sparse.eval row11747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11747, Integer.Sparse.eval_collectBalanced, rawRowCheck11747]

def rawRow11748 : Integer.Sparse Key := [(key2866, 1), (key2981, 1), (key2722, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2902, -2), (key2745, -2), (key2902, -2), (key2895, -2), (key2651, -2), (key2895, -2), (key2734, -2), (key2892, -2), (key2645, -2), (key2892, -2), (key2645, -2), (key2734, -2)]

theorem rawRowCheck11748 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form21 = rawRow11748 := by decide +kernel

def row11748 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11748 : row11748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11748 := by decide +kernel

theorem rowEval11748 (x : Key → ℝ) : Integer.Sparse.eval row11748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck11748, Integer.Sparse.eval_collectBalanced, rawRowCheck11748]

def rawRow11749 : Integer.Sparse Key := [(key2981, 1), (key2866, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2722, 1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2971, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2627, 1), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1), (key2902, -2), (key2902, -2), (key2745, -2), (key2895, -2), (key2895, -2), (key2651, -2), (key2892, -2), (key2734, -2), (key2892, -2), (key2645, -2), (key2734, -2), (key2645, -2)]

theorem rawRowCheck11749 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form21 = rawRow11749 := by decide +kernel

def row11749 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11749 : row11749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11749 := by decide +kernel

theorem rowEval11749 (x : Key → ℝ) : Integer.Sparse.eval row11749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck11749, Integer.Sparse.eval_collectBalanced, rawRowCheck11749]

def rawRow11750 : Integer.Sparse Key := [(key2608, -2), (key2611, -2), (key2611, -2), (key2801, -2), (key2804, -2), (key2801, -2), (key2825, -2), (key2804, -2), (key2825, -2), (key2947, -2), (key2947, -2), (key2958, -2), (key2624, 1), (key2627, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2636, 1), (key2698, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2722, 1), (key2851, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2866, 1), (key2971, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2974, 1), (key2981, 1)]

theorem rawRowCheck11750 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form22 = rawRow11750 := by decide +kernel

def row11750 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11750 : row11750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11750 := by decide +kernel

theorem rowEval11750 (x : Key → ℝ) : Integer.Sparse.eval row11750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11750, Integer.Sparse.eval_collectBalanced, rawRowCheck11750]

def rawRow11751 : Integer.Sparse Key := [(key2611, -2), (key2608, -2), (key2611, -2), (key2804, -2), (key2801, -2), (key2825, -2), (key2801, -2), (key2825, -2), (key2804, -2), (key2947, -2), (key2958, -2), (key2947, -2), (key2627, 1), (key2624, 1), (key2636, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2971, 1), (key2981, 1), (key2974, 1)]

theorem rawRowCheck11751 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form22 = rawRow11751 := by decide +kernel

def row11751 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11751 : row11751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11751 := by decide +kernel

theorem rowEval11751 (x : Key → ℝ) : Integer.Sparse.eval row11751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11751, Integer.Sparse.eval_collectBalanced, rawRowCheck11751]

def rawRow11752 : Integer.Sparse Key := [(key2611, -2), (key2611, -2), (key2608, -2), (key2825, -2), (key2825, -2), (key2804, -2), (key2804, -2), (key2801, -2), (key2801, -2), (key2958, -2), (key2947, -2), (key2947, -2), (key2636, 1), (key2636, 1), (key2627, 1), (key2627, 1), (key2624, 1), (key2624, 1), (key2722, 1), (key2722, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1), (key2866, 1), (key2866, 1), (key2856, 1), (key2856, 1), (key2851, 1), (key2851, 1), (key2981, 1), (key2981, 1), (key2974, 1), (key2974, 1), (key2971, 1), (key2971, 1)]

theorem rawRowCheck11752 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form22 = rawRow11752 := by decide +kernel

def row11752 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11752 : row11752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11752 := by decide +kernel

theorem rowEval11752 (x : Key → ℝ) : Integer.Sparse.eval row11752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11752, Integer.Sparse.eval_collectBalanced, rawRowCheck11752]

def rawRow11753 : Integer.Sparse Key := [(key2801, -2), (key2804, -2), (key2825, -2), (key2608, -2), (key2611, -2), (key2801, -2), (key2825, -2), (key2947, -2), (key2958, -2), (key2611, -2), (key2804, -2), (key2825, -2), (key2698, 1), (key2701, 1), (key2851, 1), (key2856, 1), (key2971, 1), (key2974, 1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2627, 1), (key2636, 1), (key2701, 1), (key2722, 1), (key2856, 1), (key2866, 1)]

theorem rawRowCheck11753 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form22 = rawRow11753 := by decide +kernel

def row11753 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11753 : row11753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11753 := by decide +kernel

theorem rowEval11753 (x : Key → ℝ) : Integer.Sparse.eval row11753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11753, Integer.Sparse.eval_collectBalanced, rawRowCheck11753]

def rawRow11754 : Integer.Sparse Key := [(key2804, -2), (key2801, -2), (key2825, -2), (key2611, -2), (key2608, -2), (key2825, -2), (key2801, -2), (key2958, -2), (key2947, -2), (key2611, -2), (key2825, -2), (key2804, -2), (key2701, 1), (key2698, 1), (key2856, 1), (key2851, 1), (key2974, 1), (key2971, 1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2636, 1), (key2627, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2856, 1)]

theorem rawRowCheck11754 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form22 = rawRow11754 := by decide +kernel

def row11754 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11754 : row11754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11754 := by decide +kernel

theorem rowEval11754 (x : Key → ℝ) : Integer.Sparse.eval row11754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11754, Integer.Sparse.eval_collectBalanced, rawRowCheck11754]

def rawRow11755 : Integer.Sparse Key := [(key2801, -2), (key2825, -2), (key2804, -2), (key2801, -2), (key2825, -2), (key2608, -2), (key2958, -2), (key2611, -2), (key2825, -2), (key2804, -2), (key2611, -2), (key2825, -2), (key2851, 1), (key2971, 1), (key2698, 1), (key2974, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2722, 1)]

theorem rawRowCheck11755 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form22 = rawRow11755 := by decide +kernel

def row11755 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -8), (key2851, 2), (key2856, 2), (key2866, 2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11755 : row11755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11755 := by decide +kernel

theorem rowEval11755 (x : Key → ℝ) : Integer.Sparse.eval row11755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11755, Integer.Sparse.eval_collectBalanced, rawRowCheck11755]

def rawRow11756 : Integer.Sparse Key := [(key2825, -2), (key2801, -2), (key2804, -2), (key2825, -2), (key2801, -2), (key2958, -2), (key2608, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2971, 1), (key2851, 1), (key2974, 1), (key2698, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2722, 1), (key2636, 1)]

theorem rawRowCheck11756 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form22 = rawRow11756 := by decide +kernel

def row11756 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -8), (key2851, 2), (key2856, 2), (key2866, 2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11756 : row11756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11756 := by decide +kernel

theorem rowEval11756 (x : Key → ℝ) : Integer.Sparse.eval row11756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck11756, Integer.Sparse.eval_collectBalanced, rawRowCheck11756]

def rawRow11757 : Integer.Sparse Key := [(key2804, -2), (key2825, -2), (key2801, -2), (key2947, -2), (key2958, -2), (key2611, -2), (key2825, -2), (key2608, -2), (key2801, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2856, 1), (key2974, 1), (key2701, 1), (key2971, 1), (key2698, 1), (key2851, 1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2722, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2627, 1), (key2701, 1)]

theorem rawRowCheck11757 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form22 = rawRow11757 := by decide +kernel

def row11757 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11757 : row11757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11757 := by decide +kernel

theorem rowEval11757 (x : Key → ℝ) : Integer.Sparse.eval row11757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11757, Integer.Sparse.eval_collectBalanced, rawRowCheck11757]

def rawRow11758 : Integer.Sparse Key := [(key2825, -2), (key2804, -2), (key2801, -2), (key2958, -2), (key2947, -2), (key2825, -2), (key2611, -2), (key2801, -2), (key2608, -2), (key2825, -2), (key2804, -2), (key2611, -2), (key2974, 1), (key2856, 1), (key2971, 1), (key2701, 1), (key2851, 1), (key2698, 1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2866, 1), (key2722, 1), (key2856, 1), (key2636, 1), (key2701, 1), (key2627, 1)]

theorem rawRowCheck11758 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form22 = rawRow11758 := by decide +kernel

def row11758 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11758 : row11758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11758 := by decide +kernel

theorem rowEval11758 (x : Key → ℝ) : Integer.Sparse.eval row11758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck11758, Integer.Sparse.eval_collectBalanced, rawRowCheck11758]

def rawRow11759 : Integer.Sparse Key := [(key2947, -2), (key2947, -2), (key2958, -2), (key2611, -2), (key2611, -2), (key2804, -2), (key2804, -2), (key2825, -2), (key2825, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2722, 1), (key2722, 1), (key2866, 1), (key2866, 1), (key2981, 1), (key2981, 1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2627, 1), (key2627, 1), (key2701, 1), (key2701, 1), (key2971, 1), (key2971, 1), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

theorem rawRowCheck11759 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form22 = rawRow11759 := by decide +kernel

def row11759 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11759 : row11759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11759 := by decide +kernel

theorem rowEval11759 (x : Key → ℝ) : Integer.Sparse.eval row11759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11759, Integer.Sparse.eval_collectBalanced, rawRowCheck11759]

def rawRow11760 : Integer.Sparse Key := [(key2947, -2), (key2958, -2), (key2947, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2866, 1), (key2981, 1), (key2722, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

theorem rawRowCheck11760 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form22 = rawRow11760 := by decide +kernel

def row11760 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11760 : row11760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11760 := by decide +kernel

theorem rowEval11760 (x : Key → ℝ) : Integer.Sparse.eval row11760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11760, Integer.Sparse.eval_collectBalanced, rawRowCheck11760]

def rawRow11761 : Integer.Sparse Key := [(key2958, -2), (key2947, -2), (key2947, -2), (key2825, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2611, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key2981, 1), (key2866, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2722, 1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2971, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2627, 1), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

theorem rawRowCheck11761 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form22 = rawRow11761 := by decide +kernel

def row11761 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck11761 : row11761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11761 := by decide +kernel

theorem rowEval11761 (x : Key → ℝ) : Integer.Sparse.eval row11761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck11761, Integer.Sparse.eval_collectBalanced, rawRowCheck11761]

def rawRow11762 : Integer.Sparse Key := [(key2624, -2), (key2627, -2), (key2636, -2), (key2698, -2), (key2701, -2), (key2851, -2), (key2971, -2), (key2856, -2), (key2974, -2), (key2722, -2), (key2866, -2), (key2981, -2), (key2608, 1), (key2611, 1), (key2624, 1), (key2636, 1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

theorem rawRowCheck11762 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form22 = rawRow11762 := by decide +kernel

def row11762 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11762 : row11762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11762 := by decide +kernel

theorem rowEval11762 (x : Key → ℝ) : Integer.Sparse.eval row11762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11762, Integer.Sparse.eval_collectBalanced, rawRowCheck11762]

def rawRow11763 : Integer.Sparse Key := [(key2627, -2), (key2624, -2), (key2636, -2), (key2701, -2), (key2698, -2), (key2971, -2), (key2851, -2), (key2974, -2), (key2856, -2), (key2722, -2), (key2981, -2), (key2866, -2), (key2611, 1), (key2608, 1), (key2636, 1), (key2624, 1), (key2651, 1), (key2645, 1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2790, 1), (key2778, 1), (key2825, 1), (key2801, 1), (key2902, 1), (key2895, 1), (key2941, 1), (key2935, 1), (key2958, 1), (key2947, 1), (key2981, 1), (key2974, 1)]

theorem rawRowCheck11763 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form22 = rawRow11763 := by decide +kernel

def row11763 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11763 : row11763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11763 := by decide +kernel

theorem rowEval11763 (x : Key → ℝ) : Integer.Sparse.eval row11763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11763, Integer.Sparse.eval_collectBalanced, rawRowCheck11763]

def rawRow11764 : Integer.Sparse Key := [(key2624, -2), (key2636, -2), (key2627, -2), (key2851, -2), (key2856, -2), (key2698, -2), (key2974, -2), (key2701, -2), (key2971, -2), (key2866, -2), (key2722, -2), (key2981, -2), (key2624, 1), (key2636, 1), (key2608, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2801, 1), (key2895, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2947, 1), (key2974, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2958, 1)]

theorem rawRowCheck11764 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form22 = rawRow11764 := by decide +kernel

def row11764 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11764 : row11764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11764 := by decide +kernel

theorem rowEval11764 (x : Key → ℝ) : Integer.Sparse.eval row11764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11764, Integer.Sparse.eval_collectBalanced, rawRowCheck11764]

def rawRow11765 : Integer.Sparse Key := [(key2636, -2), (key2624, -2), (key2627, -2), (key2856, -2), (key2851, -2), (key2974, -2), (key2698, -2), (key2971, -2), (key2701, -2), (key2866, -2), (key2981, -2), (key2722, -2), (key2636, 1), (key2624, 1), (key2651, 1), (key2608, 1), (key2636, 1), (key2611, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2825, 1), (key2790, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2958, 1), (key2941, 1)]

theorem rawRowCheck11765 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form22 = rawRow11765 := by decide +kernel

def row11765 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11765 : row11765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11765 := by decide +kernel

theorem rowEval11765 (x : Key → ℝ) : Integer.Sparse.eval row11765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11765, Integer.Sparse.eval_collectBalanced, rawRowCheck11765]

def rawRow11766 : Integer.Sparse Key := [(key2627, -2), (key2636, -2), (key2624, -2), (key2971, -2), (key2974, -2), (key2701, -2), (key2856, -2), (key2698, -2), (key2851, -2), (key2981, -2), (key2722, -2), (key2866, -2), (key2645, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2608, 1), (key2624, 1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2825, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2778, 1), (key2801, 1), (key2958, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2935, 1), (key2947, 1)]

theorem rawRowCheck11766 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form22 = rawRow11766 := by decide +kernel

def row11766 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11766 : row11766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11766 := by decide +kernel

theorem rowEval11766 (x : Key → ℝ) : Integer.Sparse.eval row11766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11766, Integer.Sparse.eval_collectBalanced, rawRowCheck11766]

def rawRow11767 : Integer.Sparse Key := [(key2636, -2), (key2627, -2), (key2624, -2), (key2974, -2), (key2971, -2), (key2856, -2), (key2701, -2), (key2851, -2), (key2698, -2), (key2981, -2), (key2866, -2), (key2722, -2), (key2651, 1), (key2645, 1), (key2636, 1), (key2611, 1), (key2624, 1), (key2608, 1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2902, 1), (key2825, 1), (key2895, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2958, 1), (key2974, 1), (key2941, 1), (key2947, 1), (key2935, 1)]

theorem rawRowCheck11767 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form22 = rawRow11767 := by decide +kernel

def row11767 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11767 : row11767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11767 := by decide +kernel

theorem rowEval11767 (x : Key → ℝ) : Integer.Sparse.eval row11767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11767, Integer.Sparse.eval_collectBalanced, rawRowCheck11767]

def rawRow11768 : Integer.Sparse Key := [(key2698, -2), (key2701, -2), (key2722, -2), (key2624, -2), (key2627, -2), (key2851, -2), (key2971, -2), (key2866, -2), (key2981, -2), (key2636, -2), (key2856, -2), (key2974, -2), (key2663, 1), (key2666, 1), (key2698, 1), (key2734, 1), (key2722, 1), (key2745, 1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2745, 1), (key2895, 1), (key2902, 1)]

theorem rawRowCheck11768 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form22 = rawRow11768 := by decide +kernel

def row11768 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11768 : row11768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11768 := by decide +kernel

theorem rowEval11768 (x : Key → ℝ) : Integer.Sparse.eval row11768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11768, Integer.Sparse.eval_collectBalanced, rawRowCheck11768]

def rawRow11769 : Integer.Sparse Key := [(key2701, -2), (key2698, -2), (key2722, -2), (key2627, -2), (key2624, -2), (key2971, -2), (key2851, -2), (key2981, -2), (key2866, -2), (key2636, -2), (key2974, -2), (key2856, -2), (key2666, 1), (key2663, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2722, 1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2651, 1), (key2645, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2895, 1)]

theorem rawRowCheck11769 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form22 = rawRow11769 := by decide +kernel

def row11769 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11769 : row11769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11769 := by decide +kernel

theorem rowEval11769 (x : Key → ℝ) : Integer.Sparse.eval row11769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11769, Integer.Sparse.eval_collectBalanced, rawRowCheck11769]

def rawRow11770 : Integer.Sparse Key := [(key2698, -2), (key2722, -2), (key2701, -2), (key2851, -2), (key2866, -2), (key2624, -2), (key2981, -2), (key2627, -2), (key2971, -2), (key2856, -2), (key2636, -2), (key2974, -2), (key2698, 1), (key2722, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2734, 1), (key2895, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2745, 1)]

theorem rawRowCheck11770 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form22 = rawRow11770 := by decide +kernel

def row11770 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11770 : row11770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11770 := by decide +kernel

theorem rowEval11770 (x : Key → ℝ) : Integer.Sparse.eval row11770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11770, Integer.Sparse.eval_collectBalanced, rawRowCheck11770]

def rawRow11771 : Integer.Sparse Key := [(key2722, -2), (key2698, -2), (key2701, -2), (key2866, -2), (key2851, -2), (key2981, -2), (key2624, -2), (key2971, -2), (key2627, -2), (key2856, -2), (key2974, -2), (key2636, -2), (key2722, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2734, 1), (key2666, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2745, 1), (key2651, 1)]

theorem rawRowCheck11771 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form22 = rawRow11771 := by decide +kernel

def row11771 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11771 : row11771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11771 := by decide +kernel

theorem rowEval11771 (x : Key → ℝ) : Integer.Sparse.eval row11771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck11771, Integer.Sparse.eval_collectBalanced, rawRowCheck11771]

def rawRow11772 : Integer.Sparse Key := [(key2701, -2), (key2722, -2), (key2698, -2), (key2971, -2), (key2981, -2), (key2627, -2), (key2866, -2), (key2624, -2), (key2851, -2), (key2974, -2), (key2636, -2), (key2856, -2), (key2734, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2663, 1), (key2698, 1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2745, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2645, 1), (key2734, 1)]

theorem rawRowCheck11772 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form22 = rawRow11772 := by decide +kernel

def row11772 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11772 : row11772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11772 := by decide +kernel

theorem rowEval11772 (x : Key → ℝ) : Integer.Sparse.eval row11772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck11772, Integer.Sparse.eval_collectBalanced, rawRowCheck11772]

def rawRow11773 : Integer.Sparse Key := [(key2722, -2), (key2701, -2), (key2698, -2), (key2981, -2), (key2971, -2), (key2866, -2), (key2627, -2), (key2851, -2), (key2624, -2), (key2974, -2), (key2856, -2), (key2636, -2), (key2745, 1), (key2734, 1), (key2722, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2902, 1), (key2745, 1), (key2895, 1), (key2651, 1), (key2734, 1), (key2645, 1)]

theorem rawRowCheck11773 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form22 = rawRow11773 := by decide +kernel

def row11773 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11773 : row11773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11773 := by decide +kernel

theorem rowEval11773 (x : Key → ℝ) : Integer.Sparse.eval row11773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck11773, Integer.Sparse.eval_collectBalanced, rawRowCheck11773]

def rawRow11774 : Integer.Sparse Key := [(key2851, -2), (key2856, -2), (key2866, -2), (key2624, -2), (key2636, -2), (key2698, -2), (key2974, -2), (key2722, -2), (key2981, -2), (key2627, -2), (key2701, -2), (key2971, -2), (key2778, 1), (key2790, 1), (key2801, 1), (key2895, 1), (key2825, 1), (key2902, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2974, 1), (key2722, 1), (key2981, 1), (key2608, 1), (key2651, 1), (key2663, 1), (key2745, 1), (key2941, 1), (key2958, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2722, 1), (key2790, 1), (key2825, 1)]

theorem rawRowCheck11774 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form22 = rawRow11774 := by decide +kernel

def row11774 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11774 : row11774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11774 := by decide +kernel

theorem rowEval11774 (x : Key → ℝ) : Integer.Sparse.eval row11774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11774, Integer.Sparse.eval_collectBalanced, rawRowCheck11774]

def rawRow11775 : Integer.Sparse Key := [(key2856, -2), (key2851, -2), (key2866, -2), (key2636, -2), (key2624, -2), (key2974, -2), (key2698, -2), (key2981, -2), (key2722, -2), (key2627, -2), (key2971, -2), (key2701, -2), (key2790, 1), (key2778, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2825, 1), (key2636, 1), (key2624, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2722, 1), (key2651, 1), (key2608, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2941, 1), (key2636, 1), (key2611, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2790, 1)]

theorem rawRowCheck11775 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form22 = rawRow11775 := by decide +kernel

def row11775 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck11775 : row11775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11775 := by decide +kernel

theorem rowEval11775 (x : Key → ℝ) : Integer.Sparse.eval row11775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck11775, Integer.Sparse.eval_collectBalanced, rawRowCheck11775]

end MUB6.Certificate.GramRows

end OAI

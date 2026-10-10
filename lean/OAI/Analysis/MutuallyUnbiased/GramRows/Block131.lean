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

def rawRow13696 : Integer.Sparse Key := [(key2570, -2), (key2568, -2), (key2575, -2), (key2568, 6), (key2478, -2), (key2470, -2), (key2501, -2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2376, -2), (key2470, -2), (key2404, -2), (key2464, 6), (key2370, -2), (key2839, -2), (key2762, -2)]

theorem rawRowCheck13696 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form2 = rawRow13696 := by decide +kernel

def row13696 : Integer.Sparse Key := [(key2370, -2), (key2388, 2), (key2435, 2), (key2464, 6), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, -2), (key2839, -2)]

theorem rowCheck13696 : row13696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13696 := by decide +kernel

theorem rowEval13696 (x : Key → ℝ) : Integer.Sparse.eval row13696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13696, Integer.Sparse.eval_collectBalanced, rawRowCheck13696]

def rawRow13697 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2570, -2), (key2568, 6), (key2470, -2), (key2501, -2), (key2478, -2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2404, -2), (key2376, -2), (key2470, -2), (key2464, 6), (key2398, -2), (key2583, -2), (key2839, -2)]

theorem rawRowCheck13697 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form2 = rawRow13697 := by decide +kernel

def row13697 : Integer.Sparse Key := [(key2388, 2), (key2398, -2), (key2435, 2), (key2464, 6), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, -2), (key2839, -2)]

theorem rowCheck13697 : row13697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13697 := by decide +kernel

theorem rowEval13697 (x : Key → ℝ) : Integer.Sparse.eval row13697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13697, Integer.Sparse.eval_collectBalanced, rawRowCheck13697]

def rawRow13698 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2570, -2), (key2568, 6), (key2501, -2), (key2470, -2), (key2478, -2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2404, -2), (key2470, -2), (key2376, -2), (key2464, 6), (key2398, -2), (key2839, -2), (key2583, -2)]

theorem rawRowCheck13698 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form2 = rawRow13698 := by decide +kernel

def row13698 : Integer.Sparse Key := [(key2388, 2), (key2398, -2), (key2435, 2), (key2464, 6), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, -2), (key2839, -2)]

theorem rowCheck13698 : row13698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13698 := by decide +kernel

theorem rowEval13698 (x : Key → ℝ) : Integer.Sparse.eval row13698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13698, Integer.Sparse.eval_collectBalanced, rawRowCheck13698]

def rawRow13699 : Integer.Sparse Key := [(key2570, -2), (key2575, -2), (key2568, -2), (key2568, 6), (key2478, -2), (key2501, -2), (key2470, -2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2470, -2), (key2376, -2), (key2404, -2), (key2464, 6), (key2464, -2), (key2370, -2), (key2762, -2)]

theorem rawRowCheck13699 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form2 = rawRow13699 := by decide +kernel

def row13699 : Integer.Sparse Key := [(key2370, -2), (key2388, 2), (key2435, 2), (key2464, 4), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, -2)]

theorem rowCheck13699 : row13699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13699 := by decide +kernel

theorem rowEval13699 (x : Key → ℝ) : Integer.Sparse.eval row13699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13699, Integer.Sparse.eval_collectBalanced, rawRowCheck13699]

def rawRow13700 : Integer.Sparse Key := [(key2575, -2), (key2570, -2), (key2568, -2), (key2568, 6), (key2501, -2), (key2478, -2), (key2470, -2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2470, -2), (key2404, -2), (key2376, -2), (key2464, 6), (key2464, -2), (key2398, -2), (key2583, -2)]

theorem rawRowCheck13700 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form2 = rawRow13700 := by decide +kernel

def row13700 : Integer.Sparse Key := [(key2388, 2), (key2398, -2), (key2435, 2), (key2464, 4), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, -2)]

theorem rowCheck13700 : row13700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13700 := by decide +kernel

theorem rowEval13700 (x : Key → ℝ) : Integer.Sparse.eval row13700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13700, Integer.Sparse.eval_collectBalanced, rawRowCheck13700]

def rawRow13701 : Integer.Sparse Key := [(key2780, 6), (key2665, -2), (key2780, -2), (key2789, -2), (key2803, 6), (key2610, -2), (key2803, -2), (key2824, -2), (key2700, -2), (key2853, -2), (key2855, -2), (key2626, -2), (key2853, -2), (key2865, -2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck13701 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form3 = rawRow13701 := by decide +kernel

def row13701 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13701 : row13701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13701 := by decide +kernel

theorem rowEval13701 (x : Key → ℝ) : Integer.Sparse.eval row13701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13701, Integer.Sparse.eval_collectBalanced, rawRowCheck13701]

def rawRow13702 : Integer.Sparse Key := [(key2780, 6), (key2665, -2), (key2789, -2), (key2780, -2), (key2803, 6), (key2610, -2), (key2824, -2), (key2803, -2), (key2700, -2), (key2855, -2), (key2853, -2), (key2626, -2), (key2865, -2), (key2853, -2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck13702 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form3 = rawRow13702 := by decide +kernel

def row13702 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13702 : row13702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13702 := by decide +kernel

theorem rowEval13702 (x : Key → ℝ) : Integer.Sparse.eval row13702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13702, Integer.Sparse.eval_collectBalanced, rawRowCheck13702]

def rawRow13703 : Integer.Sparse Key := [(key2780, 6), (key2780, -2), (key2665, -2), (key2789, -2), (key2803, 6), (key2803, -2), (key2610, -2), (key2824, -2), (key2853, -2), (key2700, -2), (key2855, -2), (key2853, -2), (key2626, -2), (key2865, -2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

theorem rawRowCheck13703 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form3 = rawRow13703 := by decide +kernel

def row13703 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13703 : row13703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13703 := by decide +kernel

theorem rowEval13703 (x : Key → ℝ) : Integer.Sparse.eval row13703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13703, Integer.Sparse.eval_collectBalanced, rawRowCheck13703]

def rawRow13704 : Integer.Sparse Key := [(key2780, 6), (key2780, -2), (key2789, -2), (key2665, -2), (key2803, 6), (key2803, -2), (key2824, -2), (key2610, -2), (key2853, -2), (key2855, -2), (key2700, -2), (key2853, -2), (key2865, -2), (key2626, -2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

theorem rawRowCheck13704 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form3 = rawRow13704 := by decide +kernel

def row13704 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13704 : row13704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13704 := by decide +kernel

theorem rowEval13704 (x : Key → ℝ) : Integer.Sparse.eval row13704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13704, Integer.Sparse.eval_collectBalanced, rawRowCheck13704]

def rawRow13705 : Integer.Sparse Key := [(key2780, 6), (key2789, -2), (key2665, -2), (key2780, -2), (key2803, 6), (key2824, -2), (key2610, -2), (key2803, -2), (key2855, -2), (key2700, -2), (key2853, -2), (key2865, -2), (key2626, -2), (key2853, -2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck13705 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form3 = rawRow13705 := by decide +kernel

def row13705 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13705 : row13705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13705 := by decide +kernel

theorem rowEval13705 (x : Key → ℝ) : Integer.Sparse.eval row13705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13705, Integer.Sparse.eval_collectBalanced, rawRowCheck13705]

def rawRow13706 : Integer.Sparse Key := [(key2780, 6), (key2789, -2), (key2780, -2), (key2665, -2), (key2803, 6), (key2824, -2), (key2803, -2), (key2610, -2), (key2855, -2), (key2853, -2), (key2700, -2), (key2865, -2), (key2853, -2), (key2626, -2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck13706 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form3 = rawRow13706 := by decide +kernel

def row13706 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13706 : row13706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13706 := by decide +kernel

theorem rowEval13706 (x : Key → ℝ) : Integer.Sparse.eval row13706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13706, Integer.Sparse.eval_collectBalanced, rawRowCheck13706]

def rawRow13707 : Integer.Sparse Key := [(key2789, 6), (key2665, -2), (key2780, -2), (key2780, -2), (key2824, 6), (key2610, -2), (key2803, -2), (key2803, -2), (key2721, -2), (key2865, -2), (key2865, -2), (key2635, -2), (key2855, -2), (key2855, -2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck13707 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form3 = rawRow13707 := by decide +kernel

def row13707 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck13707 : row13707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13707 := by decide +kernel

theorem rowEval13707 (x : Key → ℝ) : Integer.Sparse.eval row13707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13707, Integer.Sparse.eval_collectBalanced, rawRowCheck13707]

def rawRow13708 : Integer.Sparse Key := [(key2789, 6), (key2780, -2), (key2665, -2), (key2780, -2), (key2824, 6), (key2803, -2), (key2610, -2), (key2803, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck13708 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form3 = rawRow13708 := by decide +kernel

def row13708 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck13708 : row13708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13708 := by decide +kernel

theorem rowEval13708 (x : Key → ℝ) : Integer.Sparse.eval row13708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13708, Integer.Sparse.eval_collectBalanced, rawRowCheck13708]

def rawRow13709 : Integer.Sparse Key := [(key2789, 6), (key2780, -2), (key2780, -2), (key2665, -2), (key2824, 6), (key2803, -2), (key2803, -2), (key2610, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck13709 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form3 = rawRow13709 := by decide +kernel

def row13709 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck13709 : row13709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13709 := by decide +kernel

theorem rowEval13709 (x : Key → ℝ) : Integer.Sparse.eval row13709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13709, Integer.Sparse.eval_collectBalanced, rawRowCheck13709]

def rawRow13710 : Integer.Sparse Key := [(key2803, 6), (key2700, -2), (key2853, -2), (key2855, -2), (key2780, 6), (key2626, -2), (key2853, -2), (key2865, -2), (key2665, -2), (key2780, -2), (key2789, -2), (key2610, -2), (key2803, -2), (key2824, -2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck13710 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form3 = rawRow13710 := by decide +kernel

def row13710 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13710 : row13710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13710 := by decide +kernel

theorem rowEval13710 (x : Key → ℝ) : Integer.Sparse.eval row13710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13710, Integer.Sparse.eval_collectBalanced, rawRowCheck13710]

def rawRow13711 : Integer.Sparse Key := [(key2803, 6), (key2700, -2), (key2855, -2), (key2853, -2), (key2780, 6), (key2626, -2), (key2865, -2), (key2853, -2), (key2665, -2), (key2789, -2), (key2780, -2), (key2610, -2), (key2824, -2), (key2803, -2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck13711 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form3 = rawRow13711 := by decide +kernel

def row13711 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13711 : row13711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13711 := by decide +kernel

theorem rowEval13711 (x : Key → ℝ) : Integer.Sparse.eval row13711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13711, Integer.Sparse.eval_collectBalanced, rawRowCheck13711]

def rawRow13712 : Integer.Sparse Key := [(key2803, 6), (key2853, -2), (key2700, -2), (key2855, -2), (key2780, 6), (key2853, -2), (key2626, -2), (key2865, -2), (key2780, -2), (key2665, -2), (key2789, -2), (key2803, -2), (key2610, -2), (key2824, -2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

theorem rawRowCheck13712 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form3 = rawRow13712 := by decide +kernel

def row13712 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13712 : row13712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13712 := by decide +kernel

theorem rowEval13712 (x : Key → ℝ) : Integer.Sparse.eval row13712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13712, Integer.Sparse.eval_collectBalanced, rawRowCheck13712]

def rawRow13713 : Integer.Sparse Key := [(key2803, 6), (key2853, -2), (key2855, -2), (key2700, -2), (key2780, 6), (key2853, -2), (key2865, -2), (key2626, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2803, -2), (key2824, -2), (key2610, -2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

theorem rawRowCheck13713 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form3 = rawRow13713 := by decide +kernel

def row13713 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13713 : row13713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13713 := by decide +kernel

theorem rowEval13713 (x : Key → ℝ) : Integer.Sparse.eval row13713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13713, Integer.Sparse.eval_collectBalanced, rawRowCheck13713]

def rawRow13714 : Integer.Sparse Key := [(key2803, 6), (key2855, -2), (key2700, -2), (key2853, -2), (key2780, 6), (key2865, -2), (key2626, -2), (key2853, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2824, -2), (key2610, -2), (key2803, -2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck13714 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form3 = rawRow13714 := by decide +kernel

def row13714 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13714 : row13714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13714 := by decide +kernel

theorem rowEval13714 (x : Key → ℝ) : Integer.Sparse.eval row13714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13714, Integer.Sparse.eval_collectBalanced, rawRowCheck13714]

def rawRow13715 : Integer.Sparse Key := [(key2803, 6), (key2855, -2), (key2853, -2), (key2700, -2), (key2780, 6), (key2865, -2), (key2853, -2), (key2626, -2), (key2789, -2), (key2780, -2), (key2665, -2), (key2824, -2), (key2803, -2), (key2610, -2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck13715 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form3 = rawRow13715 := by decide +kernel

def row13715 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

theorem rowCheck13715 : row13715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13715 := by decide +kernel

theorem rowEval13715 (x : Key → ℝ) : Integer.Sparse.eval row13715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13715, Integer.Sparse.eval_collectBalanced, rawRowCheck13715]

def rawRow13716 : Integer.Sparse Key := [(key2853, 6), (key2700, -2), (key2803, -2), (key2855, -2), (key2853, 6), (key2626, -2), (key2780, -2), (key2865, -2), (key2700, -2), (key2803, -2), (key2855, -2), (key2626, -2), (key2780, -2), (key2865, -2), (key2610, 2), (key2635, 2), (key2665, 2), (key2721, 2), (key2789, 2), (key2824, 2)]

theorem rawRowCheck13716 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form3 = rawRow13716 := by decide +kernel

def row13716 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

theorem rowCheck13716 : row13716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13716 := by decide +kernel

theorem rowEval13716 (x : Key → ℝ) : Integer.Sparse.eval row13716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13716, Integer.Sparse.eval_collectBalanced, rawRowCheck13716]

def rawRow13717 : Integer.Sparse Key := [(key2853, 6), (key2700, -2), (key2855, -2), (key2803, -2), (key2853, 6), (key2626, -2), (key2865, -2), (key2780, -2), (key2700, -2), (key2855, -2), (key2803, -2), (key2626, -2), (key2865, -2), (key2780, -2), (key2635, 2), (key2610, 2), (key2721, 2), (key2665, 2), (key2824, 2), (key2789, 2)]

theorem rawRowCheck13717 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form3 = rawRow13717 := by decide +kernel

def row13717 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

theorem rowCheck13717 : row13717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13717 := by decide +kernel

theorem rowEval13717 (x : Key → ℝ) : Integer.Sparse.eval row13717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13717, Integer.Sparse.eval_collectBalanced, rawRowCheck13717]

def rawRow13718 : Integer.Sparse Key := [(key2853, 6), (key2803, -2), (key2700, -2), (key2855, -2), (key2853, 6), (key2780, -2), (key2626, -2), (key2865, -2), (key2803, -2), (key2700, -2), (key2855, -2), (key2780, -2), (key2626, -2), (key2865, -2), (key2665, 2), (key2789, 2), (key2610, 2), (key2824, 2), (key2635, 2), (key2721, 2)]

theorem rawRowCheck13718 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form3 = rawRow13718 := by decide +kernel

def row13718 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

theorem rowCheck13718 : row13718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13718 := by decide +kernel

theorem rowEval13718 (x : Key → ℝ) : Integer.Sparse.eval row13718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13718, Integer.Sparse.eval_collectBalanced, rawRowCheck13718]

def rawRow13719 : Integer.Sparse Key := [(key2853, 6), (key2803, -2), (key2855, -2), (key2700, -2), (key2853, 6), (key2780, -2), (key2865, -2), (key2626, -2), (key2803, -2), (key2855, -2), (key2700, -2), (key2780, -2), (key2865, -2), (key2626, -2), (key2789, 2), (key2665, 2), (key2824, 2), (key2610, 2), (key2721, 2), (key2635, 2)]

theorem rawRowCheck13719 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form3 = rawRow13719 := by decide +kernel

def row13719 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

theorem rowCheck13719 : row13719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13719 := by decide +kernel

theorem rowEval13719 (x : Key → ℝ) : Integer.Sparse.eval row13719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13719, Integer.Sparse.eval_collectBalanced, rawRowCheck13719]

def rawRow13720 : Integer.Sparse Key := [(key2853, 6), (key2855, -2), (key2700, -2), (key2803, -2), (key2853, 6), (key2865, -2), (key2626, -2), (key2780, -2), (key2855, -2), (key2700, -2), (key2803, -2), (key2865, -2), (key2626, -2), (key2780, -2), (key2721, 2), (key2824, 2), (key2635, 2), (key2789, 2), (key2610, 2), (key2665, 2)]

theorem rawRowCheck13720 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form3 = rawRow13720 := by decide +kernel

def row13720 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

theorem rowCheck13720 : row13720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13720 := by decide +kernel

theorem rowEval13720 (x : Key → ℝ) : Integer.Sparse.eval row13720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13720, Integer.Sparse.eval_collectBalanced, rawRowCheck13720]

def rawRow13721 : Integer.Sparse Key := [(key2853, 6), (key2855, -2), (key2803, -2), (key2700, -2), (key2853, 6), (key2865, -2), (key2780, -2), (key2626, -2), (key2855, -2), (key2803, -2), (key2700, -2), (key2865, -2), (key2780, -2), (key2626, -2), (key2824, 2), (key2721, 2), (key2789, 2), (key2635, 2), (key2665, 2), (key2610, 2)]

theorem rawRowCheck13721 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form3 = rawRow13721 := by decide +kernel

def row13721 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

theorem rowCheck13721 : row13721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13721 := by decide +kernel

theorem rowEval13721 (x : Key → ℝ) : Integer.Sparse.eval row13721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13721, Integer.Sparse.eval_collectBalanced, rawRowCheck13721]

def rawRow13722 : Integer.Sparse Key := [(key2855, 6), (key2700, -2), (key2803, -2), (key2853, -2), (key2865, 6), (key2626, -2), (key2780, -2), (key2853, -2), (key2721, -2), (key2824, -2), (key2865, -2), (key2635, -2), (key2789, -2), (key2855, -2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck13722 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form3 = rawRow13722 := by decide +kernel

def row13722 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13722 : row13722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13722 := by decide +kernel

theorem rowEval13722 (x : Key → ℝ) : Integer.Sparse.eval row13722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13722, Integer.Sparse.eval_collectBalanced, rawRowCheck13722]

def rawRow13723 : Integer.Sparse Key := [(key2855, 6), (key2700, -2), (key2853, -2), (key2803, -2), (key2865, 6), (key2626, -2), (key2853, -2), (key2780, -2), (key2721, -2), (key2865, -2), (key2824, -2), (key2635, -2), (key2855, -2), (key2789, -2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck13723 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form3 = rawRow13723 := by decide +kernel

def row13723 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13723 : row13723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13723 := by decide +kernel

theorem rowEval13723 (x : Key → ℝ) : Integer.Sparse.eval row13723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13723, Integer.Sparse.eval_collectBalanced, rawRowCheck13723]

def rawRow13724 : Integer.Sparse Key := [(key2855, 6), (key2803, -2), (key2700, -2), (key2853, -2), (key2865, 6), (key2780, -2), (key2626, -2), (key2853, -2), (key2824, -2), (key2721, -2), (key2865, -2), (key2789, -2), (key2635, -2), (key2855, -2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck13724 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form3 = rawRow13724 := by decide +kernel

def row13724 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13724 : row13724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13724 := by decide +kernel

theorem rowEval13724 (x : Key → ℝ) : Integer.Sparse.eval row13724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13724, Integer.Sparse.eval_collectBalanced, rawRowCheck13724]

def rawRow13725 : Integer.Sparse Key := [(key2855, 6), (key2803, -2), (key2853, -2), (key2700, -2), (key2865, 6), (key2780, -2), (key2853, -2), (key2626, -2), (key2824, -2), (key2865, -2), (key2721, -2), (key2789, -2), (key2855, -2), (key2635, -2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck13725 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form3 = rawRow13725 := by decide +kernel

def row13725 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13725 : row13725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13725 := by decide +kernel

theorem rowEval13725 (x : Key → ℝ) : Integer.Sparse.eval row13725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13725, Integer.Sparse.eval_collectBalanced, rawRowCheck13725]

def rawRow13726 : Integer.Sparse Key := [(key2855, 6), (key2853, -2), (key2700, -2), (key2803, -2), (key2865, 6), (key2853, -2), (key2626, -2), (key2780, -2), (key2865, -2), (key2721, -2), (key2824, -2), (key2855, -2), (key2635, -2), (key2789, -2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

theorem rawRowCheck13726 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form3 = rawRow13726 := by decide +kernel

def row13726 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13726 : row13726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13726 := by decide +kernel

theorem rowEval13726 (x : Key → ℝ) : Integer.Sparse.eval row13726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13726, Integer.Sparse.eval_collectBalanced, rawRowCheck13726]

def rawRow13727 : Integer.Sparse Key := [(key2855, 6), (key2853, -2), (key2803, -2), (key2700, -2), (key2865, 6), (key2853, -2), (key2780, -2), (key2626, -2), (key2865, -2), (key2824, -2), (key2721, -2), (key2855, -2), (key2789, -2), (key2635, -2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

theorem rawRowCheck13727 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form3 = rawRow13727 := by decide +kernel

def row13727 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13727 : row13727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13727 := by decide +kernel

theorem rowEval13727 (x : Key → ℝ) : Integer.Sparse.eval row13727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13727, Integer.Sparse.eval_collectBalanced, rawRowCheck13727]

def rawRow13728 : Integer.Sparse Key := [(key2824, 6), (key2721, -2), (key2865, -2), (key2865, -2), (key2789, 6), (key2635, -2), (key2855, -2), (key2855, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck13728 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form3 = rawRow13728 := by decide +kernel

def row13728 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck13728 : row13728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13728 := by decide +kernel

theorem rowEval13728 (x : Key → ℝ) : Integer.Sparse.eval row13728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13728, Integer.Sparse.eval_collectBalanced, rawRowCheck13728]

def rawRow13729 : Integer.Sparse Key := [(key2824, 6), (key2865, -2), (key2721, -2), (key2865, -2), (key2789, 6), (key2855, -2), (key2635, -2), (key2855, -2), (key2780, -2), (key2665, -2), (key2780, -2), (key2803, -2), (key2610, -2), (key2803, -2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck13729 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form3 = rawRow13729 := by decide +kernel

def row13729 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck13729 : row13729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13729 := by decide +kernel

theorem rowEval13729 (x : Key → ℝ) : Integer.Sparse.eval row13729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13729, Integer.Sparse.eval_collectBalanced, rawRowCheck13729]

def rawRow13730 : Integer.Sparse Key := [(key2824, 6), (key2865, -2), (key2865, -2), (key2721, -2), (key2789, 6), (key2855, -2), (key2855, -2), (key2635, -2), (key2780, -2), (key2780, -2), (key2665, -2), (key2803, -2), (key2803, -2), (key2610, -2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck13730 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form3 = rawRow13730 := by decide +kernel

def row13730 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

theorem rowCheck13730 : row13730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13730 := by decide +kernel

theorem rowEval13730 (x : Key → ℝ) : Integer.Sparse.eval row13730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13730, Integer.Sparse.eval_collectBalanced, rawRowCheck13730]

def rawRow13731 : Integer.Sparse Key := [(key2865, 6), (key2721, -2), (key2824, -2), (key2865, -2), (key2855, 6), (key2635, -2), (key2789, -2), (key2855, -2), (key2700, -2), (key2803, -2), (key2853, -2), (key2626, -2), (key2780, -2), (key2853, -2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck13731 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form3 = rawRow13731 := by decide +kernel

def row13731 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13731 : row13731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13731 := by decide +kernel

theorem rowEval13731 (x : Key → ℝ) : Integer.Sparse.eval row13731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13731, Integer.Sparse.eval_collectBalanced, rawRowCheck13731]

def rawRow13732 : Integer.Sparse Key := [(key2865, 6), (key2721, -2), (key2865, -2), (key2824, -2), (key2855, 6), (key2635, -2), (key2855, -2), (key2789, -2), (key2700, -2), (key2853, -2), (key2803, -2), (key2626, -2), (key2853, -2), (key2780, -2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck13732 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form3 = rawRow13732 := by decide +kernel

def row13732 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13732 : row13732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13732 := by decide +kernel

theorem rowEval13732 (x : Key → ℝ) : Integer.Sparse.eval row13732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13732, Integer.Sparse.eval_collectBalanced, rawRowCheck13732]

def rawRow13733 : Integer.Sparse Key := [(key2865, 6), (key2824, -2), (key2721, -2), (key2865, -2), (key2855, 6), (key2789, -2), (key2635, -2), (key2855, -2), (key2803, -2), (key2700, -2), (key2853, -2), (key2780, -2), (key2626, -2), (key2853, -2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck13733 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form3 = rawRow13733 := by decide +kernel

def row13733 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13733 : row13733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13733 := by decide +kernel

theorem rowEval13733 (x : Key → ℝ) : Integer.Sparse.eval row13733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13733, Integer.Sparse.eval_collectBalanced, rawRowCheck13733]

def rawRow13734 : Integer.Sparse Key := [(key2865, 6), (key2824, -2), (key2865, -2), (key2721, -2), (key2855, 6), (key2789, -2), (key2855, -2), (key2635, -2), (key2803, -2), (key2853, -2), (key2700, -2), (key2780, -2), (key2853, -2), (key2626, -2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck13734 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form3 = rawRow13734 := by decide +kernel

def row13734 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13734 : row13734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13734 := by decide +kernel

theorem rowEval13734 (x : Key → ℝ) : Integer.Sparse.eval row13734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13734, Integer.Sparse.eval_collectBalanced, rawRowCheck13734]

def rawRow13735 : Integer.Sparse Key := [(key2865, 6), (key2865, -2), (key2721, -2), (key2824, -2), (key2855, 6), (key2855, -2), (key2635, -2), (key2789, -2), (key2853, -2), (key2700, -2), (key2803, -2), (key2853, -2), (key2626, -2), (key2780, -2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

theorem rawRowCheck13735 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form3 = rawRow13735 := by decide +kernel

def row13735 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13735 : row13735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13735 := by decide +kernel

theorem rowEval13735 (x : Key → ℝ) : Integer.Sparse.eval row13735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13735, Integer.Sparse.eval_collectBalanced, rawRowCheck13735]

def rawRow13736 : Integer.Sparse Key := [(key2865, 6), (key2865, -2), (key2824, -2), (key2721, -2), (key2855, 6), (key2855, -2), (key2789, -2), (key2635, -2), (key2853, -2), (key2803, -2), (key2700, -2), (key2853, -2), (key2780, -2), (key2626, -2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

theorem rawRowCheck13736 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form3 = rawRow13736 := by decide +kernel

def row13736 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, 2), (key2721, -2), (key2789, -2), (key2824, -2), (key2853, -4), (key2855, 4), (key2865, 4)]

theorem rowCheck13736 : row13736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13736 := by decide +kernel

theorem rowEval13736 (x : Key → ℝ) : Integer.Sparse.eval row13736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13736, Integer.Sparse.eval_collectBalanced, rawRowCheck13736]

def rawRow13737 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1070, -2), (key1035, 6), (key1107, -2), (key1113, -2), (key1149, -2), (key994, 2), (key1000, 2), (key1107, 2), (key1231, 2), (key1149, 2), (key1241, 2), (key1000, -2), (key1113, -2), (key1231, -2), (key1122, 6), (key1014, -2), (key1122, -2), (key1234, -2)]

theorem rawRowCheck13737 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form4 = rawRow13737 := by decide +kernel

def row13737 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13737 : row13737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13737 := by decide +kernel

theorem rowEval13737 (x : Key → ℝ) : Integer.Sparse.eval row13737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13737, Integer.Sparse.eval_collectBalanced, rawRowCheck13737]

def rawRow13738 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1070, -2), (key1035, 6), (key1113, -2), (key1107, -2), (key1149, -2), (key1000, 2), (key994, 2), (key1231, 2), (key1107, 2), (key1241, 2), (key1149, 2), (key1000, -2), (key1231, -2), (key1113, -2), (key1122, 6), (key1014, -2), (key1234, -2), (key1122, -2)]

theorem rawRowCheck13738 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form4 = rawRow13738 := by decide +kernel

def row13738 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13738 : row13738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13738 := by decide +kernel

theorem rowEval13738 (x : Key → ℝ) : Integer.Sparse.eval row13738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13738, Integer.Sparse.eval_collectBalanced, rawRowCheck13738]

def rawRow13739 : Integer.Sparse Key := [(key1029, -2), (key1070, -2), (key1035, -2), (key1035, 6), (key1107, -2), (key1149, -2), (key1113, -2), (key1107, 2), (key1149, 2), (key994, 2), (key1241, 2), (key1000, 2), (key1231, 2), (key1113, -2), (key1000, -2), (key1231, -2), (key1122, 6), (key1122, -2), (key1014, -2), (key1234, -2)]

theorem rawRowCheck13739 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form4 = rawRow13739 := by decide +kernel

def row13739 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13739 : row13739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13739 := by decide +kernel

theorem rowEval13739 (x : Key → ℝ) : Integer.Sparse.eval row13739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13739, Integer.Sparse.eval_collectBalanced, rawRowCheck13739]

def rawRow13740 : Integer.Sparse Key := [(key1070, -2), (key1029, -2), (key1035, -2), (key1035, 6), (key1149, -2), (key1107, -2), (key1113, -2), (key1149, 2), (key1107, 2), (key1241, 2), (key994, 2), (key1231, 2), (key1000, 2), (key1113, -2), (key1231, -2), (key1000, -2), (key1122, 6), (key1122, -2), (key1234, -2), (key1014, -2)]

theorem rawRowCheck13740 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form4 = rawRow13740 := by decide +kernel

def row13740 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13740 : row13740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13740 := by decide +kernel

theorem rowEval13740 (x : Key → ℝ) : Integer.Sparse.eval row13740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13740, Integer.Sparse.eval_collectBalanced, rawRowCheck13740]

def rawRow13741 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1029, -2), (key1035, 6), (key1113, -2), (key1149, -2), (key1107, -2), (key1231, 2), (key1241, 2), (key1000, 2), (key1149, 2), (key994, 2), (key1107, 2), (key1231, -2), (key1000, -2), (key1113, -2), (key1122, 6), (key1234, -2), (key1014, -2), (key1122, -2)]

theorem rawRowCheck13741 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form4 = rawRow13741 := by decide +kernel

def row13741 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13741 : row13741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13741 := by decide +kernel

theorem rowEval13741 (x : Key → ℝ) : Integer.Sparse.eval row13741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13741, Integer.Sparse.eval_collectBalanced, rawRowCheck13741]

def rawRow13742 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1029, -2), (key1035, 6), (key1149, -2), (key1113, -2), (key1107, -2), (key1241, 2), (key1231, 2), (key1149, 2), (key1000, 2), (key1107, 2), (key994, 2), (key1231, -2), (key1113, -2), (key1000, -2), (key1122, 6), (key1234, -2), (key1122, -2), (key1014, -2)]

theorem rawRowCheck13742 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form4 = rawRow13742 := by decide +kernel

def row13742 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13742 : row13742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13742 := by decide +kernel

theorem rowEval13742 (x : Key → ℝ) : Integer.Sparse.eval row13742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13742, Integer.Sparse.eval_collectBalanced, rawRowCheck13742]

def rawRow13743 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1070, -2), (key1029, 6), (key1231, -2), (key1231, -2), (key1241, -2), (key1000, 2), (key1000, 2), (key1113, 2), (key1113, 2), (key1149, 2), (key1149, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1234, 6), (key1014, -2), (key1122, -2), (key1122, -2)]

theorem rawRowCheck13743 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form4 = rawRow13743 := by decide +kernel

def row13743 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

theorem rowCheck13743 : row13743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13743 := by decide +kernel

theorem rowEval13743 (x : Key → ℝ) : Integer.Sparse.eval row13743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13743, Integer.Sparse.eval_collectBalanced, rawRowCheck13743]

def rawRow13744 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1035, -2), (key1029, 6), (key1231, -2), (key1241, -2), (key1231, -2), (key1113, 2), (key1149, 2), (key1000, 2), (key1149, 2), (key1000, 2), (key1113, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1234, 6), (key1122, -2), (key1014, -2), (key1122, -2)]

theorem rawRowCheck13744 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form4 = rawRow13744 := by decide +kernel

def row13744 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

theorem rowCheck13744 : row13744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13744 := by decide +kernel

theorem rowEval13744 (x : Key → ℝ) : Integer.Sparse.eval row13744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13744, Integer.Sparse.eval_collectBalanced, rawRowCheck13744]

def rawRow13745 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1035, -2), (key1029, 6), (key1241, -2), (key1231, -2), (key1231, -2), (key1149, 2), (key1113, 2), (key1149, 2), (key1000, 2), (key1113, 2), (key1000, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1234, 6), (key1122, -2), (key1122, -2), (key1014, -2)]

theorem rawRowCheck13745 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form4 = rawRow13745 := by decide +kernel

def row13745 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

theorem rowCheck13745 : row13745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13745 := by decide +kernel

theorem rowEval13745 (x : Key → ℝ) : Integer.Sparse.eval row13745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13745, Integer.Sparse.eval_collectBalanced, rawRowCheck13745]

def rawRow13746 : Integer.Sparse Key := [(key1107, -2), (key1113, -2), (key1149, -2), (key1122, 6), (key1029, -2), (key1035, -2), (key1070, -2), (key994, 2), (key1000, 2), (key1107, 2), (key1231, 2), (key1149, 2), (key1241, 2), (key1014, -2), (key1122, -2), (key1234, -2), (key1035, 6), (key1000, -2), (key1113, -2), (key1231, -2)]

theorem rawRowCheck13746 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form4 = rawRow13746 := by decide +kernel

def row13746 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13746 : row13746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13746 := by decide +kernel

theorem rowEval13746 (x : Key → ℝ) : Integer.Sparse.eval row13746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13746, Integer.Sparse.eval_collectBalanced, rawRowCheck13746]

def rawRow13747 : Integer.Sparse Key := [(key1113, -2), (key1107, -2), (key1149, -2), (key1122, 6), (key1035, -2), (key1029, -2), (key1070, -2), (key1000, 2), (key994, 2), (key1231, 2), (key1107, 2), (key1241, 2), (key1149, 2), (key1014, -2), (key1234, -2), (key1122, -2), (key1035, 6), (key1000, -2), (key1231, -2), (key1113, -2)]

theorem rawRowCheck13747 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form4 = rawRow13747 := by decide +kernel

def row13747 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13747 : row13747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13747 := by decide +kernel

theorem rowEval13747 (x : Key → ℝ) : Integer.Sparse.eval row13747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13747, Integer.Sparse.eval_collectBalanced, rawRowCheck13747]

def rawRow13748 : Integer.Sparse Key := [(key1107, -2), (key1149, -2), (key1113, -2), (key1122, 6), (key1029, -2), (key1070, -2), (key1035, -2), (key1107, 2), (key1149, 2), (key994, 2), (key1241, 2), (key1000, 2), (key1231, 2), (key1122, -2), (key1014, -2), (key1234, -2), (key1035, 6), (key1113, -2), (key1000, -2), (key1231, -2)]

theorem rawRowCheck13748 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form4 = rawRow13748 := by decide +kernel

def row13748 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13748 : row13748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13748 := by decide +kernel

theorem rowEval13748 (x : Key → ℝ) : Integer.Sparse.eval row13748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13748, Integer.Sparse.eval_collectBalanced, rawRowCheck13748]

def rawRow13749 : Integer.Sparse Key := [(key1149, -2), (key1107, -2), (key1113, -2), (key1122, 6), (key1070, -2), (key1029, -2), (key1035, -2), (key1149, 2), (key1107, 2), (key1241, 2), (key994, 2), (key1231, 2), (key1000, 2), (key1122, -2), (key1234, -2), (key1014, -2), (key1035, 6), (key1113, -2), (key1231, -2), (key1000, -2)]

theorem rawRowCheck13749 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form4 = rawRow13749 := by decide +kernel

def row13749 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13749 : row13749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13749 := by decide +kernel

theorem rowEval13749 (x : Key → ℝ) : Integer.Sparse.eval row13749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13749, Integer.Sparse.eval_collectBalanced, rawRowCheck13749]

def rawRow13750 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1107, -2), (key1122, 6), (key1035, -2), (key1070, -2), (key1029, -2), (key1231, 2), (key1241, 2), (key1000, 2), (key1149, 2), (key994, 2), (key1107, 2), (key1234, -2), (key1014, -2), (key1122, -2), (key1035, 6), (key1231, -2), (key1000, -2), (key1113, -2)]

theorem rawRowCheck13750 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form4 = rawRow13750 := by decide +kernel

def row13750 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13750 : row13750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13750 := by decide +kernel

theorem rowEval13750 (x : Key → ℝ) : Integer.Sparse.eval row13750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13750, Integer.Sparse.eval_collectBalanced, rawRowCheck13750]

def rawRow13751 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1107, -2), (key1122, 6), (key1070, -2), (key1035, -2), (key1029, -2), (key1241, 2), (key1231, 2), (key1149, 2), (key1000, 2), (key1107, 2), (key994, 2), (key1234, -2), (key1122, -2), (key1014, -2), (key1035, 6), (key1231, -2), (key1113, -2), (key1000, -2)]

theorem rawRowCheck13751 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form4 = rawRow13751 := by decide +kernel

def row13751 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

theorem rowCheck13751 : row13751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13751 := by decide +kernel

theorem rowEval13751 (x : Key → ℝ) : Integer.Sparse.eval row13751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13751, Integer.Sparse.eval_collectBalanced, rawRowCheck13751]

def rawRow13752 : Integer.Sparse Key := [(key1107, -2), (key1122, -2), (key1149, -2), (key1113, 6), (key1107, -2), (key1122, -2), (key1149, -2), (key994, 2), (key1014, 2), (key1029, 2), (key1234, 2), (key1070, 2), (key1241, 2), (key1000, -2), (key1035, -2), (key1231, -2), (key1113, 6), (key1000, -2), (key1035, -2), (key1231, -2)]

theorem rawRowCheck13752 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form4 = rawRow13752 := by decide +kernel

def row13752 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck13752 : row13752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13752 := by decide +kernel

theorem rowEval13752 (x : Key → ℝ) : Integer.Sparse.eval row13752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13752, Integer.Sparse.eval_collectBalanced, rawRowCheck13752]

def rawRow13753 : Integer.Sparse Key := [(key1122, -2), (key1107, -2), (key1149, -2), (key1113, 6), (key1122, -2), (key1107, -2), (key1149, -2), (key1014, 2), (key994, 2), (key1234, 2), (key1029, 2), (key1241, 2), (key1070, 2), (key1000, -2), (key1231, -2), (key1035, -2), (key1113, 6), (key1000, -2), (key1231, -2), (key1035, -2)]

theorem rawRowCheck13753 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form4 = rawRow13753 := by decide +kernel

def row13753 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck13753 : row13753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13753 := by decide +kernel

theorem rowEval13753 (x : Key → ℝ) : Integer.Sparse.eval row13753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13753, Integer.Sparse.eval_collectBalanced, rawRowCheck13753]

def rawRow13754 : Integer.Sparse Key := [(key1107, -2), (key1149, -2), (key1122, -2), (key1113, 6), (key1107, -2), (key1149, -2), (key1122, -2), (key1029, 2), (key1070, 2), (key994, 2), (key1241, 2), (key1014, 2), (key1234, 2), (key1035, -2), (key1000, -2), (key1231, -2), (key1113, 6), (key1035, -2), (key1000, -2), (key1231, -2)]

theorem rawRowCheck13754 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form4 = rawRow13754 := by decide +kernel

def row13754 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck13754 : row13754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13754 := by decide +kernel

theorem rowEval13754 (x : Key → ℝ) : Integer.Sparse.eval row13754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13754, Integer.Sparse.eval_collectBalanced, rawRowCheck13754]

def rawRow13755 : Integer.Sparse Key := [(key1149, -2), (key1107, -2), (key1122, -2), (key1113, 6), (key1149, -2), (key1107, -2), (key1122, -2), (key1070, 2), (key1029, 2), (key1241, 2), (key994, 2), (key1234, 2), (key1014, 2), (key1035, -2), (key1231, -2), (key1000, -2), (key1113, 6), (key1035, -2), (key1231, -2), (key1000, -2)]

theorem rawRowCheck13755 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form4 = rawRow13755 := by decide +kernel

def row13755 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck13755 : row13755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13755 := by decide +kernel

theorem rowEval13755 (x : Key → ℝ) : Integer.Sparse.eval row13755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13755, Integer.Sparse.eval_collectBalanced, rawRowCheck13755]

def rawRow13756 : Integer.Sparse Key := [(key1122, -2), (key1149, -2), (key1107, -2), (key1113, 6), (key1122, -2), (key1149, -2), (key1107, -2), (key1234, 2), (key1241, 2), (key1014, 2), (key1070, 2), (key994, 2), (key1029, 2), (key1231, -2), (key1000, -2), (key1035, -2), (key1113, 6), (key1231, -2), (key1000, -2), (key1035, -2)]

theorem rawRowCheck13756 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form4 = rawRow13756 := by decide +kernel

def row13756 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck13756 : row13756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13756 := by decide +kernel

theorem rowEval13756 (x : Key → ℝ) : Integer.Sparse.eval row13756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13756, Integer.Sparse.eval_collectBalanced, rawRowCheck13756]

def rawRow13757 : Integer.Sparse Key := [(key1149, -2), (key1122, -2), (key1107, -2), (key1113, 6), (key1149, -2), (key1122, -2), (key1107, -2), (key1241, 2), (key1234, 2), (key1070, 2), (key1014, 2), (key1029, 2), (key994, 2), (key1231, -2), (key1035, -2), (key1000, -2), (key1113, 6), (key1231, -2), (key1035, -2), (key1000, -2)]

theorem rawRowCheck13757 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form4 = rawRow13757 := by decide +kernel

def row13757 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck13757 : row13757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13757 := by decide +kernel

theorem rowEval13757 (x : Key → ℝ) : Integer.Sparse.eval row13757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13757, Integer.Sparse.eval_collectBalanced, rawRowCheck13757]

def rawRow13758 : Integer.Sparse Key := [(key1113, -2), (key1122, -2), (key1149, -2), (key1107, 6), (key1231, -2), (key1234, -2), (key1241, -2), (key1000, 2), (key1014, 2), (key1035, 2), (key1122, 2), (key1070, 2), (key1149, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1231, 6), (key1000, -2), (key1035, -2), (key1113, -2)]

theorem rawRowCheck13758 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form4 = rawRow13758 := by decide +kernel

def row13758 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13758 : row13758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13758 := by decide +kernel

theorem rowEval13758 (x : Key → ℝ) : Integer.Sparse.eval row13758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13758, Integer.Sparse.eval_collectBalanced, rawRowCheck13758]

def rawRow13759 : Integer.Sparse Key := [(key1122, -2), (key1113, -2), (key1149, -2), (key1107, 6), (key1234, -2), (key1231, -2), (key1241, -2), (key1014, 2), (key1000, 2), (key1122, 2), (key1035, 2), (key1149, 2), (key1070, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1231, 6), (key1000, -2), (key1113, -2), (key1035, -2)]

theorem rawRowCheck13759 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form4 = rawRow13759 := by decide +kernel

def row13759 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13759 : row13759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13759 := by decide +kernel

theorem rowEval13759 (x : Key → ℝ) : Integer.Sparse.eval row13759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13759, Integer.Sparse.eval_collectBalanced, rawRowCheck13759]

def rawRow13760 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1122, -2), (key1107, 6), (key1231, -2), (key1241, -2), (key1234, -2), (key1035, 2), (key1070, 2), (key1000, 2), (key1149, 2), (key1014, 2), (key1122, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1231, 6), (key1035, -2), (key1000, -2), (key1113, -2)]

theorem rawRowCheck13760 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form4 = rawRow13760 := by decide +kernel

def row13760 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13760 : row13760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13760 := by decide +kernel

theorem rowEval13760 (x : Key → ℝ) : Integer.Sparse.eval row13760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13760, Integer.Sparse.eval_collectBalanced, rawRowCheck13760]

def rawRow13761 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1122, -2), (key1107, 6), (key1241, -2), (key1231, -2), (key1234, -2), (key1070, 2), (key1035, 2), (key1149, 2), (key1000, 2), (key1122, 2), (key1014, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1231, 6), (key1035, -2), (key1113, -2), (key1000, -2)]

theorem rawRowCheck13761 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form4 = rawRow13761 := by decide +kernel

def row13761 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13761 : row13761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13761 := by decide +kernel

theorem rowEval13761 (x : Key → ℝ) : Integer.Sparse.eval row13761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13761, Integer.Sparse.eval_collectBalanced, rawRowCheck13761]

def rawRow13762 : Integer.Sparse Key := [(key1122, -2), (key1149, -2), (key1113, -2), (key1107, 6), (key1234, -2), (key1241, -2), (key1231, -2), (key1122, 2), (key1149, 2), (key1014, 2), (key1070, 2), (key1000, 2), (key1035, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1231, 6), (key1113, -2), (key1000, -2), (key1035, -2)]

theorem rawRowCheck13762 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form4 = rawRow13762 := by decide +kernel

def row13762 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13762 : row13762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13762 := by decide +kernel

theorem rowEval13762 (x : Key → ℝ) : Integer.Sparse.eval row13762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13762, Integer.Sparse.eval_collectBalanced, rawRowCheck13762]

def rawRow13763 : Integer.Sparse Key := [(key1149, -2), (key1122, -2), (key1113, -2), (key1107, 6), (key1241, -2), (key1234, -2), (key1231, -2), (key1149, 2), (key1122, 2), (key1070, 2), (key1014, 2), (key1035, 2), (key1000, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1231, 6), (key1113, -2), (key1035, -2), (key1000, -2)]

theorem rawRowCheck13763 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form4 = rawRow13763 := by decide +kernel

def row13763 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13763 : row13763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13763 := by decide +kernel

theorem rowEval13763 (x : Key → ℝ) : Integer.Sparse.eval row13763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13763, Integer.Sparse.eval_collectBalanced, rawRowCheck13763]

def rawRow13764 : Integer.Sparse Key := [(key1231, -2), (key1231, -2), (key1241, -2), (key1234, 6), (key1035, -2), (key1035, -2), (key1070, -2), (key1000, 2), (key1000, 2), (key1113, 2), (key1113, 2), (key1149, 2), (key1149, 2), (key1014, -2), (key1122, -2), (key1122, -2), (key1029, 6), (key994, -2), (key1107, -2), (key1107, -2)]

theorem rawRowCheck13764 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form4 = rawRow13764 := by decide +kernel

def row13764 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

theorem rowCheck13764 : row13764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13764 := by decide +kernel

theorem rowEval13764 (x : Key → ℝ) : Integer.Sparse.eval row13764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13764, Integer.Sparse.eval_collectBalanced, rawRowCheck13764]

def rawRow13765 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1231, -2), (key1234, 6), (key1035, -2), (key1070, -2), (key1035, -2), (key1113, 2), (key1149, 2), (key1000, 2), (key1149, 2), (key1000, 2), (key1113, 2), (key1122, -2), (key1014, -2), (key1122, -2), (key1029, 6), (key1107, -2), (key994, -2), (key1107, -2)]

theorem rawRowCheck13765 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form4 = rawRow13765 := by decide +kernel

def row13765 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

theorem rowCheck13765 : row13765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13765 := by decide +kernel

theorem rowEval13765 (x : Key → ℝ) : Integer.Sparse.eval row13765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13765, Integer.Sparse.eval_collectBalanced, rawRowCheck13765]

def rawRow13766 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1231, -2), (key1234, 6), (key1070, -2), (key1035, -2), (key1035, -2), (key1149, 2), (key1113, 2), (key1149, 2), (key1000, 2), (key1113, 2), (key1000, 2), (key1122, -2), (key1122, -2), (key1014, -2), (key1029, 6), (key1107, -2), (key1107, -2), (key994, -2)]

theorem rawRowCheck13766 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form4 = rawRow13766 := by decide +kernel

def row13766 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

theorem rowCheck13766 : row13766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13766 := by decide +kernel

theorem rowEval13766 (x : Key → ℝ) : Integer.Sparse.eval row13766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13766, Integer.Sparse.eval_collectBalanced, rawRowCheck13766]

def rawRow13767 : Integer.Sparse Key := [(key1231, -2), (key1234, -2), (key1241, -2), (key1231, 6), (key1113, -2), (key1122, -2), (key1149, -2), (key1000, 2), (key1014, 2), (key1035, 2), (key1122, 2), (key1070, 2), (key1149, 2), (key1000, -2), (key1035, -2), (key1113, -2), (key1107, 6), (key994, -2), (key1029, -2), (key1107, -2)]

theorem rawRowCheck13767 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form4 = rawRow13767 := by decide +kernel

def row13767 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13767 : row13767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13767 := by decide +kernel

theorem rowEval13767 (x : Key → ℝ) : Integer.Sparse.eval row13767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13767, Integer.Sparse.eval_collectBalanced, rawRowCheck13767]

def rawRow13768 : Integer.Sparse Key := [(key1234, -2), (key1231, -2), (key1241, -2), (key1231, 6), (key1122, -2), (key1113, -2), (key1149, -2), (key1014, 2), (key1000, 2), (key1122, 2), (key1035, 2), (key1149, 2), (key1070, 2), (key1000, -2), (key1113, -2), (key1035, -2), (key1107, 6), (key994, -2), (key1107, -2), (key1029, -2)]

theorem rawRowCheck13768 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form4 = rawRow13768 := by decide +kernel

def row13768 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13768 : row13768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13768 := by decide +kernel

theorem rowEval13768 (x : Key → ℝ) : Integer.Sparse.eval row13768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13768, Integer.Sparse.eval_collectBalanced, rawRowCheck13768]

def rawRow13769 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1234, -2), (key1231, 6), (key1113, -2), (key1149, -2), (key1122, -2), (key1035, 2), (key1070, 2), (key1000, 2), (key1149, 2), (key1014, 2), (key1122, 2), (key1035, -2), (key1000, -2), (key1113, -2), (key1107, 6), (key1029, -2), (key994, -2), (key1107, -2)]

theorem rawRowCheck13769 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form4 = rawRow13769 := by decide +kernel

def row13769 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13769 : row13769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13769 := by decide +kernel

theorem rowEval13769 (x : Key → ℝ) : Integer.Sparse.eval row13769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13769, Integer.Sparse.eval_collectBalanced, rawRowCheck13769]

def rawRow13770 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1234, -2), (key1231, 6), (key1149, -2), (key1113, -2), (key1122, -2), (key1070, 2), (key1035, 2), (key1149, 2), (key1000, 2), (key1122, 2), (key1014, 2), (key1035, -2), (key1113, -2), (key1000, -2), (key1107, 6), (key1029, -2), (key1107, -2), (key994, -2)]

theorem rawRowCheck13770 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form4 = rawRow13770 := by decide +kernel

def row13770 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13770 : row13770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13770 := by decide +kernel

theorem rowEval13770 (x : Key → ℝ) : Integer.Sparse.eval row13770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13770, Integer.Sparse.eval_collectBalanced, rawRowCheck13770]

def rawRow13771 : Integer.Sparse Key := [(key1234, -2), (key1241, -2), (key1231, -2), (key1231, 6), (key1122, -2), (key1149, -2), (key1113, -2), (key1122, 2), (key1149, 2), (key1014, 2), (key1070, 2), (key1000, 2), (key1035, 2), (key1113, -2), (key1000, -2), (key1035, -2), (key1107, 6), (key1107, -2), (key994, -2), (key1029, -2)]

theorem rawRowCheck13771 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form4 = rawRow13771 := by decide +kernel

def row13771 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13771 : row13771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13771 := by decide +kernel

theorem rowEval13771 (x : Key → ℝ) : Integer.Sparse.eval row13771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13771, Integer.Sparse.eval_collectBalanced, rawRowCheck13771]

def rawRow13772 : Integer.Sparse Key := [(key1241, -2), (key1234, -2), (key1231, -2), (key1231, 6), (key1149, -2), (key1122, -2), (key1113, -2), (key1149, 2), (key1122, 2), (key1070, 2), (key1014, 2), (key1035, 2), (key1000, 2), (key1113, -2), (key1035, -2), (key1000, -2), (key1107, 6), (key1107, -2), (key1029, -2), (key994, -2)]

theorem rawRowCheck13772 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form4 = rawRow13772 := by decide +kernel

def row13772 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, -2), (key1070, 2), (key1107, 4), (key1113, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck13772 : row13772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13772 := by decide +kernel

theorem rowEval13772 (x : Key → ℝ) : Integer.Sparse.eval row13772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck13772, Integer.Sparse.eval_collectBalanced, rawRowCheck13772]

def rawRow13773 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1243, 4), (key1003, -2), (key1009, -2), (key1116, -2), (key1233, -2), (key1159, -2), (key1243, -2), (key1017, -2), (key1022, -2), (key1125, -2), (key1236, -2), (key1174, -2), (key1247, -2), (key1022, 4), (key1130, 4), (key1236, 4)]

theorem rawRowCheck13773 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form5 = rawRow13773 := by decide +kernel

def row13773 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13773 : row13773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13773 := by decide +kernel

theorem rowEval13773 (x : Key → ℝ) : Integer.Sparse.eval row13773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13773, Integer.Sparse.eval_collectBalanced, rawRowCheck13773]

def rawRow13774 : Integer.Sparse Key := [(key1003, 4), (key1243, 4), (key1152, 4), (key1009, -2), (key1003, -2), (key1233, -2), (key1116, -2), (key1243, -2), (key1159, -2), (key1022, -2), (key1017, -2), (key1236, -2), (key1125, -2), (key1247, -2), (key1174, -2), (key1022, 4), (key1236, 4), (key1130, 4)]

theorem rawRowCheck13774 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form5 = rawRow13774 := by decide +kernel

def row13774 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13774 : row13774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13774 := by decide +kernel

theorem rowEval13774 (x : Key → ℝ) : Integer.Sparse.eval row13774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13774, Integer.Sparse.eval_collectBalanced, rawRowCheck13774]

def rawRow13775 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1243, 4), (key1116, -2), (key1159, -2), (key1003, -2), (key1243, -2), (key1009, -2), (key1233, -2), (key1125, -2), (key1174, -2), (key1017, -2), (key1247, -2), (key1022, -2), (key1236, -2), (key1130, 4), (key1022, 4), (key1236, 4)]

theorem rawRowCheck13775 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form5 = rawRow13775 := by decide +kernel

def row13775 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13775 : row13775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13775 := by decide +kernel

theorem rowEval13775 (x : Key → ℝ) : Integer.Sparse.eval row13775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13775, Integer.Sparse.eval_collectBalanced, rawRowCheck13775]

def rawRow13776 : Integer.Sparse Key := [(key1152, 4), (key1243, 4), (key1003, 4), (key1159, -2), (key1116, -2), (key1243, -2), (key1003, -2), (key1233, -2), (key1009, -2), (key1174, -2), (key1125, -2), (key1247, -2), (key1017, -2), (key1236, -2), (key1022, -2), (key1130, 4), (key1236, 4), (key1022, 4)]

theorem rawRowCheck13776 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form5 = rawRow13776 := by decide +kernel

def row13776 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13776 : row13776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13776 := by decide +kernel

theorem rowEval13776 (x : Key → ℝ) : Integer.Sparse.eval row13776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13776, Integer.Sparse.eval_collectBalanced, rawRowCheck13776]

def rawRow13777 : Integer.Sparse Key := [(key1243, 4), (key1003, 4), (key1152, 4), (key1233, -2), (key1243, -2), (key1009, -2), (key1159, -2), (key1003, -2), (key1116, -2), (key1236, -2), (key1247, -2), (key1022, -2), (key1174, -2), (key1017, -2), (key1125, -2), (key1236, 4), (key1022, 4), (key1130, 4)]

theorem rawRowCheck13777 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form5 = rawRow13777 := by decide +kernel

def row13777 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13777 : row13777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13777 := by decide +kernel

theorem rowEval13777 (x : Key → ℝ) : Integer.Sparse.eval row13777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13777, Integer.Sparse.eval_collectBalanced, rawRowCheck13777]

def rawRow13778 : Integer.Sparse Key := [(key1243, 4), (key1152, 4), (key1003, 4), (key1243, -2), (key1233, -2), (key1159, -2), (key1009, -2), (key1116, -2), (key1003, -2), (key1247, -2), (key1236, -2), (key1174, -2), (key1022, -2), (key1125, -2), (key1017, -2), (key1236, 4), (key1130, 4), (key1022, 4)]

theorem rawRowCheck13778 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form5 = rawRow13778 := by decide +kernel

def row13778 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13778 : row13778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13778 := by decide +kernel

theorem rowEval13778 (x : Key → ℝ) : Integer.Sparse.eval row13778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13778, Integer.Sparse.eval_collectBalanced, rawRowCheck13778]

def rawRow13779 : Integer.Sparse Key := [(key1009, 4), (key1159, 4), (key1159, 4), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1022, -2), (key1022, -2), (key1130, -2), (key1130, -2), (key1174, -2), (key1174, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

theorem rawRowCheck13779 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form5 = rawRow13779 := by decide +kernel

def row13779 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

theorem rowCheck13779 : row13779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13779 := by decide +kernel

theorem rowEval13779 (x : Key → ℝ) : Integer.Sparse.eval row13779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13779, Integer.Sparse.eval_collectBalanced, rawRowCheck13779]

def rawRow13780 : Integer.Sparse Key := [(key1159, 4), (key1009, 4), (key1159, 4), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

theorem rawRowCheck13780 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form5 = rawRow13780 := by decide +kernel

def row13780 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

theorem rowCheck13780 : row13780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13780 := by decide +kernel

theorem rowEval13780 (x : Key → ℝ) : Integer.Sparse.eval row13780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13780, Integer.Sparse.eval_collectBalanced, rawRowCheck13780]

def rawRow13781 : Integer.Sparse Key := [(key1159, 4), (key1159, 4), (key1009, 4), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1174, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1022, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

theorem rawRowCheck13781 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form5 = rawRow13781 := by decide +kernel

def row13781 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

theorem rowCheck13781 : row13781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13781 := by decide +kernel

theorem rowEval13781 (x : Key → ℝ) : Integer.Sparse.eval row13781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13781, Integer.Sparse.eval_collectBalanced, rawRowCheck13781]

def rawRow13782 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1243, 4), (key1017, -2), (key1022, -2), (key1125, -2), (key1236, -2), (key1174, -2), (key1247, -2), (key1003, -2), (key1009, -2), (key1116, -2), (key1233, -2), (key1159, -2), (key1243, -2), (key1022, 4), (key1130, 4), (key1236, 4)]

theorem rawRowCheck13782 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form5 = rawRow13782 := by decide +kernel

def row13782 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13782 : row13782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13782 := by decide +kernel

theorem rowEval13782 (x : Key → ℝ) : Integer.Sparse.eval row13782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13782, Integer.Sparse.eval_collectBalanced, rawRowCheck13782]

def rawRow13783 : Integer.Sparse Key := [(key1003, 4), (key1243, 4), (key1152, 4), (key1022, -2), (key1017, -2), (key1236, -2), (key1125, -2), (key1247, -2), (key1174, -2), (key1009, -2), (key1003, -2), (key1233, -2), (key1116, -2), (key1243, -2), (key1159, -2), (key1022, 4), (key1236, 4), (key1130, 4)]

theorem rawRowCheck13783 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form5 = rawRow13783 := by decide +kernel

def row13783 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13783 : row13783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13783 := by decide +kernel

theorem rowEval13783 (x : Key → ℝ) : Integer.Sparse.eval row13783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13783, Integer.Sparse.eval_collectBalanced, rawRowCheck13783]

def rawRow13784 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1243, 4), (key1125, -2), (key1174, -2), (key1017, -2), (key1247, -2), (key1022, -2), (key1236, -2), (key1116, -2), (key1159, -2), (key1003, -2), (key1243, -2), (key1009, -2), (key1233, -2), (key1130, 4), (key1022, 4), (key1236, 4)]

theorem rawRowCheck13784 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form5 = rawRow13784 := by decide +kernel

def row13784 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13784 : row13784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13784 := by decide +kernel

theorem rowEval13784 (x : Key → ℝ) : Integer.Sparse.eval row13784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13784, Integer.Sparse.eval_collectBalanced, rawRowCheck13784]

def rawRow13785 : Integer.Sparse Key := [(key1152, 4), (key1243, 4), (key1003, 4), (key1174, -2), (key1125, -2), (key1247, -2), (key1017, -2), (key1236, -2), (key1022, -2), (key1159, -2), (key1116, -2), (key1243, -2), (key1003, -2), (key1233, -2), (key1009, -2), (key1130, 4), (key1236, 4), (key1022, 4)]

theorem rawRowCheck13785 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form5 = rawRow13785 := by decide +kernel

def row13785 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13785 : row13785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13785 := by decide +kernel

theorem rowEval13785 (x : Key → ℝ) : Integer.Sparse.eval row13785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13785, Integer.Sparse.eval_collectBalanced, rawRowCheck13785]

def rawRow13786 : Integer.Sparse Key := [(key1243, 4), (key1003, 4), (key1152, 4), (key1236, -2), (key1247, -2), (key1022, -2), (key1174, -2), (key1017, -2), (key1125, -2), (key1233, -2), (key1243, -2), (key1009, -2), (key1159, -2), (key1003, -2), (key1116, -2), (key1236, 4), (key1022, 4), (key1130, 4)]

theorem rawRowCheck13786 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form5 = rawRow13786 := by decide +kernel

def row13786 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13786 : row13786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13786 := by decide +kernel

theorem rowEval13786 (x : Key → ℝ) : Integer.Sparse.eval row13786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13786, Integer.Sparse.eval_collectBalanced, rawRowCheck13786]

def rawRow13787 : Integer.Sparse Key := [(key1243, 4), (key1152, 4), (key1003, 4), (key1247, -2), (key1236, -2), (key1174, -2), (key1022, -2), (key1125, -2), (key1017, -2), (key1243, -2), (key1233, -2), (key1159, -2), (key1009, -2), (key1116, -2), (key1003, -2), (key1236, 4), (key1130, 4), (key1022, 4)]

theorem rawRowCheck13787 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form5 = rawRow13787 := by decide +kernel

def row13787 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck13787 : row13787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13787 := by decide +kernel

theorem rowEval13787 (x : Key → ℝ) : Integer.Sparse.eval row13787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13787, Integer.Sparse.eval_collectBalanced, rawRowCheck13787]

def rawRow13788 : Integer.Sparse Key := [(key1017, 4), (key1073, 4), (key1247, 4), (key1003, -2), (key1022, -2), (key1038, -2), (key1236, -2), (key1080, -2), (key1243, -2), (key1003, -2), (key1022, -2), (key1038, -2), (key1236, -2), (key1080, -2), (key1243, -2), (key1009, 4), (key1044, 4), (key1233, 4)]

theorem rawRowCheck13788 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form5 = rawRow13788 := by decide +kernel

def row13788 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck13788 : row13788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13788 := by decide +kernel

theorem rowEval13788 (x : Key → ℝ) : Integer.Sparse.eval row13788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13788, Integer.Sparse.eval_collectBalanced, rawRowCheck13788]

def rawRow13789 : Integer.Sparse Key := [(key1017, 4), (key1247, 4), (key1073, 4), (key1022, -2), (key1003, -2), (key1236, -2), (key1038, -2), (key1243, -2), (key1080, -2), (key1022, -2), (key1003, -2), (key1236, -2), (key1038, -2), (key1243, -2), (key1080, -2), (key1009, 4), (key1233, 4), (key1044, 4)]

theorem rawRowCheck13789 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form5 = rawRow13789 := by decide +kernel

def row13789 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck13789 : row13789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13789 := by decide +kernel

theorem rowEval13789 (x : Key → ℝ) : Integer.Sparse.eval row13789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13789, Integer.Sparse.eval_collectBalanced, rawRowCheck13789]

def rawRow13790 : Integer.Sparse Key := [(key1073, 4), (key1017, 4), (key1247, 4), (key1038, -2), (key1080, -2), (key1003, -2), (key1243, -2), (key1022, -2), (key1236, -2), (key1038, -2), (key1080, -2), (key1003, -2), (key1243, -2), (key1022, -2), (key1236, -2), (key1044, 4), (key1009, 4), (key1233, 4)]

theorem rawRowCheck13790 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form5 = rawRow13790 := by decide +kernel

def row13790 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck13790 : row13790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13790 := by decide +kernel

theorem rowEval13790 (x : Key → ℝ) : Integer.Sparse.eval row13790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13790, Integer.Sparse.eval_collectBalanced, rawRowCheck13790]

def rawRow13791 : Integer.Sparse Key := [(key1073, 4), (key1247, 4), (key1017, 4), (key1080, -2), (key1038, -2), (key1243, -2), (key1003, -2), (key1236, -2), (key1022, -2), (key1080, -2), (key1038, -2), (key1243, -2), (key1003, -2), (key1236, -2), (key1022, -2), (key1044, 4), (key1233, 4), (key1009, 4)]

theorem rawRowCheck13791 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form5 = rawRow13791 := by decide +kernel

def row13791 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck13791 : row13791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13791 := by decide +kernel

theorem rowEval13791 (x : Key → ℝ) : Integer.Sparse.eval row13791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13791, Integer.Sparse.eval_collectBalanced, rawRowCheck13791]

def rawRow13792 : Integer.Sparse Key := [(key1247, 4), (key1017, 4), (key1073, 4), (key1236, -2), (key1243, -2), (key1022, -2), (key1080, -2), (key1003, -2), (key1038, -2), (key1236, -2), (key1243, -2), (key1022, -2), (key1080, -2), (key1003, -2), (key1038, -2), (key1233, 4), (key1009, 4), (key1044, 4)]

theorem rawRowCheck13792 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form5 = rawRow13792 := by decide +kernel

def row13792 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck13792 : row13792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13792 := by decide +kernel

theorem rowEval13792 (x : Key → ℝ) : Integer.Sparse.eval row13792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13792, Integer.Sparse.eval_collectBalanced, rawRowCheck13792]

def rawRow13793 : Integer.Sparse Key := [(key1247, 4), (key1073, 4), (key1017, 4), (key1243, -2), (key1236, -2), (key1080, -2), (key1022, -2), (key1038, -2), (key1003, -2), (key1243, -2), (key1236, -2), (key1080, -2), (key1022, -2), (key1038, -2), (key1003, -2), (key1233, 4), (key1044, 4), (key1009, 4)]

theorem rawRowCheck13793 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form5 = rawRow13793 := by decide +kernel

def row13793 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck13793 : row13793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13793 := by decide +kernel

theorem rowEval13793 (x : Key → ℝ) : Integer.Sparse.eval row13793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13793, Integer.Sparse.eval_collectBalanced, rawRowCheck13793]

def rawRow13794 : Integer.Sparse Key := [(key1022, 4), (key1080, 4), (key1174, 4), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1009, -2), (key1022, -2), (key1044, -2), (key1130, -2), (key1080, -2), (key1159, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

theorem rawRowCheck13794 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form5 = rawRow13794 := by decide +kernel

def row13794 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13794 : row13794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13794 := by decide +kernel

theorem rowEval13794 (x : Key → ℝ) : Integer.Sparse.eval row13794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13794, Integer.Sparse.eval_collectBalanced, rawRowCheck13794]

def rawRow13795 : Integer.Sparse Key := [(key1022, 4), (key1174, 4), (key1080, 4), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1022, -2), (key1009, -2), (key1130, -2), (key1044, -2), (key1159, -2), (key1080, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

theorem rawRowCheck13795 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form5 = rawRow13795 := by decide +kernel

def row13795 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13795 : row13795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13795 := by decide +kernel

theorem rowEval13795 (x : Key → ℝ) : Integer.Sparse.eval row13795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13795, Integer.Sparse.eval_collectBalanced, rawRowCheck13795]

def rawRow13796 : Integer.Sparse Key := [(key1080, 4), (key1022, 4), (key1174, 4), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1044, -2), (key1080, -2), (key1009, -2), (key1159, -2), (key1022, -2), (key1130, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

theorem rawRowCheck13796 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form5 = rawRow13796 := by decide +kernel

def row13796 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13796 : row13796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13796 := by decide +kernel

theorem rowEval13796 (x : Key → ℝ) : Integer.Sparse.eval row13796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13796, Integer.Sparse.eval_collectBalanced, rawRowCheck13796]

def rawRow13797 : Integer.Sparse Key := [(key1080, 4), (key1174, 4), (key1022, 4), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1080, -2), (key1044, -2), (key1159, -2), (key1009, -2), (key1130, -2), (key1022, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

theorem rawRowCheck13797 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form5 = rawRow13797 := by decide +kernel

def row13797 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13797 : row13797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13797 := by decide +kernel

theorem rowEval13797 (x : Key → ℝ) : Integer.Sparse.eval row13797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13797, Integer.Sparse.eval_collectBalanced, rawRowCheck13797]

def rawRow13798 : Integer.Sparse Key := [(key1174, 4), (key1022, 4), (key1080, 4), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1130, -2), (key1159, -2), (key1022, -2), (key1080, -2), (key1009, -2), (key1044, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

theorem rawRowCheck13798 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form5 = rawRow13798 := by decide +kernel

def row13798 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13798 : row13798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13798 := by decide +kernel

theorem rowEval13798 (x : Key → ℝ) : Integer.Sparse.eval row13798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13798, Integer.Sparse.eval_collectBalanced, rawRowCheck13798]

def rawRow13799 : Integer.Sparse Key := [(key1174, 4), (key1080, 4), (key1022, 4), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1159, -2), (key1130, -2), (key1080, -2), (key1022, -2), (key1044, -2), (key1009, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

theorem rawRowCheck13799 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form5 = rawRow13799 := by decide +kernel

def row13799 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13799 : row13799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13799 := by decide +kernel

theorem rowEval13799 (x : Key → ℝ) : Integer.Sparse.eval row13799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13799, Integer.Sparse.eval_collectBalanced, rawRowCheck13799]

def rawRow13800 : Integer.Sparse Key := [(key1009, 4), (key1159, 4), (key1159, 4), (key1022, -2), (key1022, -2), (key1130, -2), (key1130, -2), (key1174, -2), (key1174, -2), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

theorem rawRowCheck13800 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form5 = rawRow13800 := by decide +kernel

def row13800 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

theorem rowCheck13800 : row13800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13800 := by decide +kernel

theorem rowEval13800 (x : Key → ℝ) : Integer.Sparse.eval row13800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13800, Integer.Sparse.eval_collectBalanced, rawRowCheck13800]

def rawRow13801 : Integer.Sparse Key := [(key1159, 4), (key1009, 4), (key1159, 4), (key1130, -2), (key1174, -2), (key1022, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

theorem rawRowCheck13801 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form5 = rawRow13801 := by decide +kernel

def row13801 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

theorem rowCheck13801 : row13801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13801 := by decide +kernel

theorem rowEval13801 (x : Key → ℝ) : Integer.Sparse.eval row13801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13801, Integer.Sparse.eval_collectBalanced, rawRowCheck13801]

def rawRow13802 : Integer.Sparse Key := [(key1159, 4), (key1159, 4), (key1009, 4), (key1174, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1022, -2), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

theorem rawRowCheck13802 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form5 = rawRow13802 := by decide +kernel

def row13802 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

theorem rowCheck13802 : row13802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13802 := by decide +kernel

theorem rowEval13802 (x : Key → ℝ) : Integer.Sparse.eval row13802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13802, Integer.Sparse.eval_collectBalanced, rawRowCheck13802]

def rawRow13803 : Integer.Sparse Key := [(key1022, 4), (key1080, 4), (key1174, 4), (key1009, -2), (key1022, -2), (key1044, -2), (key1130, -2), (key1080, -2), (key1159, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

theorem rawRowCheck13803 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form5 = rawRow13803 := by decide +kernel

def row13803 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13803 : row13803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13803 := by decide +kernel

theorem rowEval13803 (x : Key → ℝ) : Integer.Sparse.eval row13803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13803, Integer.Sparse.eval_collectBalanced, rawRowCheck13803]

def rawRow13804 : Integer.Sparse Key := [(key1022, 4), (key1174, 4), (key1080, 4), (key1022, -2), (key1009, -2), (key1130, -2), (key1044, -2), (key1159, -2), (key1080, -2), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

theorem rawRowCheck13804 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form5 = rawRow13804 := by decide +kernel

def row13804 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13804 : row13804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13804 := by decide +kernel

theorem rowEval13804 (x : Key → ℝ) : Integer.Sparse.eval row13804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13804, Integer.Sparse.eval_collectBalanced, rawRowCheck13804]

def rawRow13805 : Integer.Sparse Key := [(key1080, 4), (key1022, 4), (key1174, 4), (key1044, -2), (key1080, -2), (key1009, -2), (key1159, -2), (key1022, -2), (key1130, -2), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

theorem rawRowCheck13805 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form5 = rawRow13805 := by decide +kernel

def row13805 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13805 : row13805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13805 := by decide +kernel

theorem rowEval13805 (x : Key → ℝ) : Integer.Sparse.eval row13805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13805, Integer.Sparse.eval_collectBalanced, rawRowCheck13805]

def rawRow13806 : Integer.Sparse Key := [(key1080, 4), (key1174, 4), (key1022, 4), (key1080, -2), (key1044, -2), (key1159, -2), (key1009, -2), (key1130, -2), (key1022, -2), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

theorem rawRowCheck13806 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form5 = rawRow13806 := by decide +kernel

def row13806 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13806 : row13806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13806 := by decide +kernel

theorem rowEval13806 (x : Key → ℝ) : Integer.Sparse.eval row13806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13806, Integer.Sparse.eval_collectBalanced, rawRowCheck13806]

def rawRow13807 : Integer.Sparse Key := [(key1174, 4), (key1022, 4), (key1080, 4), (key1130, -2), (key1159, -2), (key1022, -2), (key1080, -2), (key1009, -2), (key1044, -2), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

theorem rawRowCheck13807 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form5 = rawRow13807 := by decide +kernel

def row13807 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13807 : row13807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13807 := by decide +kernel

theorem rowEval13807 (x : Key → ℝ) : Integer.Sparse.eval row13807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13807, Integer.Sparse.eval_collectBalanced, rawRowCheck13807]

def rawRow13808 : Integer.Sparse Key := [(key1174, 4), (key1080, 4), (key1022, 4), (key1159, -2), (key1130, -2), (key1080, -2), (key1022, -2), (key1044, -2), (key1009, -2), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

theorem rawRowCheck13808 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form5 = rawRow13808 := by decide +kernel

def row13808 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4)]

theorem rowCheck13808 : row13808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13808 := by decide +kernel

theorem rowEval13808 (x : Key → ℝ) : Integer.Sparse.eval row13808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck13808, Integer.Sparse.eval_collectBalanced, rawRowCheck13808]

def rawRow13809 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2614, 2), (key2807, 2), (key2827, 2), (key2624, -1), (key2630, -1), (key2851, -1), (key2868, -1), (key3021, -1), (key3025, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, -1), (key2868, -1), (key2657, 2), (key2918, 2), (key2922, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, -1), (key2922, -1)]

theorem rawRowCheck13809 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form6 = rawRow13809 := by decide +kernel

def row13809 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck13809 : row13809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13809 := by decide +kernel

theorem rowEval13809 (x : Key → ℝ) : Integer.Sparse.eval row13809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13809, Integer.Sparse.eval_collectBalanced, rawRowCheck13809]

def rawRow13810 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2614, 2), (key2827, 2), (key2807, 2), (key2630, -1), (key2624, -1), (key2868, -1), (key2851, -1), (key3025, -1), (key3021, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, -1), (key2858, -1), (key2657, 2), (key2922, 2), (key2918, 2), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, -1), (key2919, -1)]

theorem rawRowCheck13810 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form6 = rawRow13810 := by decide +kernel

def row13810 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck13810 : row13810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13810 := by decide +kernel

theorem rowEval13810 (x : Key → ℝ) : Integer.Sparse.eval row13810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13810, Integer.Sparse.eval_collectBalanced, rawRowCheck13810]

def rawRow13811 : Integer.Sparse Key := [(key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2807, 2), (key2614, 2), (key2827, 2), (key2851, -1), (key3021, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2918, 2), (key2657, 2), (key2922, 2), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2757, -1)]

theorem rawRowCheck13811 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form6 = rawRow13811 := by decide +kernel

def row13811 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck13811 : row13811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13811 := by decide +kernel

theorem rowEval13811 (x : Key → ℝ) : Integer.Sparse.eval row13811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13811, Integer.Sparse.eval_collectBalanced, rawRowCheck13811]

def rawRow13812 : Integer.Sparse Key := [(key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key2807, 2), (key2827, 2), (key2614, 2), (key3021, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key2868, -1), (key2630, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, -1), (key2638, -1), (key2918, 2), (key2922, 2), (key2657, 2), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, -1), (key2659, -1)]

theorem rawRowCheck13812 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form6 = rawRow13812 := by decide +kernel

def row13812 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck13812 : row13812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13812 := by decide +kernel

theorem rowEval13812 (x : Key → ℝ) : Integer.Sparse.eval row13812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13812, Integer.Sparse.eval_collectBalanced, rawRowCheck13812]

def rawRow13813 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2827, 2), (key2614, 2), (key2807, 2), (key2868, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2624, -1), (key2851, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2724, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2630, -1), (key2704, -1), (key2922, 2), (key2657, 2), (key2918, 2), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, -1), (key2752, -1)]

theorem rawRowCheck13813 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form6 = rawRow13813 := by decide +kernel

def row13813 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck13813 : row13813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13813 := by decide +kernel

theorem rowEval13813 (x : Key → ℝ) : Integer.Sparse.eval row13813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13813, Integer.Sparse.eval_collectBalanced, rawRowCheck13813]

def rawRow13814 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key2827, 2), (key2807, 2), (key2614, 2), (key3025, -1), (key2868, -1), (key3021, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2868, -1), (key2724, -1), (key2858, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2922, 2), (key2918, 2), (key2657, 2), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, -1), (key2657, -1)]

theorem rawRowCheck13814 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form6 = rawRow13814 := by decide +kernel

def row13814 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

theorem rowCheck13814 : row13814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13814 := by decide +kernel

theorem rowEval13814 (x : Key → ℝ) : Integer.Sparse.eval row13814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13814, Integer.Sparse.eval_collectBalanced, rawRowCheck13814]

def rawRow13815 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2638, -1), (key2638, -1), (key2858, -1), (key2858, -1), (key3022, -1), (key3022, -1), (key2630, 2), (key2630, 2), (key2704, 2), (key2704, 2), (key3021, 2), (key3021, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2659, 2), (key2919, 2), (key2919, 2), (key2657, -1), (key2657, -1), (key2752, -1), (key2752, -1), (key2918, -1), (key2918, -1)]

theorem rawRowCheck13815 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form6 = rawRow13815 := by decide +kernel

def row13815 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2704, 4), (key2752, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2918, -2), (key2919, 4), (key3021, 4), (key3022, -2)]

theorem rowCheck13815 : row13815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13815 := by decide +kernel

theorem rowEval13815 (x : Key → ℝ) : Integer.Sparse.eval row13815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13815, Integer.Sparse.eval_collectBalanced, rawRowCheck13815]

def rawRow13816 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2858, -1), (key3022, -1), (key2638, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2704, 2), (key3021, 2), (key2630, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2919, 2), (key2659, 2), (key2919, 2), (key2752, -1), (key2918, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2752, -1)]

theorem rawRowCheck13816 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form6 = rawRow13816 := by decide +kernel

def row13816 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2704, 4), (key2752, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2918, -2), (key2919, 4), (key3021, 4), (key3022, -2)]

theorem rowCheck13816 : row13816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13816 := by decide +kernel

theorem rowEval13816 (x : Key → ℝ) : Integer.Sparse.eval row13816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13816, Integer.Sparse.eval_collectBalanced, rawRowCheck13816]

def rawRow13817 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key3022, -1), (key2858, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key3021, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2630, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2919, 2), (key2919, 2), (key2659, 2), (key2918, -1), (key2752, -1), (key2918, -1), (key2657, -1), (key2752, -1), (key2657, -1)]

theorem rawRowCheck13817 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form6 = rawRow13817 := by decide +kernel

def row13817 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2704, 4), (key2752, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2918, -2), (key2919, 4), (key3021, 4), (key3022, -2)]

theorem rowCheck13817 : row13817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13817 := by decide +kernel

theorem rowEval13817 (x : Key → ℝ) : Integer.Sparse.eval row13817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13817, Integer.Sparse.eval_collectBalanced, rawRowCheck13817]

def rawRow13818 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2638, 2), (key2858, 2), (key3022, 2), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, -1), (key2922, -1), (key2614, 2), (key2807, 2), (key2827, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, -1), (key2868, -1)]

theorem rawRowCheck13818 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form6 = rawRow13818 := by decide +kernel

def row13818 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

theorem rowCheck13818 : row13818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13818 := by decide +kernel

theorem rowEval13818 (x : Key → ℝ) : Integer.Sparse.eval row13818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13818, Integer.Sparse.eval_collectBalanced, rawRowCheck13818]

def rawRow13819 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2638, 2), (key3022, 2), (key2858, 2), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, -1), (key2919, -1), (key2614, 2), (key2827, 2), (key2807, 2), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, -1), (key2858, -1)]

theorem rawRowCheck13819 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form6 = rawRow13819 := by decide +kernel

def row13819 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

theorem rowCheck13819 : row13819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13819 := by decide +kernel

theorem rowEval13819 (x : Key → ℝ) : Integer.Sparse.eval row13819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13819, Integer.Sparse.eval_collectBalanced, rawRowCheck13819]

def rawRow13820 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2858, 2), (key2638, 2), (key3022, 2), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2807, 2), (key2614, 2), (key2827, 2), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2724, -1)]

theorem rawRowCheck13820 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form6 = rawRow13820 := by decide +kernel

def row13820 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

theorem rowCheck13820 : row13820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13820 := by decide +kernel

theorem rowEval13820 (x : Key → ℝ) : Integer.Sparse.eval row13820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13820, Integer.Sparse.eval_collectBalanced, rawRowCheck13820]

def rawRow13821 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2858, 2), (key3022, 2), (key2638, 2), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, -1), (key2659, -1), (key2807, 2), (key2827, 2), (key2614, 2), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, -1), (key2638, -1)]

theorem rawRowCheck13821 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form6 = rawRow13821 := by decide +kernel

def row13821 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

theorem rowCheck13821 : row13821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13821 := by decide +kernel

theorem rowEval13821 (x : Key → ℝ) : Integer.Sparse.eval row13821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13821, Integer.Sparse.eval_collectBalanced, rawRowCheck13821]

def rawRow13822 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key3022, 2), (key2638, 2), (key2858, 2), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, -1), (key2752, -1), (key2827, 2), (key2614, 2), (key2807, 2), (key2724, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2630, -1), (key2704, -1)]

theorem rawRowCheck13822 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form6 = rawRow13822 := by decide +kernel

def row13822 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

theorem rowCheck13822 : row13822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13822 := by decide +kernel

theorem rowEval13822 (x : Key → ℝ) : Integer.Sparse.eval row13822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck13822, Integer.Sparse.eval_collectBalanced, rawRowCheck13822]

def rawRow13823 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3022, 2), (key2858, 2), (key2638, 2), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2827, 2), (key2807, 2), (key2614, 2), (key2868, -1), (key2724, -1), (key2858, -1), (key2638, -1), (key2704, -1), (key2630, -1)]

theorem rawRowCheck13823 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form6 = rawRow13823 := by decide +kernel

def row13823 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

theorem rowCheck13823 : row13823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13823 := by decide +kernel

theorem rowEval13823 (x : Key → ℝ) : Integer.Sparse.eval row13823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck13823, Integer.Sparse.eval_collectBalanced, rawRowCheck13823]

end MUB6.Certificate.GramRows

end OAI

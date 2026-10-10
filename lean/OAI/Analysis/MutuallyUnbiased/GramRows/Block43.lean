import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
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

def rawRow2432 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2398, -2), (key2401, 6), (key2842, 2), (key2965, 2), (key2839, 2), (key2874, -2), (key2586, -2), (key2842, -2), (key2886, -6), (key2908, 2), (key2597, 2), (key2886, 2)]

theorem rawRowCheck2432 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form11 = rawRow2432 := by decide +kernel

def row2432 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

theorem rowCheck2432 : row2432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2432 := by decide +kernel

theorem rowEval2432 (x : Key → ℝ) : Integer.Sparse.eval row2432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2432, Integer.Sparse.eval_collectBalanced, rawRowCheck2432]

def rawRow2433 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2398, -2), (key2401, 6), (key2965, 2), (key2842, 2), (key2839, 2), (key2874, -2), (key2842, -2), (key2586, -2), (key2886, -6), (key2908, 2), (key2886, 2), (key2597, 2)]

theorem rawRowCheck2433 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form11 = rawRow2433 := by decide +kernel

def row2433 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

theorem rowCheck2433 : row2433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2433 := by decide +kernel

theorem rowEval2433 (x : Key → ℝ) : Integer.Sparse.eval row2433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2433, Integer.Sparse.eval_collectBalanced, rawRowCheck2433]

def rawRow2434 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2370, 2), (key2373, 2), (key2386, 2), (key2928, -2), (key2965, -2), (key2987, -2), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2)]

theorem rawRowCheck2434 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form11 = rawRow2434 := by decide +kernel

def row2434 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck2434 : row2434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2434 := by decide +kernel

theorem rowEval2434 (x : Key → ℝ) : Integer.Sparse.eval row2434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2434, Integer.Sparse.eval_collectBalanced, rawRowCheck2434]

def rawRow2435 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2476, -2), (key2499, 6), (key2373, 2), (key2370, 2), (key2386, 2), (key2928, -2), (key2987, -2), (key2965, -2), (key2586, -6), (key2765, 2), (key2874, 2), (key2842, 2)]

theorem rawRowCheck2435 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form11 = rawRow2435 := by decide +kernel

def row2435 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck2435 : row2435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2435 := by decide +kernel

theorem rowEval2435 (x : Key → ℝ) : Integer.Sparse.eval row2435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2435, Integer.Sparse.eval_collectBalanced, rawRowCheck2435]

def rawRow2436 : Integer.Sparse Key := [(key2464, -2), (key2476, -2), (key2467, -2), (key2499, 6), (key2370, 2), (key2386, 2), (key2373, 2), (key2965, -2), (key2928, -2), (key2987, -2), (key2586, -6), (key2842, 2), (key2765, 2), (key2874, 2)]

theorem rawRowCheck2436 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form11 = rawRow2436 := by decide +kernel

def row2436 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck2436 : row2436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2436 := by decide +kernel

theorem rowEval2436 (x : Key → ℝ) : Integer.Sparse.eval row2436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2436, Integer.Sparse.eval_collectBalanced, rawRowCheck2436]

def rawRow2437 : Integer.Sparse Key := [(key2476, -2), (key2464, -2), (key2467, -2), (key2499, 6), (key2386, 2), (key2370, 2), (key2373, 2), (key2965, -2), (key2987, -2), (key2928, -2), (key2586, -6), (key2842, 2), (key2874, 2), (key2765, 2)]

theorem rawRowCheck2437 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form11 = rawRow2437 := by decide +kernel

def row2437 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck2437 : row2437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2437 := by decide +kernel

theorem rowEval2437 (x : Key → ℝ) : Integer.Sparse.eval row2437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2437, Integer.Sparse.eval_collectBalanced, rawRowCheck2437]

def rawRow2438 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2464, -2), (key2499, 6), (key2373, 2), (key2386, 2), (key2370, 2), (key2987, -2), (key2928, -2), (key2965, -2), (key2586, -6), (key2874, 2), (key2765, 2), (key2842, 2)]

theorem rawRowCheck2438 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form11 = rawRow2438 := by decide +kernel

def row2438 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck2438 : row2438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2438 := by decide +kernel

theorem rowEval2438 (x : Key → ℝ) : Integer.Sparse.eval row2438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2438, Integer.Sparse.eval_collectBalanced, rawRowCheck2438]

def rawRow2439 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2464, -2), (key2499, 6), (key2386, 2), (key2373, 2), (key2370, 2), (key2987, -2), (key2965, -2), (key2928, -2), (key2586, -6), (key2874, 2), (key2842, 2), (key2765, 2)]

theorem rawRowCheck2439 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form11 = rawRow2439 := by decide +kernel

def row2439 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

theorem rowCheck2439 : row2439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2439 := by decide +kernel

theorem rowEval2439 (x : Key → ℝ) : Integer.Sparse.eval row2439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2439, Integer.Sparse.eval_collectBalanced, rawRowCheck2439]

def rawRow2440 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2499, -2), (key2476, 6), (key2398, 2), (key2401, 2), (key2433, 2), (key2597, -2), (key2886, -2), (key2908, -2), (key2765, -6), (key2586, 2), (key2842, 2), (key2874, 2)]

theorem rawRowCheck2440 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form11 = rawRow2440 := by decide +kernel

def row2440 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

theorem rowCheck2440 : row2440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2440 := by decide +kernel

theorem rowEval2440 (x : Key → ℝ) : Integer.Sparse.eval row2440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2440, Integer.Sparse.eval_collectBalanced, rawRowCheck2440]

def rawRow2441 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2499, -2), (key2476, 6), (key2401, 2), (key2398, 2), (key2433, 2), (key2597, -2), (key2908, -2), (key2886, -2), (key2765, -6), (key2586, 2), (key2874, 2), (key2842, 2)]

theorem rawRowCheck2441 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form11 = rawRow2441 := by decide +kernel

def row2441 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

theorem rowCheck2441 : row2441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2441 := by decide +kernel

theorem rowEval2441 (x : Key → ℝ) : Integer.Sparse.eval row2441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2441, Integer.Sparse.eval_collectBalanced, rawRowCheck2441]

def rawRow2442 : Integer.Sparse Key := [(key2464, -2), (key2499, -2), (key2467, -2), (key2476, 6), (key2398, 2), (key2433, 2), (key2401, 2), (key2886, -2), (key2597, -2), (key2908, -2), (key2765, -6), (key2842, 2), (key2586, 2), (key2874, 2)]

theorem rawRowCheck2442 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form11 = rawRow2442 := by decide +kernel

def row2442 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

theorem rowCheck2442 : row2442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2442 := by decide +kernel

theorem rowEval2442 (x : Key → ℝ) : Integer.Sparse.eval row2442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2442, Integer.Sparse.eval_collectBalanced, rawRowCheck2442]

def rawRow2443 : Integer.Sparse Key := [(key2499, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2433, 2), (key2398, 2), (key2401, 2), (key2886, -2), (key2908, -2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2586, 2)]

theorem rawRowCheck2443 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form11 = rawRow2443 := by decide +kernel

def row2443 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

theorem rowCheck2443 : row2443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2443 := by decide +kernel

theorem rowEval2443 (x : Key → ℝ) : Integer.Sparse.eval row2443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2443, Integer.Sparse.eval_collectBalanced, rawRowCheck2443]

def rawRow2444 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2464, -2), (key2476, 6), (key2401, 2), (key2433, 2), (key2398, 2), (key2908, -2), (key2597, -2), (key2886, -2), (key2765, -6), (key2874, 2), (key2586, 2), (key2842, 2)]

theorem rawRowCheck2444 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form11 = rawRow2444 := by decide +kernel

def row2444 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

theorem rowCheck2444 : row2444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2444 := by decide +kernel

theorem rowEval2444 (x : Key → ℝ) : Integer.Sparse.eval row2444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2444, Integer.Sparse.eval_collectBalanced, rawRowCheck2444]

def rawRow2445 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2464, -2), (key2476, 6), (key2433, 2), (key2401, 2), (key2398, 2), (key2908, -2), (key2886, -2), (key2597, -2), (key2765, -6), (key2874, 2), (key2842, 2), (key2586, 2)]

theorem rawRowCheck2445 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form11 = rawRow2445 := by decide +kernel

def row2445 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2586, 2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2886, -2), (key2908, -2)]

theorem rowCheck2445 : row2445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2445 := by decide +kernel

theorem rowEval2445 (x : Key → ℝ) : Integer.Sparse.eval row2445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2445, Integer.Sparse.eval_collectBalanced, rawRowCheck2445]

def rawRow2446 : Integer.Sparse Key := [(key2608, -2), (key2611, -2), (key2611, -2), (key2624, 1), (key2627, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2636, 1), (key2663, 2), (key2666, 2), (key2666, 2), (key2698, -1), (key2701, -1), (key2698, -1), (key2722, -1), (key2701, -1), (key2722, -1), (key2778, -1), (key2781, -1), (key2778, -1), (key2790, -1), (key2781, -1), (key2790, -1), (key2801, 1), (key2804, 1), (key2801, 1), (key2825, 1), (key2804, 1), (key2825, 1)]

theorem rawRowCheck2446 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form12 = rawRow2446 := by decide +kernel

def row2446 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2663, 2), (key2666, 4), (key2698, -2), (key2701, -2), (key2722, -2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 2), (key2804, 2), (key2825, 2)]

theorem rowCheck2446 : row2446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2446 := by decide +kernel

theorem rowEval2446 (x : Key → ℝ) : Integer.Sparse.eval row2446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2446, Integer.Sparse.eval_collectBalanced, rawRowCheck2446]

def rawRow2447 : Integer.Sparse Key := [(key2611, -2), (key2608, -2), (key2611, -2), (key2627, 1), (key2624, 1), (key2636, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2666, 2), (key2663, 2), (key2666, 2), (key2701, -1), (key2698, -1), (key2722, -1), (key2698, -1), (key2722, -1), (key2701, -1), (key2781, -1), (key2778, -1), (key2790, -1), (key2778, -1), (key2790, -1), (key2781, -1), (key2804, 1), (key2801, 1), (key2825, 1), (key2801, 1), (key2825, 1), (key2804, 1)]

theorem rawRowCheck2447 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form12 = rawRow2447 := by decide +kernel

def row2447 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2663, 2), (key2666, 4), (key2698, -2), (key2701, -2), (key2722, -2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 2), (key2804, 2), (key2825, 2)]

theorem rowCheck2447 : row2447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2447 := by decide +kernel

theorem rowEval2447 (x : Key → ℝ) : Integer.Sparse.eval row2447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2447, Integer.Sparse.eval_collectBalanced, rawRowCheck2447]

def rawRow2448 : Integer.Sparse Key := [(key2611, -2), (key2611, -2), (key2608, -2), (key2636, 1), (key2636, 1), (key2627, 1), (key2627, 1), (key2624, 1), (key2624, 1), (key2666, 2), (key2666, 2), (key2663, 2), (key2722, -1), (key2722, -1), (key2701, -1), (key2701, -1), (key2698, -1), (key2698, -1), (key2790, -1), (key2790, -1), (key2781, -1), (key2781, -1), (key2778, -1), (key2778, -1), (key2825, 1), (key2825, 1), (key2804, 1), (key2804, 1), (key2801, 1), (key2801, 1)]

theorem rawRowCheck2448 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form12 = rawRow2448 := by decide +kernel

def row2448 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2663, 2), (key2666, 4), (key2698, -2), (key2701, -2), (key2722, -2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 2), (key2804, 2), (key2825, 2)]

theorem rowCheck2448 : row2448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2448 := by decide +kernel

theorem rowEval2448 (x : Key → ℝ) : Integer.Sparse.eval row2448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2448, Integer.Sparse.eval_collectBalanced, rawRowCheck2448]

def rawRow2449 : Integer.Sparse Key := [(key2624, -2), (key2627, -2), (key2636, -2), (key2608, 1), (key2611, 1), (key2624, 1), (key2636, 1), (key2645, 1), (key2651, 1), (key2698, 2), (key2701, 2), (key2734, 2), (key2663, -1), (key2666, -1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, -1), (key2851, -1), (key2856, -1), (key2892, -1), (key2895, -1), (key2778, 1), (key2781, 1), (key2851, 1), (key2866, 1), (key2892, 1), (key2902, 1)]

theorem rawRowCheck2449 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form12 = rawRow2449 := by decide +kernel

def row2449 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

theorem rowCheck2449 : row2449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2449 := by decide +kernel

theorem rowEval2449 (x : Key → ℝ) : Integer.Sparse.eval row2449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2449, Integer.Sparse.eval_collectBalanced, rawRowCheck2449]

def rawRow2450 : Integer.Sparse Key := [(key2627, -2), (key2624, -2), (key2636, -2), (key2611, 1), (key2608, 1), (key2636, 1), (key2624, 1), (key2651, 1), (key2645, 1), (key2701, 2), (key2698, 2), (key2734, 2), (key2666, -1), (key2663, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2734, -1), (key2804, -1), (key2801, -1), (key2856, -1), (key2851, -1), (key2895, -1), (key2892, -1), (key2781, 1), (key2778, 1), (key2866, 1), (key2851, 1), (key2902, 1), (key2892, 1)]

theorem rawRowCheck2450 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form12 = rawRow2450 := by decide +kernel

def row2450 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

theorem rowCheck2450 : row2450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2450 := by decide +kernel

theorem rowEval2450 (x : Key → ℝ) : Integer.Sparse.eval row2450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2450, Integer.Sparse.eval_collectBalanced, rawRowCheck2450]

def rawRow2451 : Integer.Sparse Key := [(key2624, -2), (key2636, -2), (key2627, -2), (key2624, 1), (key2636, 1), (key2608, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2698, 2), (key2734, 2), (key2701, 2), (key2698, -1), (key2734, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2851, -1), (key2892, -1), (key2801, -1), (key2895, -1), (key2804, -1), (key2856, -1), (key2851, 1), (key2892, 1), (key2778, 1), (key2902, 1), (key2781, 1), (key2866, 1)]

theorem rawRowCheck2451 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form12 = rawRow2451 := by decide +kernel

def row2451 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

theorem rowCheck2451 : row2451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2451 := by decide +kernel

theorem rowEval2451 (x : Key → ℝ) : Integer.Sparse.eval row2451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2451, Integer.Sparse.eval_collectBalanced, rawRowCheck2451]

def rawRow2452 : Integer.Sparse Key := [(key2636, -2), (key2624, -2), (key2627, -2), (key2636, 1), (key2624, 1), (key2651, 1), (key2608, 1), (key2636, 1), (key2611, 1), (key2734, 2), (key2698, 2), (key2701, 2), (key2734, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2722, -1), (key2666, -1), (key2892, -1), (key2851, -1), (key2895, -1), (key2801, -1), (key2856, -1), (key2804, -1), (key2892, 1), (key2851, 1), (key2902, 1), (key2778, 1), (key2866, 1), (key2781, 1)]

theorem rawRowCheck2452 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form12 = rawRow2452 := by decide +kernel

def row2452 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

theorem rowCheck2452 : row2452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2452 := by decide +kernel

theorem rowEval2452 (x : Key → ℝ) : Integer.Sparse.eval row2452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2452, Integer.Sparse.eval_collectBalanced, rawRowCheck2452]

def rawRow2453 : Integer.Sparse Key := [(key2627, -2), (key2636, -2), (key2624, -2), (key2645, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2608, 1), (key2624, 1), (key2701, 2), (key2734, 2), (key2698, 2), (key2722, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2663, -1), (key2698, -1), (key2856, -1), (key2895, -1), (key2804, -1), (key2892, -1), (key2801, -1), (key2851, -1), (key2866, 1), (key2902, 1), (key2781, 1), (key2892, 1), (key2778, 1), (key2851, 1)]

theorem rawRowCheck2453 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form12 = rawRow2453 := by decide +kernel

def row2453 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

theorem rowCheck2453 : row2453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2453 := by decide +kernel

theorem rowEval2453 (x : Key → ℝ) : Integer.Sparse.eval row2453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2453, Integer.Sparse.eval_collectBalanced, rawRowCheck2453]

def rawRow2454 : Integer.Sparse Key := [(key2636, -2), (key2627, -2), (key2624, -2), (key2651, 1), (key2645, 1), (key2636, 1), (key2611, 1), (key2624, 1), (key2608, 1), (key2734, 2), (key2701, 2), (key2698, 2), (key2745, -1), (key2722, -1), (key2734, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2895, -1), (key2856, -1), (key2892, -1), (key2804, -1), (key2851, -1), (key2801, -1), (key2902, 1), (key2866, 1), (key2892, 1), (key2781, 1), (key2851, 1), (key2778, 1)]

theorem rawRowCheck2454 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form12 = rawRow2454 := by decide +kernel

def row2454 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, -1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1)]

theorem rowCheck2454 : row2454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2454 := by decide +kernel

theorem rowEval2454 (x : Key → ℝ) : Integer.Sparse.eval row2454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2454, Integer.Sparse.eval_collectBalanced, rawRowCheck2454]

def rawRow2455 : Integer.Sparse Key := [(key2663, -2), (key2666, -2), (key2666, -2), (key2698, 1), (key2701, 1), (key2698, 1), (key2734, 1), (key2701, 1), (key2734, 1), (key2608, 2), (key2611, 2), (key2611, 2), (key2801, -1), (key2804, -1), (key2801, -1), (key2825, -1), (key2804, -1), (key2825, -1), (key2624, -1), (key2627, -1), (key2624, -1), (key2636, -1), (key2627, -1), (key2636, -1), (key2698, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2722, 1)]

theorem rawRowCheck2455 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form12 = rawRow2455 := by decide +kernel

def row2455 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2624, -2), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, -4), (key2698, 4), (key2701, 4), (key2722, 2), (key2734, 2), (key2801, -2), (key2804, -2), (key2825, -2)]

theorem rowCheck2455 : row2455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2455 := by decide +kernel

theorem rowEval2455 (x : Key → ℝ) : Integer.Sparse.eval row2455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2455, Integer.Sparse.eval_collectBalanced, rawRowCheck2455]

def rawRow2456 : Integer.Sparse Key := [(key2666, -2), (key2663, -2), (key2666, -2), (key2701, 1), (key2698, 1), (key2734, 1), (key2698, 1), (key2734, 1), (key2701, 1), (key2611, 2), (key2608, 2), (key2611, 2), (key2804, -1), (key2801, -1), (key2825, -1), (key2801, -1), (key2825, -1), (key2804, -1), (key2627, -1), (key2624, -1), (key2636, -1), (key2624, -1), (key2636, -1), (key2627, -1), (key2701, 1), (key2698, 1), (key2722, 1), (key2698, 1), (key2722, 1), (key2701, 1)]

theorem rawRowCheck2456 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form12 = rawRow2456 := by decide +kernel

def row2456 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2624, -2), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, -4), (key2698, 4), (key2701, 4), (key2722, 2), (key2734, 2), (key2801, -2), (key2804, -2), (key2825, -2)]

theorem rowCheck2456 : row2456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2456 := by decide +kernel

theorem rowEval2456 (x : Key → ℝ) : Integer.Sparse.eval row2456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2456, Integer.Sparse.eval_collectBalanced, rawRowCheck2456]

def rawRow2457 : Integer.Sparse Key := [(key2666, -2), (key2666, -2), (key2663, -2), (key2734, 1), (key2734, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1), (key2611, 2), (key2611, 2), (key2608, 2), (key2825, -1), (key2825, -1), (key2804, -1), (key2804, -1), (key2801, -1), (key2801, -1), (key2636, -1), (key2636, -1), (key2627, -1), (key2627, -1), (key2624, -1), (key2624, -1), (key2722, 1), (key2722, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1)]

theorem rawRowCheck2457 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form12 = rawRow2457 := by decide +kernel

def row2457 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2624, -2), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, -4), (key2698, 4), (key2701, 4), (key2722, 2), (key2734, 2), (key2801, -2), (key2804, -2), (key2825, -2)]

theorem rowCheck2457 : row2457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2457 := by decide +kernel

theorem rowEval2457 (x : Key → ℝ) : Integer.Sparse.eval row2457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2457, Integer.Sparse.eval_collectBalanced, rawRowCheck2457]

def rawRow2458 : Integer.Sparse Key := [(key2698, -2), (key2701, -2), (key2722, -2), (key2663, 1), (key2666, 1), (key2698, 1), (key2734, 1), (key2722, 1), (key2745, 1), (key2801, 2), (key2804, 2), (key2825, 2), (key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2698, -1), (key2701, -1), (key2851, -1), (key2856, -1), (key2971, -1), (key2974, -1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1)]

theorem rawRowCheck2458 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form12 = rawRow2458 := by decide +kernel

def row2458 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck2458 : row2458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2458 := by decide +kernel

theorem rowEval2458 (x : Key → ℝ) : Integer.Sparse.eval row2458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2458, Integer.Sparse.eval_collectBalanced, rawRowCheck2458]

def rawRow2459 : Integer.Sparse Key := [(key2701, -2), (key2698, -2), (key2722, -2), (key2666, 1), (key2663, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2722, 1), (key2804, 2), (key2801, 2), (key2825, 2), (key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2701, -1), (key2698, -1), (key2856, -1), (key2851, -1), (key2974, -1), (key2971, -1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1)]

theorem rawRowCheck2459 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form12 = rawRow2459 := by decide +kernel

def row2459 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck2459 : row2459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2459 := by decide +kernel

theorem rowEval2459 (x : Key → ℝ) : Integer.Sparse.eval row2459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2459, Integer.Sparse.eval_collectBalanced, rawRowCheck2459]

def rawRow2460 : Integer.Sparse Key := [(key2698, -2), (key2722, -2), (key2701, -2), (key2698, 1), (key2722, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2801, 2), (key2825, 2), (key2804, 2), (key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2851, -1), (key2971, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1)]

theorem rawRowCheck2460 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form12 = rawRow2460 := by decide +kernel

def row2460 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2856, -1), (key2866, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck2460 : row2460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2460 := by decide +kernel

theorem rowEval2460 (x : Key → ℝ) : Integer.Sparse.eval row2460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2460, Integer.Sparse.eval_collectBalanced, rawRowCheck2460]

def rawRow2461 : Integer.Sparse Key := [(key2722, -2), (key2698, -2), (key2701, -2), (key2722, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2734, 1), (key2666, 1), (key2825, 2), (key2801, 2), (key2804, 2), (key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2971, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2856, -1), (key2701, -1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1)]

theorem rawRowCheck2461 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form12 = rawRow2461 := by decide +kernel

def row2461 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2856, -1), (key2866, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck2461 : row2461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2461 := by decide +kernel

theorem rowEval2461 (x : Key → ℝ) : Integer.Sparse.eval row2461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck2461, Integer.Sparse.eval_collectBalanced, rawRowCheck2461]

def rawRow2462 : Integer.Sparse Key := [(key2701, -2), (key2722, -2), (key2698, -2), (key2734, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2663, 1), (key2698, 1), (key2804, 2), (key2825, 2), (key2801, 2), (key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2856, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2698, -1), (key2851, -1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1)]

theorem rawRowCheck2462 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form12 = rawRow2462 := by decide +kernel

def row2462 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck2462 : row2462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2462 := by decide +kernel

theorem rowEval2462 (x : Key → ℝ) : Integer.Sparse.eval row2462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2462, Integer.Sparse.eval_collectBalanced, rawRowCheck2462]

def rawRow2463 : Integer.Sparse Key := [(key2722, -2), (key2701, -2), (key2698, -2), (key2745, 1), (key2734, 1), (key2722, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2825, 2), (key2804, 2), (key2801, 2), (key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2974, -1), (key2856, -1), (key2971, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1)]

theorem rawRowCheck2463 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form12 = rawRow2463 := by decide +kernel

def row2463 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 1), (key2663, 1), (key2666, 1), (key2698, -2), (key2701, -3), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, 1), (key2804, 2), (key2825, 1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck2463 : row2463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2463 := by decide +kernel

theorem rowEval2463 (x : Key → ℝ) : Integer.Sparse.eval row2463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck2463, Integer.Sparse.eval_collectBalanced, rawRowCheck2463]

def rawRow2464 : Integer.Sparse Key := [(key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2851, 1), (key2892, 1), (key2856, 1), (key2895, 1), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, -1), (key2701, -1), (key2851, -1), (key2971, -1), (key2856, -1), (key2974, -1), (key2608, -1), (key2611, -1), (key2624, -1), (key2636, -1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1)]

theorem rawRowCheck2464 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form12 = rawRow2464 := by decide +kernel

def row2464 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

theorem rowCheck2464 : row2464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2464 := by decide +kernel

theorem rowEval2464 (x : Key → ℝ) : Integer.Sparse.eval row2464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2464, Integer.Sparse.eval_collectBalanced, rawRowCheck2464]

def rawRow2465 : Integer.Sparse Key := [(key2781, -2), (key2778, -2), (key2790, -2), (key2804, 1), (key2801, 1), (key2892, 1), (key2851, 1), (key2895, 1), (key2856, 1), (key2627, 2), (key2624, 2), (key2636, 2), (key2701, -1), (key2698, -1), (key2971, -1), (key2851, -1), (key2974, -1), (key2856, -1), (key2611, -1), (key2608, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2645, -1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1)]

theorem rawRowCheck2465 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form12 = rawRow2465 := by decide +kernel

def row2465 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

theorem rowCheck2465 : row2465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2465 := by decide +kernel

theorem rowEval2465 (x : Key → ℝ) : Integer.Sparse.eval row2465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2465, Integer.Sparse.eval_collectBalanced, rawRowCheck2465]

def rawRow2466 : Integer.Sparse Key := [(key2778, -2), (key2790, -2), (key2781, -2), (key2851, 1), (key2856, 1), (key2801, 1), (key2895, 1), (key2804, 1), (key2892, 1), (key2624, 2), (key2636, 2), (key2627, 2), (key2851, -1), (key2856, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2624, -1), (key2636, -1), (key2608, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1)]

theorem rawRowCheck2466 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form12 = rawRow2466 := by decide +kernel

def row2466 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

theorem rowCheck2466 : row2466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2466 := by decide +kernel

theorem rowEval2466 (x : Key → ℝ) : Integer.Sparse.eval row2466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2466, Integer.Sparse.eval_collectBalanced, rawRowCheck2466]

def rawRow2467 : Integer.Sparse Key := [(key2790, -2), (key2778, -2), (key2781, -2), (key2856, 1), (key2851, 1), (key2895, 1), (key2801, 1), (key2892, 1), (key2804, 1), (key2636, 2), (key2624, 2), (key2627, 2), (key2856, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2971, -1), (key2701, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2608, -1), (key2636, -1), (key2611, -1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1)]

theorem rawRowCheck2467 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form12 = rawRow2467 := by decide +kernel

def row2467 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

theorem rowCheck2467 : row2467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2467 := by decide +kernel

theorem rowEval2467 (x : Key → ℝ) : Integer.Sparse.eval row2467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2467, Integer.Sparse.eval_collectBalanced, rawRowCheck2467]

def rawRow2468 : Integer.Sparse Key := [(key2781, -2), (key2790, -2), (key2778, -2), (key2892, 1), (key2895, 1), (key2804, 1), (key2856, 1), (key2801, 1), (key2851, 1), (key2627, 2), (key2636, 2), (key2624, 2), (key2971, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2698, -1), (key2851, -1), (key2645, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2608, -1), (key2624, -1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1)]

theorem rawRowCheck2468 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form12 = rawRow2468 := by decide +kernel

def row2468 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

theorem rowCheck2468 : row2468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2468 := by decide +kernel

theorem rowEval2468 (x : Key → ℝ) : Integer.Sparse.eval row2468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2468, Integer.Sparse.eval_collectBalanced, rawRowCheck2468]

def rawRow2469 : Integer.Sparse Key := [(key2790, -2), (key2781, -2), (key2778, -2), (key2895, 1), (key2892, 1), (key2856, 1), (key2804, 1), (key2851, 1), (key2801, 1), (key2636, 2), (key2627, 2), (key2624, 2), (key2974, -1), (key2971, -1), (key2856, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2651, -1), (key2645, -1), (key2636, -1), (key2611, -1), (key2624, -1), (key2608, -1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1)]

theorem rawRowCheck2469 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form12 = rawRow2469 := by decide +kernel

def row2469 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, 1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2701, -1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2892, 1), (key2895, 1), (key2971, -1), (key2974, -1)]

theorem rowCheck2469 : row2469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2469 := by decide +kernel

theorem rowEval2469 (x : Key → ℝ) : Integer.Sparse.eval row2469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2469, Integer.Sparse.eval_collectBalanced, rawRowCheck2469]

def rawRow2470 : Integer.Sparse Key := [(key2801, -2), (key2804, -2), (key2825, -2), (key2778, 1), (key2781, 1), (key2851, 1), (key2892, 1), (key2866, 1), (key2902, 1), (key2698, 2), (key2701, 2), (key2722, 2), (key2624, -1), (key2627, -1), (key2851, -1), (key2971, -1), (key2866, -1), (key2981, -1), (key2663, -1), (key2666, -1), (key2698, -1), (key2734, -1), (key2722, -1), (key2745, -1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1)]

theorem rawRowCheck2470 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form12 = rawRow2470 := by decide +kernel

def row2470 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

theorem rowCheck2470 : row2470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2470 := by decide +kernel

theorem rowEval2470 (x : Key → ℝ) : Integer.Sparse.eval row2470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2470, Integer.Sparse.eval_collectBalanced, rawRowCheck2470]

def rawRow2471 : Integer.Sparse Key := [(key2804, -2), (key2801, -2), (key2825, -2), (key2781, 1), (key2778, 1), (key2892, 1), (key2851, 1), (key2902, 1), (key2866, 1), (key2701, 2), (key2698, 2), (key2722, 2), (key2627, -1), (key2624, -1), (key2971, -1), (key2851, -1), (key2981, -1), (key2866, -1), (key2666, -1), (key2663, -1), (key2734, -1), (key2698, -1), (key2745, -1), (key2722, -1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1)]

theorem rawRowCheck2471 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form12 = rawRow2471 := by decide +kernel

def row2471 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

theorem rowCheck2471 : row2471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2471 := by decide +kernel

theorem rowEval2471 (x : Key → ℝ) : Integer.Sparse.eval row2471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2471, Integer.Sparse.eval_collectBalanced, rawRowCheck2471]

def rawRow2472 : Integer.Sparse Key := [(key2801, -2), (key2825, -2), (key2804, -2), (key2851, 1), (key2866, 1), (key2778, 1), (key2902, 1), (key2781, 1), (key2892, 1), (key2698, 2), (key2722, 2), (key2701, 2), (key2851, -1), (key2866, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2698, -1), (key2722, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1)]

theorem rawRowCheck2472 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form12 = rawRow2472 := by decide +kernel

def row2472 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2892, 1), (key2902, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

theorem rowCheck2472 : row2472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2472 := by decide +kernel

theorem rowEval2472 (x : Key → ℝ) : Integer.Sparse.eval row2472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2472, Integer.Sparse.eval_collectBalanced, rawRowCheck2472]

def rawRow2473 : Integer.Sparse Key := [(key2825, -2), (key2801, -2), (key2804, -2), (key2866, 1), (key2851, 1), (key2902, 1), (key2778, 1), (key2892, 1), (key2781, 1), (key2722, 2), (key2698, 2), (key2701, 2), (key2866, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2971, -1), (key2627, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2734, -1), (key2666, -1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1)]

theorem rawRowCheck2473 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form12 = rawRow2473 := by decide +kernel

def row2473 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2892, 1), (key2902, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

theorem rowCheck2473 : row2473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2473 := by decide +kernel

theorem rowEval2473 (x : Key → ℝ) : Integer.Sparse.eval row2473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck2473, Integer.Sparse.eval_collectBalanced, rawRowCheck2473]

def rawRow2474 : Integer.Sparse Key := [(key2804, -2), (key2825, -2), (key2801, -2), (key2892, 1), (key2902, 1), (key2781, 1), (key2866, 1), (key2778, 1), (key2851, 1), (key2701, 2), (key2722, 2), (key2698, 2), (key2971, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2624, -1), (key2851, -1), (key2734, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2663, -1), (key2698, -1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1)]

theorem rawRowCheck2474 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form12 = rawRow2474 := by decide +kernel

def row2474 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

theorem rowCheck2474 : row2474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2474 := by decide +kernel

theorem rowEval2474 (x : Key → ℝ) : Integer.Sparse.eval row2474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2474, Integer.Sparse.eval_collectBalanced, rawRowCheck2474]

def rawRow2475 : Integer.Sparse Key := [(key2825, -2), (key2804, -2), (key2801, -2), (key2902, 1), (key2892, 1), (key2866, 1), (key2781, 1), (key2851, 1), (key2778, 1), (key2722, 2), (key2701, 2), (key2698, 2), (key2981, -1), (key2971, -1), (key2866, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2745, -1), (key2734, -1), (key2722, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1)]

theorem rawRowCheck2475 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form12 = rawRow2475 := by decide +kernel

def row2475 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -1), (key2663, -1), (key2666, -1), (key2698, 1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -2), (key2825, -1), (key2892, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -1), (key2981, -1)]

theorem rowCheck2475 : row2475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2475 := by decide +kernel

theorem rowEval2475 (x : Key → ℝ) : Integer.Sparse.eval row2475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck2475, Integer.Sparse.eval_collectBalanced, rawRowCheck2475]

def rawRow2476 : Integer.Sparse Key := [(key2175, -2), (key2175, -2), (key2189, -2), (key2175, 1), (key2179, 1), (key2175, 1), (key2189, 1), (key2179, 1), (key2189, 1), (key2275, 2), (key2275, 2), (key2289, 2), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2327, -1), (key2328, -1), (key2327, -1), (key2333, -1), (key2328, -1), (key2333, -1), (key2327, 1), (key2330, 1), (key2327, 1), (key2333, 1), (key2330, 1), (key2333, 1)]

theorem rawRowCheck2476 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form0 = rawRow2476 := by decide +kernel

def row2476 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

theorem rowCheck2476 : row2476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2476 := by decide +kernel

theorem rowEval2476 (x : Key → ℝ) : Integer.Sparse.eval row2476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck2476, Integer.Sparse.eval_collectBalanced, rawRowCheck2476]

def rawRow2477 : Integer.Sparse Key := [(key2175, -2), (key2189, -2), (key2175, -2), (key2179, 1), (key2175, 1), (key2189, 1), (key2175, 1), (key2189, 1), (key2179, 1), (key2275, 2), (key2289, 2), (key2275, 2), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2328, -1), (key2327, -1), (key2333, -1), (key2327, -1), (key2333, -1), (key2328, -1), (key2330, 1), (key2327, 1), (key2333, 1), (key2327, 1), (key2333, 1), (key2330, 1)]

theorem rawRowCheck2477 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form0 = rawRow2477 := by decide +kernel

def row2477 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

theorem rowCheck2477 : row2477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2477 := by decide +kernel

theorem rowEval2477 (x : Key → ℝ) : Integer.Sparse.eval row2477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2477, Integer.Sparse.eval_collectBalanced, rawRowCheck2477]

def rawRow2478 : Integer.Sparse Key := [(key2189, -2), (key2175, -2), (key2175, -2), (key2189, 1), (key2189, 1), (key2179, 1), (key2179, 1), (key2175, 1), (key2175, 1), (key2289, 2), (key2275, 2), (key2275, 2), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2333, -1), (key2333, -1), (key2328, -1), (key2328, -1), (key2327, -1), (key2327, -1), (key2333, 1), (key2333, 1), (key2330, 1), (key2330, 1), (key2327, 1), (key2327, 1)]

theorem rawRowCheck2478 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form0 = rawRow2478 := by decide +kernel

def row2478 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

theorem rowCheck2478 : row2478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2478 := by decide +kernel

theorem rowEval2478 (x : Key → ℝ) : Integer.Sparse.eval row2478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2478, Integer.Sparse.eval_collectBalanced, rawRowCheck2478]

def rawRow2479 : Integer.Sparse Key := [(key2179, -2), (key2179, -2), (key2179, -2), (key2175, 1), (key2175, 1), (key2175, 1), (key2175, 1), (key2175, 1), (key2175, 1), (key2281, 2), (key2281, 2), (key2281, 2), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1)]

theorem rawRowCheck2479 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow2479 := by decide +kernel

def row2479 : Integer.Sparse Key := [(key2175, 6), (key2179, -6), (key2275, -6), (key2281, 6), (key2328, 6), (key2330, -6)]

theorem rowCheck2479 : row2479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2479 := by decide +kernel

theorem rowEval2479 (x : Key → ℝ) : Integer.Sparse.eval row2479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2479, Integer.Sparse.eval_collectBalanced, rawRowCheck2479]

def rawRow2480 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2289, -2), (key2327, 1), (key2328, 1), (key2327, 1), (key2333, 1), (key2328, 1), (key2333, 1), (key2175, 2), (key2175, 2), (key2189, 2), (key2327, -1), (key2330, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2333, -1), (key2175, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2189, -1), (key2275, 1), (key2281, 1), (key2275, 1), (key2289, 1), (key2281, 1), (key2289, 1)]

theorem rawRowCheck2480 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form0 = rawRow2480 := by decide +kernel

def row2480 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

theorem rowCheck2480 : row2480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2480 := by decide +kernel

theorem rowEval2480 (x : Key → ℝ) : Integer.Sparse.eval row2480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck2480, Integer.Sparse.eval_collectBalanced, rawRowCheck2480]

def rawRow2481 : Integer.Sparse Key := [(key2275, -2), (key2289, -2), (key2275, -2), (key2328, 1), (key2327, 1), (key2333, 1), (key2327, 1), (key2333, 1), (key2328, 1), (key2175, 2), (key2189, 2), (key2175, 2), (key2330, -1), (key2327, -1), (key2333, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2281, 1), (key2275, 1), (key2289, 1), (key2275, 1), (key2289, 1), (key2281, 1)]

theorem rawRowCheck2481 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form0 = rawRow2481 := by decide +kernel

def row2481 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

theorem rowCheck2481 : row2481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2481 := by decide +kernel

theorem rowEval2481 (x : Key → ℝ) : Integer.Sparse.eval row2481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2481, Integer.Sparse.eval_collectBalanced, rawRowCheck2481]

def rawRow2482 : Integer.Sparse Key := [(key2289, -2), (key2275, -2), (key2275, -2), (key2333, 1), (key2333, 1), (key2328, 1), (key2328, 1), (key2327, 1), (key2327, 1), (key2189, 2), (key2175, 2), (key2175, 2), (key2333, -1), (key2333, -1), (key2330, -1), (key2330, -1), (key2327, -1), (key2327, -1), (key2189, -1), (key2189, -1), (key2179, -1), (key2179, -1), (key2175, -1), (key2175, -1), (key2289, 1), (key2289, 1), (key2281, 1), (key2281, 1), (key2275, 1), (key2275, 1)]

theorem rawRowCheck2482 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form0 = rawRow2482 := by decide +kernel

def row2482 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

theorem rowCheck2482 : row2482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2482 := by decide +kernel

theorem rowEval2482 (x : Key → ℝ) : Integer.Sparse.eval row2482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2482, Integer.Sparse.eval_collectBalanced, rawRowCheck2482]

def rawRow2483 : Integer.Sparse Key := [(key2082, -2), (key2328, -2), (key2328, -2), (key2078, 1), (key2078, 1), (key2275, 1), (key2275, 1), (key2327, 1), (key2327, 1), (key2087, 2), (key2330, 2), (key2330, 2), (key2078, -1), (key2078, -1), (key2175, -1), (key2175, -1), (key2327, -1), (key2327, -1), (key2087, -1), (key2087, -1), (key2281, -1), (key2281, -1), (key2330, -1), (key2330, -1), (key2082, 1), (key2082, 1), (key2179, 1), (key2179, 1), (key2328, 1), (key2328, 1)]

theorem rawRowCheck2483 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form0 = rawRow2483 := by decide +kernel

def row2483 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

theorem rowCheck2483 : row2483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2483 := by decide +kernel

theorem rowEval2483 (x : Key → ℝ) : Integer.Sparse.eval row2483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2483, Integer.Sparse.eval_collectBalanced, rawRowCheck2483]

def rawRow2484 : Integer.Sparse Key := [(key2328, -2), (key2082, -2), (key2328, -2), (key2275, 1), (key2327, 1), (key2078, 1), (key2327, 1), (key2078, 1), (key2275, 1), (key2330, 2), (key2087, 2), (key2330, 2), (key2175, -1), (key2327, -1), (key2078, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2281, -1), (key2330, -1), (key2087, -1), (key2330, -1), (key2087, -1), (key2281, -1), (key2179, 1), (key2328, 1), (key2082, 1), (key2328, 1), (key2082, 1), (key2179, 1)]

theorem rawRowCheck2484 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form0 = rawRow2484 := by decide +kernel

def row2484 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

theorem rowCheck2484 : row2484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2484 := by decide +kernel

theorem rowEval2484 (x : Key → ℝ) : Integer.Sparse.eval row2484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2484, Integer.Sparse.eval_collectBalanced, rawRowCheck2484]

def rawRow2485 : Integer.Sparse Key := [(key2328, -2), (key2328, -2), (key2082, -2), (key2327, 1), (key2275, 1), (key2327, 1), (key2078, 1), (key2275, 1), (key2078, 1), (key2330, 2), (key2330, 2), (key2087, 2), (key2327, -1), (key2175, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2078, -1), (key2330, -1), (key2281, -1), (key2330, -1), (key2087, -1), (key2281, -1), (key2087, -1), (key2328, 1), (key2179, 1), (key2328, 1), (key2082, 1), (key2179, 1), (key2082, 1)]

theorem rawRowCheck2485 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form0 = rawRow2485 := by decide +kernel

def row2485 : Integer.Sparse Key := [(key2175, -2), (key2179, 2), (key2275, 2), (key2281, -2), (key2328, -2), (key2330, 2)]

theorem rowCheck2485 : row2485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2485 := by decide +kernel

theorem rowEval2485 (x : Key → ℝ) : Integer.Sparse.eval row2485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2485, Integer.Sparse.eval_collectBalanced, rawRowCheck2485]

def rawRow2486 : Integer.Sparse Key := [(key2281, -2), (key2281, -2), (key2281, -2), (key2330, 1), (key2330, 1), (key2330, 1), (key2330, 1), (key2330, 1), (key2330, 1), (key2179, 2), (key2179, 2), (key2179, 2), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1)]

theorem rawRowCheck2486 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow2486 := by decide +kernel

def row2486 : Integer.Sparse Key := [(key2175, -6), (key2179, 6), (key2275, 6), (key2281, -6), (key2328, -6), (key2330, 6)]

theorem rowCheck2486 : row2486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2486 := by decide +kernel

theorem rowEval2486 (x : Key → ℝ) : Integer.Sparse.eval row2486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2486, Integer.Sparse.eval_collectBalanced, rawRowCheck2486]

def rawRow2487 : Integer.Sparse Key := [(key2087, -2), (key2330, -2), (key2330, -2), (key2087, 1), (key2087, 1), (key2281, 1), (key2281, 1), (key2330, 1), (key2330, 1), (key2082, 2), (key2328, 2), (key2328, 2), (key2082, -1), (key2082, -1), (key2179, -1), (key2179, -1), (key2328, -1), (key2328, -1), (key2078, -1), (key2078, -1), (key2275, -1), (key2275, -1), (key2327, -1), (key2327, -1), (key2078, 1), (key2078, 1), (key2175, 1), (key2175, 1), (key2327, 1), (key2327, 1)]

theorem rawRowCheck2487 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form0 = rawRow2487 := by decide +kernel

def row2487 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

theorem rowCheck2487 : row2487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2487 := by decide +kernel

theorem rowEval2487 (x : Key → ℝ) : Integer.Sparse.eval row2487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2487, Integer.Sparse.eval_collectBalanced, rawRowCheck2487]

def rawRow2488 : Integer.Sparse Key := [(key2330, -2), (key2087, -2), (key2330, -2), (key2281, 1), (key2330, 1), (key2087, 1), (key2330, 1), (key2087, 1), (key2281, 1), (key2328, 2), (key2082, 2), (key2328, 2), (key2179, -1), (key2328, -1), (key2082, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2275, -1), (key2327, -1), (key2078, -1), (key2327, -1), (key2078, -1), (key2275, -1), (key2175, 1), (key2327, 1), (key2078, 1), (key2327, 1), (key2078, 1), (key2175, 1)]

theorem rawRowCheck2488 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form0 = rawRow2488 := by decide +kernel

def row2488 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

theorem rowCheck2488 : row2488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2488 := by decide +kernel

theorem rowEval2488 (x : Key → ℝ) : Integer.Sparse.eval row2488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2488, Integer.Sparse.eval_collectBalanced, rawRowCheck2488]

def rawRow2489 : Integer.Sparse Key := [(key2330, -2), (key2330, -2), (key2087, -2), (key2330, 1), (key2281, 1), (key2330, 1), (key2087, 1), (key2281, 1), (key2087, 1), (key2328, 2), (key2328, 2), (key2082, 2), (key2328, -1), (key2179, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2082, -1), (key2327, -1), (key2275, -1), (key2327, -1), (key2078, -1), (key2275, -1), (key2078, -1), (key2327, 1), (key2175, 1), (key2327, 1), (key2078, 1), (key2175, 1), (key2078, 1)]

theorem rawRowCheck2489 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form0 = rawRow2489 := by decide +kernel

def row2489 : Integer.Sparse Key := [(key2175, 2), (key2179, -2), (key2275, -2), (key2281, 2), (key2328, 2), (key2330, -2)]

theorem rowCheck2489 : row2489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2489 := by decide +kernel

theorem rowEval2489 (x : Key → ℝ) : Integer.Sparse.eval row2489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2489, Integer.Sparse.eval_collectBalanced, rawRowCheck2489]

def rawRow2490 : Integer.Sparse Key := [(key754, -6), (key754, 2), (key754, 2), (key755, 2), (key843, 6), (key843, -2), (key843, -2), (key844, -2), (key943, -2), (key943, -2), (key944, -2), (key943, 2), (key943, 2), (key945, 2)]

theorem rawRowCheck2490 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form1 = rawRow2490 := by decide +kernel

def row2490 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

theorem rowCheck2490 : row2490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2490 := by decide +kernel

theorem rowEval2490 (x : Key → ℝ) : Integer.Sparse.eval row2490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2490, Integer.Sparse.eval_collectBalanced, rawRowCheck2490]

def rawRow2491 : Integer.Sparse Key := [(key754, -6), (key754, 2), (key755, 2), (key754, 2), (key843, 6), (key843, -2), (key844, -2), (key843, -2), (key943, -2), (key944, -2), (key943, -2), (key943, 2), (key945, 2), (key943, 2)]

theorem rawRowCheck2491 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form1 = rawRow2491 := by decide +kernel

def row2491 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

theorem rowCheck2491 : row2491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2491 := by decide +kernel

theorem rowEval2491 (x : Key → ℝ) : Integer.Sparse.eval row2491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2491, Integer.Sparse.eval_collectBalanced, rawRowCheck2491]

def rawRow2492 : Integer.Sparse Key := [(key754, -6), (key755, 2), (key754, 2), (key754, 2), (key843, 6), (key844, -2), (key843, -2), (key843, -2), (key944, -2), (key943, -2), (key943, -2), (key945, 2), (key943, 2), (key943, 2)]

theorem rawRowCheck2492 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form1 = rawRow2492 := by decide +kernel

def row2492 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

theorem rowCheck2492 : row2492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2492 := by decide +kernel

theorem rowEval2492 (x : Key → ℝ) : Integer.Sparse.eval row2492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2492, Integer.Sparse.eval_collectBalanced, rawRowCheck2492]

def rawRow2493 : Integer.Sparse Key := [(key755, -6), (key754, 2), (key754, 2), (key754, 2), (key844, 6), (key843, -2), (key843, -2), (key843, -2), (key945, -2), (key945, -2), (key945, -2), (key944, 2), (key944, 2), (key944, 2)]

theorem rawRowCheck2493 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow2493 := by decide +kernel

def row2493 : Integer.Sparse Key := [(key754, 6), (key755, -6), (key843, -6), (key844, 6), (key944, 6), (key945, -6)]

theorem rowCheck2493 : row2493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2493 := by decide +kernel

theorem rowEval2493 (x : Key → ℝ) : Integer.Sparse.eval row2493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2493, Integer.Sparse.eval_collectBalanced, rawRowCheck2493]

def rawRow2494 : Integer.Sparse Key := [(key843, -6), (key943, 2), (key943, 2), (key944, 2), (key754, 6), (key943, -2), (key943, -2), (key945, -2), (key754, -2), (key754, -2), (key755, -2), (key843, 2), (key843, 2), (key844, 2)]

theorem rawRowCheck2494 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form1 = rawRow2494 := by decide +kernel

def row2494 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

theorem rowCheck2494 : row2494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2494 := by decide +kernel

theorem rowEval2494 (x : Key → ℝ) : Integer.Sparse.eval row2494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2494, Integer.Sparse.eval_collectBalanced, rawRowCheck2494]

def rawRow2495 : Integer.Sparse Key := [(key843, -6), (key943, 2), (key944, 2), (key943, 2), (key754, 6), (key943, -2), (key945, -2), (key943, -2), (key754, -2), (key755, -2), (key754, -2), (key843, 2), (key844, 2), (key843, 2)]

theorem rawRowCheck2495 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form1 = rawRow2495 := by decide +kernel

def row2495 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

theorem rowCheck2495 : row2495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2495 := by decide +kernel

theorem rowEval2495 (x : Key → ℝ) : Integer.Sparse.eval row2495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2495, Integer.Sparse.eval_collectBalanced, rawRowCheck2495]

def rawRow2496 : Integer.Sparse Key := [(key843, -6), (key944, 2), (key943, 2), (key943, 2), (key754, 6), (key945, -2), (key943, -2), (key943, -2), (key755, -2), (key754, -2), (key754, -2), (key844, 2), (key843, 2), (key843, 2)]

theorem rawRowCheck2496 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form1 = rawRow2496 := by decide +kernel

def row2496 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

theorem rowCheck2496 : row2496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2496 := by decide +kernel

theorem rowEval2496 (x : Key → ℝ) : Integer.Sparse.eval row2496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2496, Integer.Sparse.eval_collectBalanced, rawRowCheck2496]

def rawRow2497 : Integer.Sparse Key := [(key944, -6), (key843, 2), (key943, 2), (key943, 2), (key945, 6), (key754, -2), (key943, -2), (key943, -2), (key844, -2), (key945, -2), (key945, -2), (key755, 2), (key944, 2), (key944, 2)]

theorem rawRowCheck2497 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form1 = rawRow2497 := by decide +kernel

def row2497 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

theorem rowCheck2497 : row2497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2497 := by decide +kernel

theorem rowEval2497 (x : Key → ℝ) : Integer.Sparse.eval row2497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2497, Integer.Sparse.eval_collectBalanced, rawRowCheck2497]

def rawRow2498 : Integer.Sparse Key := [(key944, -6), (key943, 2), (key843, 2), (key943, 2), (key945, 6), (key943, -2), (key754, -2), (key943, -2), (key945, -2), (key844, -2), (key945, -2), (key944, 2), (key755, 2), (key944, 2)]

theorem rawRowCheck2498 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form1 = rawRow2498 := by decide +kernel

def row2498 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

theorem rowCheck2498 : row2498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2498 := by decide +kernel

theorem rowEval2498 (x : Key → ℝ) : Integer.Sparse.eval row2498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2498, Integer.Sparse.eval_collectBalanced, rawRowCheck2498]

def rawRow2499 : Integer.Sparse Key := [(key944, -6), (key943, 2), (key943, 2), (key843, 2), (key945, 6), (key943, -2), (key943, -2), (key754, -2), (key945, -2), (key945, -2), (key844, -2), (key944, 2), (key944, 2), (key755, 2)]

theorem rawRowCheck2499 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form1 = rawRow2499 := by decide +kernel

def row2499 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 2), (key844, -2), (key944, -2), (key945, 2)]

theorem rowCheck2499 : row2499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2499 := by decide +kernel

theorem rowEval2499 (x : Key → ℝ) : Integer.Sparse.eval row2499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2499, Integer.Sparse.eval_collectBalanced, rawRowCheck2499]

def rawRow2500 : Integer.Sparse Key := [(key844, -6), (key945, 2), (key945, 2), (key945, 2), (key755, 6), (key944, -2), (key944, -2), (key944, -2), (key754, -2), (key754, -2), (key754, -2), (key843, 2), (key843, 2), (key843, 2)]

theorem rawRowCheck2500 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow2500 := by decide +kernel

def row2500 : Integer.Sparse Key := [(key754, -6), (key755, 6), (key843, 6), (key844, -6), (key944, -6), (key945, 6)]

theorem rowCheck2500 : row2500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2500 := by decide +kernel

theorem rowEval2500 (x : Key → ℝ) : Integer.Sparse.eval row2500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2500, Integer.Sparse.eval_collectBalanced, rawRowCheck2500]

def rawRow2501 : Integer.Sparse Key := [(key945, -6), (key844, 2), (key945, 2), (key945, 2), (key944, 6), (key755, -2), (key944, -2), (key944, -2), (key843, -2), (key943, -2), (key943, -2), (key754, 2), (key943, 2), (key943, 2)]

theorem rawRowCheck2501 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form1 = rawRow2501 := by decide +kernel

def row2501 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

theorem rowCheck2501 : row2501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2501 := by decide +kernel

theorem rowEval2501 (x : Key → ℝ) : Integer.Sparse.eval row2501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2501, Integer.Sparse.eval_collectBalanced, rawRowCheck2501]

def rawRow2502 : Integer.Sparse Key := [(key945, -6), (key945, 2), (key844, 2), (key945, 2), (key944, 6), (key944, -2), (key755, -2), (key944, -2), (key943, -2), (key843, -2), (key943, -2), (key943, 2), (key754, 2), (key943, 2)]

theorem rawRowCheck2502 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form1 = rawRow2502 := by decide +kernel

def row2502 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

theorem rowCheck2502 : row2502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2502 := by decide +kernel

theorem rowEval2502 (x : Key → ℝ) : Integer.Sparse.eval row2502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2502, Integer.Sparse.eval_collectBalanced, rawRowCheck2502]

def rawRow2503 : Integer.Sparse Key := [(key945, -6), (key945, 2), (key945, 2), (key844, 2), (key944, 6), (key944, -2), (key944, -2), (key755, -2), (key943, -2), (key943, -2), (key843, -2), (key943, 2), (key943, 2), (key754, 2)]

theorem rawRowCheck2503 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form1 = rawRow2503 := by decide +kernel

def row2503 : Integer.Sparse Key := [(key754, 2), (key755, -2), (key843, -2), (key844, 2), (key944, 2), (key945, -2)]

theorem rowCheck2503 : row2503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2503 := by decide +kernel

theorem rowEval2503 (x : Key → ℝ) : Integer.Sparse.eval row2503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2503, Integer.Sparse.eval_collectBalanced, rawRowCheck2503]

def rawRow2504 : Integer.Sparse Key := [(key2077, -2), (key2079, -2), (key2079, -2), (key2077, 1), (key2079, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2085, 1), (key2174, 2), (key2176, 2), (key2176, 2), (key2174, -1), (key2176, -1), (key2174, -1), (key2187, -1), (key2176, -1), (key2187, -1), (key2274, -1), (key2276, -1), (key2274, -1), (key2279, -1), (key2276, -1), (key2279, -1), (key2274, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2287, 1)]

theorem rawRowCheck2504 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form2 = rawRow2504 := by decide +kernel

def row2504 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

theorem rowCheck2504 : row2504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2504 := by decide +kernel

theorem rowEval2504 (x : Key → ℝ) : Integer.Sparse.eval row2504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck2504, Integer.Sparse.eval_collectBalanced, rawRowCheck2504]

def rawRow2505 : Integer.Sparse Key := [(key2079, -2), (key2077, -2), (key2079, -2), (key2079, 1), (key2077, 1), (key2085, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2176, 2), (key2174, 2), (key2176, 2), (key2176, -1), (key2174, -1), (key2187, -1), (key2174, -1), (key2187, -1), (key2176, -1), (key2276, -1), (key2274, -1), (key2279, -1), (key2274, -1), (key2279, -1), (key2276, -1), (key2276, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2276, 1)]

theorem rawRowCheck2505 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form2 = rawRow2505 := by decide +kernel

def row2505 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

theorem rowCheck2505 : row2505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2505 := by decide +kernel

theorem rowEval2505 (x : Key → ℝ) : Integer.Sparse.eval row2505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2505, Integer.Sparse.eval_collectBalanced, rawRowCheck2505]

def rawRow2506 : Integer.Sparse Key := [(key2079, -2), (key2079, -2), (key2077, -2), (key2085, 1), (key2085, 1), (key2079, 1), (key2079, 1), (key2077, 1), (key2077, 1), (key2176, 2), (key2176, 2), (key2174, 2), (key2187, -1), (key2187, -1), (key2176, -1), (key2176, -1), (key2174, -1), (key2174, -1), (key2279, -1), (key2279, -1), (key2276, -1), (key2276, -1), (key2274, -1), (key2274, -1), (key2287, 1), (key2287, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1)]

theorem rawRowCheck2506 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form2 = rawRow2506 := by decide +kernel

def row2506 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

theorem rowCheck2506 : row2506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2506 := by decide +kernel

theorem rowEval2506 (x : Key → ℝ) : Integer.Sparse.eval row2506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2506, Integer.Sparse.eval_collectBalanced, rawRowCheck2506]

def rawRow2507 : Integer.Sparse Key := [(key2085, -2), (key2085, -2), (key2085, -2), (key2079, 1), (key2079, 1), (key2079, 1), (key2079, 1), (key2079, 1), (key2079, 1), (key2187, 2), (key2187, 2), (key2187, 2), (key2176, -1), (key2176, -1), (key2176, -1), (key2176, -1), (key2176, -1), (key2176, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1)]

theorem rawRowCheck2507 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow2507 := by decide +kernel

def row2507 : Integer.Sparse Key := [(key2079, 6), (key2085, -6), (key2176, -6), (key2187, 6), (key2279, 6), (key2287, -6)]

theorem rowCheck2507 : row2507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2507 := by decide +kernel

theorem rowEval2507 (x : Key → ℝ) : Integer.Sparse.eval row2507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2507, Integer.Sparse.eval_collectBalanced, rawRowCheck2507]

def rawRow2508 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2176, -2), (key2274, 1), (key2276, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2279, 1), (key2077, 2), (key2079, 2), (key2079, 2), (key2274, -1), (key2276, -1), (key2274, -1), (key2287, -1), (key2276, -1), (key2287, -1), (key2077, -1), (key2079, -1), (key2077, -1), (key2085, -1), (key2079, -1), (key2085, -1), (key2174, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2187, 1)]

theorem rawRowCheck2508 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form2 = rawRow2508 := by decide +kernel

def row2508 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

theorem rowCheck2508 : row2508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2508 := by decide +kernel

theorem rowEval2508 (x : Key → ℝ) : Integer.Sparse.eval row2508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck2508, Integer.Sparse.eval_collectBalanced, rawRowCheck2508]

def rawRow2509 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2176, -2), (key2276, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2079, 2), (key2077, 2), (key2079, 2), (key2276, -1), (key2274, -1), (key2287, -1), (key2274, -1), (key2287, -1), (key2276, -1), (key2079, -1), (key2077, -1), (key2085, -1), (key2077, -1), (key2085, -1), (key2079, -1), (key2176, 1), (key2174, 1), (key2187, 1), (key2174, 1), (key2187, 1), (key2176, 1)]

theorem rawRowCheck2509 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form2 = rawRow2509 := by decide +kernel

def row2509 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

theorem rowCheck2509 : row2509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2509 := by decide +kernel

theorem rowEval2509 (x : Key → ℝ) : Integer.Sparse.eval row2509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2509, Integer.Sparse.eval_collectBalanced, rawRowCheck2509]

def rawRow2510 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2174, -2), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2079, 2), (key2079, 2), (key2077, 2), (key2287, -1), (key2287, -1), (key2276, -1), (key2276, -1), (key2274, -1), (key2274, -1), (key2085, -1), (key2085, -1), (key2079, -1), (key2079, -1), (key2077, -1), (key2077, -1), (key2187, 1), (key2187, 1), (key2176, 1), (key2176, 1), (key2174, 1), (key2174, 1)]

theorem rawRowCheck2510 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form2 = rawRow2510 := by decide +kernel

def row2510 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

theorem rowCheck2510 : row2510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2510 := by decide +kernel

theorem rowEval2510 (x : Key → ℝ) : Integer.Sparse.eval row2510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2510, Integer.Sparse.eval_collectBalanced, rawRowCheck2510]

def rawRow2511 : Integer.Sparse Key := [(key2279, -2), (key2279, -2), (key2343, -2), (key2176, 1), (key2176, 1), (key2276, 1), (key2276, 1), (key2341, 1), (key2341, 1), (key2287, 2), (key2287, 2), (key2347, 2), (key2079, -1), (key2079, -1), (key2276, -1), (key2276, -1), (key2341, -1), (key2341, -1), (key2187, -1), (key2187, -1), (key2287, -1), (key2287, -1), (key2347, -1), (key2347, -1), (key2085, 1), (key2085, 1), (key2279, 1), (key2279, 1), (key2343, 1), (key2343, 1)]

theorem rawRowCheck2511 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form2 = rawRow2511 := by decide +kernel

def row2511 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

theorem rowCheck2511 : row2511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2511 := by decide +kernel

theorem rowEval2511 (x : Key → ℝ) : Integer.Sparse.eval row2511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2511, Integer.Sparse.eval_collectBalanced, rawRowCheck2511]

def rawRow2512 : Integer.Sparse Key := [(key2279, -2), (key2343, -2), (key2279, -2), (key2276, 1), (key2341, 1), (key2176, 1), (key2341, 1), (key2176, 1), (key2276, 1), (key2287, 2), (key2347, 2), (key2287, 2), (key2276, -1), (key2341, -1), (key2079, -1), (key2341, -1), (key2079, -1), (key2276, -1), (key2287, -1), (key2347, -1), (key2187, -1), (key2347, -1), (key2187, -1), (key2287, -1), (key2279, 1), (key2343, 1), (key2085, 1), (key2343, 1), (key2085, 1), (key2279, 1)]

theorem rawRowCheck2512 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form2 = rawRow2512 := by decide +kernel

def row2512 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

theorem rowCheck2512 : row2512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2512 := by decide +kernel

theorem rowEval2512 (x : Key → ℝ) : Integer.Sparse.eval row2512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2512, Integer.Sparse.eval_collectBalanced, rawRowCheck2512]

def rawRow2513 : Integer.Sparse Key := [(key2343, -2), (key2279, -2), (key2279, -2), (key2341, 1), (key2276, 1), (key2341, 1), (key2176, 1), (key2276, 1), (key2176, 1), (key2347, 2), (key2287, 2), (key2287, 2), (key2341, -1), (key2276, -1), (key2341, -1), (key2079, -1), (key2276, -1), (key2079, -1), (key2347, -1), (key2287, -1), (key2347, -1), (key2187, -1), (key2287, -1), (key2187, -1), (key2343, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2085, 1)]

theorem rawRowCheck2513 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form2 = rawRow2513 := by decide +kernel

def row2513 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2176, 2), (key2187, -2), (key2279, -2), (key2287, 2)]

theorem rowCheck2513 : row2513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2513 := by decide +kernel

theorem rowEval2513 (x : Key → ℝ) : Integer.Sparse.eval row2513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2513, Integer.Sparse.eval_collectBalanced, rawRowCheck2513]

def rawRow2514 : Integer.Sparse Key := [(key2187, -2), (key2187, -2), (key2187, -2), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2085, 2), (key2085, 2), (key2085, 2), (key2279, -1), (key2279, -1), (key2279, -1), (key2279, -1), (key2279, -1), (key2279, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2176, 1), (key2176, 1), (key2176, 1), (key2176, 1), (key2176, 1), (key2176, 1)]

theorem rawRowCheck2514 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow2514 := by decide +kernel

def row2514 : Integer.Sparse Key := [(key2079, -6), (key2085, 6), (key2176, 6), (key2187, -6), (key2279, -6), (key2287, 6)]

theorem rowCheck2514 : row2514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2514 := by decide +kernel

theorem rowEval2514 (x : Key → ℝ) : Integer.Sparse.eval row2514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2514, Integer.Sparse.eval_collectBalanced, rawRowCheck2514]

def rawRow2515 : Integer.Sparse Key := [(key2287, -2), (key2287, -2), (key2347, -2), (key2187, 1), (key2187, 1), (key2287, 1), (key2287, 1), (key2347, 1), (key2347, 1), (key2279, 2), (key2279, 2), (key2343, 2), (key2085, -1), (key2085, -1), (key2279, -1), (key2279, -1), (key2343, -1), (key2343, -1), (key2176, -1), (key2176, -1), (key2276, -1), (key2276, -1), (key2341, -1), (key2341, -1), (key2079, 1), (key2079, 1), (key2276, 1), (key2276, 1), (key2341, 1), (key2341, 1)]

theorem rawRowCheck2515 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form2 = rawRow2515 := by decide +kernel

def row2515 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

theorem rowCheck2515 : row2515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2515 := by decide +kernel

theorem rowEval2515 (x : Key → ℝ) : Integer.Sparse.eval row2515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2515, Integer.Sparse.eval_collectBalanced, rawRowCheck2515]

def rawRow2516 : Integer.Sparse Key := [(key2287, -2), (key2347, -2), (key2287, -2), (key2287, 1), (key2347, 1), (key2187, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2279, 2), (key2343, 2), (key2279, 2), (key2279, -1), (key2343, -1), (key2085, -1), (key2343, -1), (key2085, -1), (key2279, -1), (key2276, -1), (key2341, -1), (key2176, -1), (key2341, -1), (key2176, -1), (key2276, -1), (key2276, 1), (key2341, 1), (key2079, 1), (key2341, 1), (key2079, 1), (key2276, 1)]

theorem rawRowCheck2516 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form2 = rawRow2516 := by decide +kernel

def row2516 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

theorem rowCheck2516 : row2516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2516 := by decide +kernel

theorem rowEval2516 (x : Key → ℝ) : Integer.Sparse.eval row2516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2516, Integer.Sparse.eval_collectBalanced, rawRowCheck2516]

def rawRow2517 : Integer.Sparse Key := [(key2347, -2), (key2287, -2), (key2287, -2), (key2347, 1), (key2287, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2187, 1), (key2343, 2), (key2279, 2), (key2279, 2), (key2343, -1), (key2279, -1), (key2343, -1), (key2085, -1), (key2279, -1), (key2085, -1), (key2341, -1), (key2276, -1), (key2341, -1), (key2176, -1), (key2276, -1), (key2176, -1), (key2341, 1), (key2276, 1), (key2341, 1), (key2079, 1), (key2276, 1), (key2079, 1)]

theorem rawRowCheck2517 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form2 = rawRow2517 := by decide +kernel

def row2517 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2176, -2), (key2187, 2), (key2279, 2), (key2287, -2)]

theorem rowCheck2517 : row2517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2517 := by decide +kernel

theorem rowEval2517 (x : Key → ℝ) : Integer.Sparse.eval row2517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2517, Integer.Sparse.eval_collectBalanced, rawRowCheck2517]

def rawRow2518 : Integer.Sparse Key := [(key713, -2), (key715, -2), (key715, -2), (key715, 6), (key890, 2), (key892, 2), (key892, 2), (key892, -2), (key892, -2), (key914, -2), (key959, -6), (key959, 2), (key959, 2), (key966, 2)]

theorem rawRowCheck2518 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form3 = rawRow2518 := by decide +kernel

def row2518 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

theorem rowCheck2518 : row2518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2518 := by decide +kernel

theorem rowEval2518 (x : Key → ℝ) : Integer.Sparse.eval row2518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2518, Integer.Sparse.eval_collectBalanced, rawRowCheck2518]

def rawRow2519 : Integer.Sparse Key := [(key715, -2), (key713, -2), (key715, -2), (key715, 6), (key892, 2), (key890, 2), (key892, 2), (key892, -2), (key914, -2), (key892, -2), (key959, -6), (key959, 2), (key966, 2), (key959, 2)]

theorem rawRowCheck2519 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form3 = rawRow2519 := by decide +kernel

def row2519 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

theorem rowCheck2519 : row2519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2519 := by decide +kernel

theorem rowEval2519 (x : Key → ℝ) : Integer.Sparse.eval row2519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2519, Integer.Sparse.eval_collectBalanced, rawRowCheck2519]

def rawRow2520 : Integer.Sparse Key := [(key715, -2), (key715, -2), (key713, -2), (key715, 6), (key892, 2), (key892, 2), (key890, 2), (key914, -2), (key892, -2), (key892, -2), (key959, -6), (key966, 2), (key959, 2), (key959, 2)]

theorem rawRowCheck2520 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form3 = rawRow2520 := by decide +kernel

def row2520 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

theorem rowCheck2520 : row2520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2520 := by decide +kernel

theorem rowEval2520 (x : Key → ℝ) : Integer.Sparse.eval row2520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2520, Integer.Sparse.eval_collectBalanced, rawRowCheck2520]

def rawRow2521 : Integer.Sparse Key := [(key715, -2), (key715, -2), (key715, -2), (key713, 6), (key914, 2), (key914, 2), (key914, 2), (key890, -2), (key890, -2), (key890, -2), (key966, -6), (key959, 2), (key959, 2), (key959, 2)]

theorem rawRowCheck2521 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow2521 := by decide +kernel

def row2521 : Integer.Sparse Key := [(key713, 6), (key715, -6), (key890, -6), (key914, 6), (key959, 6), (key966, -6)]

theorem rowCheck2521 : row2521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2521 := by decide +kernel

theorem rowEval2521 (x : Key → ℝ) : Integer.Sparse.eval row2521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2521, Integer.Sparse.eval_collectBalanced, rawRowCheck2521]

def rawRow2522 : Integer.Sparse Key := [(key890, -2), (key892, -2), (key892, -2), (key959, 6), (key713, 2), (key715, 2), (key715, 2), (key959, -2), (key959, -2), (key966, -2), (key715, -6), (key892, 2), (key892, 2), (key914, 2)]

theorem rawRowCheck2522 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form3 = rawRow2522 := by decide +kernel

def row2522 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

theorem rowCheck2522 : row2522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2522 := by decide +kernel

theorem rowEval2522 (x : Key → ℝ) : Integer.Sparse.eval row2522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2522, Integer.Sparse.eval_collectBalanced, rawRowCheck2522]

def rawRow2523 : Integer.Sparse Key := [(key892, -2), (key890, -2), (key892, -2), (key959, 6), (key715, 2), (key713, 2), (key715, 2), (key959, -2), (key966, -2), (key959, -2), (key715, -6), (key892, 2), (key914, 2), (key892, 2)]

theorem rawRowCheck2523 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form3 = rawRow2523 := by decide +kernel

def row2523 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

theorem rowCheck2523 : row2523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2523 := by decide +kernel

theorem rowEval2523 (x : Key → ℝ) : Integer.Sparse.eval row2523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2523, Integer.Sparse.eval_collectBalanced, rawRowCheck2523]

def rawRow2524 : Integer.Sparse Key := [(key892, -2), (key892, -2), (key890, -2), (key959, 6), (key715, 2), (key715, 2), (key713, 2), (key966, -2), (key959, -2), (key959, -2), (key715, -6), (key914, 2), (key892, 2), (key892, 2)]

theorem rawRowCheck2524 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form3 = rawRow2524 := by decide +kernel

def row2524 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

theorem rowCheck2524 : row2524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2524 := by decide +kernel

theorem rowEval2524 (x : Key → ℝ) : Integer.Sparse.eval row2524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2524, Integer.Sparse.eval_collectBalanced, rawRowCheck2524]

def rawRow2525 : Integer.Sparse Key := [(key892, -2), (key892, -2), (key959, -2), (key890, 6), (key914, 2), (key914, 2), (key966, 2), (key713, -2), (key890, -2), (key890, -2), (key914, -6), (key715, 2), (key892, 2), (key892, 2)]

theorem rawRowCheck2525 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form3 = rawRow2525 := by decide +kernel

def row2525 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

theorem rowCheck2525 : row2525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2525 := by decide +kernel

theorem rowEval2525 (x : Key → ℝ) : Integer.Sparse.eval row2525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2525, Integer.Sparse.eval_collectBalanced, rawRowCheck2525]

def rawRow2526 : Integer.Sparse Key := [(key892, -2), (key959, -2), (key892, -2), (key890, 6), (key914, 2), (key966, 2), (key914, 2), (key890, -2), (key713, -2), (key890, -2), (key914, -6), (key892, 2), (key715, 2), (key892, 2)]

theorem rawRowCheck2526 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form3 = rawRow2526 := by decide +kernel

def row2526 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

theorem rowCheck2526 : row2526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2526 := by decide +kernel

theorem rowEval2526 (x : Key → ℝ) : Integer.Sparse.eval row2526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2526, Integer.Sparse.eval_collectBalanced, rawRowCheck2526]

def rawRow2527 : Integer.Sparse Key := [(key959, -2), (key892, -2), (key892, -2), (key890, 6), (key966, 2), (key914, 2), (key914, 2), (key890, -2), (key890, -2), (key713, -2), (key914, -6), (key892, 2), (key892, 2), (key715, 2)]

theorem rawRowCheck2527 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form3 = rawRow2527 := by decide +kernel

def row2527 : Integer.Sparse Key := [(key713, -2), (key715, 2), (key890, 2), (key914, -2), (key959, -2), (key966, 2)]

theorem rowCheck2527 : row2527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2527 := by decide +kernel

theorem rowEval2527 (x : Key → ℝ) : Integer.Sparse.eval row2527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2527, Integer.Sparse.eval_collectBalanced, rawRowCheck2527]

def rawRow2528 : Integer.Sparse Key := [(key914, -2), (key914, -2), (key914, -2), (key966, 6), (key715, 2), (key715, 2), (key715, 2), (key959, -2), (key959, -2), (key959, -2), (key713, -6), (key890, 2), (key890, 2), (key890, 2)]

theorem rawRowCheck2528 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow2528 := by decide +kernel

def row2528 : Integer.Sparse Key := [(key713, -6), (key715, 6), (key890, 6), (key914, -6), (key959, -6), (key966, 6)]

theorem rowCheck2528 : row2528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2528 := by decide +kernel

theorem rowEval2528 (x : Key → ℝ) : Integer.Sparse.eval row2528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2528, Integer.Sparse.eval_collectBalanced, rawRowCheck2528]

def rawRow2529 : Integer.Sparse Key := [(key914, -2), (key914, -2), (key966, -2), (key914, 6), (key892, 2), (key892, 2), (key959, 2), (key715, -2), (key892, -2), (key892, -2), (key890, -6), (key713, 2), (key890, 2), (key890, 2)]

theorem rawRowCheck2529 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form3 = rawRow2529 := by decide +kernel

def row2529 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

theorem rowCheck2529 : row2529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2529 := by decide +kernel

theorem rowEval2529 (x : Key → ℝ) : Integer.Sparse.eval row2529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2529, Integer.Sparse.eval_collectBalanced, rawRowCheck2529]

def rawRow2530 : Integer.Sparse Key := [(key914, -2), (key966, -2), (key914, -2), (key914, 6), (key892, 2), (key959, 2), (key892, 2), (key892, -2), (key715, -2), (key892, -2), (key890, -6), (key890, 2), (key713, 2), (key890, 2)]

theorem rawRowCheck2530 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form3 = rawRow2530 := by decide +kernel

def row2530 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

theorem rowCheck2530 : row2530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2530 := by decide +kernel

theorem rowEval2530 (x : Key → ℝ) : Integer.Sparse.eval row2530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2530, Integer.Sparse.eval_collectBalanced, rawRowCheck2530]

def rawRow2531 : Integer.Sparse Key := [(key966, -2), (key914, -2), (key914, -2), (key914, 6), (key959, 2), (key892, 2), (key892, 2), (key892, -2), (key892, -2), (key715, -2), (key890, -6), (key890, 2), (key890, 2), (key713, 2)]

theorem rawRowCheck2531 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form3 = rawRow2531 := by decide +kernel

def row2531 : Integer.Sparse Key := [(key713, 2), (key715, -2), (key890, -2), (key914, 2), (key959, 2), (key966, -2)]

theorem rowCheck2531 : row2531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2531 := by decide +kernel

theorem rowEval2531 (x : Key → ℝ) : Integer.Sparse.eval row2531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2531, Integer.Sparse.eval_collectBalanced, rawRowCheck2531]

def rawRow2532 : Integer.Sparse Key := [(key2098, -6), (key2098, 2), (key2098, 2), (key2099, 2), (key2203, 6), (key2203, -2), (key2203, -2), (key2206, -2), (key2317, -2), (key2317, -2), (key2318, -2), (key2317, 2), (key2317, 2), (key2321, 2)]

theorem rawRowCheck2532 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form4 = rawRow2532 := by decide +kernel

def row2532 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

theorem rowCheck2532 : row2532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2532 := by decide +kernel

theorem rowEval2532 (x : Key → ℝ) : Integer.Sparse.eval row2532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2532, Integer.Sparse.eval_collectBalanced, rawRowCheck2532]

def rawRow2533 : Integer.Sparse Key := [(key2098, -6), (key2098, 2), (key2099, 2), (key2098, 2), (key2203, 6), (key2203, -2), (key2206, -2), (key2203, -2), (key2317, -2), (key2318, -2), (key2317, -2), (key2317, 2), (key2321, 2), (key2317, 2)]

theorem rawRowCheck2533 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form4 = rawRow2533 := by decide +kernel

def row2533 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

theorem rowCheck2533 : row2533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2533 := by decide +kernel

theorem rowEval2533 (x : Key → ℝ) : Integer.Sparse.eval row2533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2533, Integer.Sparse.eval_collectBalanced, rawRowCheck2533]

def rawRow2534 : Integer.Sparse Key := [(key2098, -6), (key2099, 2), (key2098, 2), (key2098, 2), (key2203, 6), (key2206, -2), (key2203, -2), (key2203, -2), (key2318, -2), (key2317, -2), (key2317, -2), (key2321, 2), (key2317, 2), (key2317, 2)]

theorem rawRowCheck2534 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form4 = rawRow2534 := by decide +kernel

def row2534 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

theorem rowCheck2534 : row2534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2534 := by decide +kernel

theorem rowEval2534 (x : Key → ℝ) : Integer.Sparse.eval row2534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2534, Integer.Sparse.eval_collectBalanced, rawRowCheck2534]

def rawRow2535 : Integer.Sparse Key := [(key2099, -6), (key2098, 2), (key2098, 2), (key2098, 2), (key2206, 6), (key2203, -2), (key2203, -2), (key2203, -2), (key2321, -2), (key2321, -2), (key2321, -2), (key2318, 2), (key2318, 2), (key2318, 2)]

theorem rawRowCheck2535 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow2535 := by decide +kernel

def row2535 : Integer.Sparse Key := [(key2098, 6), (key2099, -6), (key2203, -6), (key2206, 6), (key2318, 6), (key2321, -6)]

theorem rowCheck2535 : row2535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2535 := by decide +kernel

theorem rowEval2535 (x : Key → ℝ) : Integer.Sparse.eval row2535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2535, Integer.Sparse.eval_collectBalanced, rawRowCheck2535]

def rawRow2536 : Integer.Sparse Key := [(key2203, -6), (key2317, 2), (key2317, 2), (key2318, 2), (key2098, 6), (key2317, -2), (key2317, -2), (key2321, -2), (key2098, -2), (key2098, -2), (key2099, -2), (key2203, 2), (key2203, 2), (key2206, 2)]

theorem rawRowCheck2536 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form4 = rawRow2536 := by decide +kernel

def row2536 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

theorem rowCheck2536 : row2536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2536 := by decide +kernel

theorem rowEval2536 (x : Key → ℝ) : Integer.Sparse.eval row2536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2536, Integer.Sparse.eval_collectBalanced, rawRowCheck2536]

def rawRow2537 : Integer.Sparse Key := [(key2203, -6), (key2317, 2), (key2318, 2), (key2317, 2), (key2098, 6), (key2317, -2), (key2321, -2), (key2317, -2), (key2098, -2), (key2099, -2), (key2098, -2), (key2203, 2), (key2206, 2), (key2203, 2)]

theorem rawRowCheck2537 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form4 = rawRow2537 := by decide +kernel

def row2537 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

theorem rowCheck2537 : row2537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2537 := by decide +kernel

theorem rowEval2537 (x : Key → ℝ) : Integer.Sparse.eval row2537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2537, Integer.Sparse.eval_collectBalanced, rawRowCheck2537]

def rawRow2538 : Integer.Sparse Key := [(key2203, -6), (key2318, 2), (key2317, 2), (key2317, 2), (key2098, 6), (key2321, -2), (key2317, -2), (key2317, -2), (key2099, -2), (key2098, -2), (key2098, -2), (key2206, 2), (key2203, 2), (key2203, 2)]

theorem rawRowCheck2538 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form4 = rawRow2538 := by decide +kernel

def row2538 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

theorem rowCheck2538 : row2538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2538 := by decide +kernel

theorem rowEval2538 (x : Key → ℝ) : Integer.Sparse.eval row2538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2538, Integer.Sparse.eval_collectBalanced, rawRowCheck2538]

def rawRow2539 : Integer.Sparse Key := [(key2318, -6), (key2203, 2), (key2317, 2), (key2317, 2), (key2321, 6), (key2098, -2), (key2317, -2), (key2317, -2), (key2206, -2), (key2321, -2), (key2321, -2), (key2099, 2), (key2318, 2), (key2318, 2)]

theorem rawRowCheck2539 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form4 = rawRow2539 := by decide +kernel

def row2539 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

theorem rowCheck2539 : row2539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2539 := by decide +kernel

theorem rowEval2539 (x : Key → ℝ) : Integer.Sparse.eval row2539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2539, Integer.Sparse.eval_collectBalanced, rawRowCheck2539]

def rawRow2540 : Integer.Sparse Key := [(key2318, -6), (key2317, 2), (key2203, 2), (key2317, 2), (key2321, 6), (key2317, -2), (key2098, -2), (key2317, -2), (key2321, -2), (key2206, -2), (key2321, -2), (key2318, 2), (key2099, 2), (key2318, 2)]

theorem rawRowCheck2540 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form4 = rawRow2540 := by decide +kernel

def row2540 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

theorem rowCheck2540 : row2540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2540 := by decide +kernel

theorem rowEval2540 (x : Key → ℝ) : Integer.Sparse.eval row2540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2540, Integer.Sparse.eval_collectBalanced, rawRowCheck2540]

def rawRow2541 : Integer.Sparse Key := [(key2318, -6), (key2317, 2), (key2317, 2), (key2203, 2), (key2321, 6), (key2317, -2), (key2317, -2), (key2098, -2), (key2321, -2), (key2321, -2), (key2206, -2), (key2318, 2), (key2318, 2), (key2099, 2)]

theorem rawRowCheck2541 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form4 = rawRow2541 := by decide +kernel

def row2541 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 2), (key2206, -2), (key2318, -2), (key2321, 2)]

theorem rowCheck2541 : row2541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2541 := by decide +kernel

theorem rowEval2541 (x : Key → ℝ) : Integer.Sparse.eval row2541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2541, Integer.Sparse.eval_collectBalanced, rawRowCheck2541]

def rawRow2542 : Integer.Sparse Key := [(key2206, -6), (key2321, 2), (key2321, 2), (key2321, 2), (key2099, 6), (key2318, -2), (key2318, -2), (key2318, -2), (key2098, -2), (key2098, -2), (key2098, -2), (key2203, 2), (key2203, 2), (key2203, 2)]

theorem rawRowCheck2542 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow2542 := by decide +kernel

def row2542 : Integer.Sparse Key := [(key2098, -6), (key2099, 6), (key2203, 6), (key2206, -6), (key2318, -6), (key2321, 6)]

theorem rowCheck2542 : row2542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2542 := by decide +kernel

theorem rowEval2542 (x : Key → ℝ) : Integer.Sparse.eval row2542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2542, Integer.Sparse.eval_collectBalanced, rawRowCheck2542]

def rawRow2543 : Integer.Sparse Key := [(key2321, -6), (key2206, 2), (key2321, 2), (key2321, 2), (key2318, 6), (key2099, -2), (key2318, -2), (key2318, -2), (key2203, -2), (key2317, -2), (key2317, -2), (key2098, 2), (key2317, 2), (key2317, 2)]

theorem rawRowCheck2543 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form4 = rawRow2543 := by decide +kernel

def row2543 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

theorem rowCheck2543 : row2543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2543 := by decide +kernel

theorem rowEval2543 (x : Key → ℝ) : Integer.Sparse.eval row2543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2543, Integer.Sparse.eval_collectBalanced, rawRowCheck2543]

def rawRow2544 : Integer.Sparse Key := [(key2321, -6), (key2321, 2), (key2206, 2), (key2321, 2), (key2318, 6), (key2318, -2), (key2099, -2), (key2318, -2), (key2317, -2), (key2203, -2), (key2317, -2), (key2317, 2), (key2098, 2), (key2317, 2)]

theorem rawRowCheck2544 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form4 = rawRow2544 := by decide +kernel

def row2544 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

theorem rowCheck2544 : row2544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2544 := by decide +kernel

theorem rowEval2544 (x : Key → ℝ) : Integer.Sparse.eval row2544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2544, Integer.Sparse.eval_collectBalanced, rawRowCheck2544]

def rawRow2545 : Integer.Sparse Key := [(key2321, -6), (key2321, 2), (key2321, 2), (key2206, 2), (key2318, 6), (key2318, -2), (key2318, -2), (key2099, -2), (key2317, -2), (key2317, -2), (key2203, -2), (key2317, 2), (key2317, 2), (key2098, 2)]

theorem rawRowCheck2545 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form4 = rawRow2545 := by decide +kernel

def row2545 : Integer.Sparse Key := [(key2098, 2), (key2099, -2), (key2203, -2), (key2206, 2), (key2318, 2), (key2321, -2)]

theorem rowCheck2545 : row2545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2545 := by decide +kernel

theorem rowEval2545 (x : Key → ℝ) : Integer.Sparse.eval row2545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2545, Integer.Sparse.eval_collectBalanced, rawRowCheck2545]

def rawRow2546 : Integer.Sparse Key := [(key817, -1), (key818, -1), (key817, -1), (key825, -1), (key818, -1), (key825, -1), (key818, 2), (key818, 2), (key825, 2), (key897, 1), (key898, 1), (key897, 1), (key908, 1), (key898, 1), (key908, 1), (key898, -1), (key902, -1), (key898, -1), (key908, -1), (key902, -1), (key908, -1), (key960, -2), (key960, -2), (key964, -2), (key960, 1), (key962, 1), (key960, 1), (key964, 1), (key962, 1), (key964, 1)]

theorem rawRowCheck2546 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form5 = rawRow2546 := by decide +kernel

def row2546 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

theorem rowCheck2546 : row2546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2546 := by decide +kernel

theorem rowEval2546 (x : Key → ℝ) : Integer.Sparse.eval row2546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2546, Integer.Sparse.eval_collectBalanced, rawRowCheck2546]

def rawRow2547 : Integer.Sparse Key := [(key818, -1), (key817, -1), (key825, -1), (key817, -1), (key825, -1), (key818, -1), (key818, 2), (key825, 2), (key818, 2), (key898, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key898, 1), (key902, -1), (key898, -1), (key908, -1), (key898, -1), (key908, -1), (key902, -1), (key960, -2), (key964, -2), (key960, -2), (key962, 1), (key960, 1), (key964, 1), (key960, 1), (key964, 1), (key962, 1)]

theorem rawRowCheck2547 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form5 = rawRow2547 := by decide +kernel

def row2547 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

theorem rowCheck2547 : row2547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2547 := by decide +kernel

theorem rowEval2547 (x : Key → ℝ) : Integer.Sparse.eval row2547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2547, Integer.Sparse.eval_collectBalanced, rawRowCheck2547]

def rawRow2548 : Integer.Sparse Key := [(key825, -1), (key825, -1), (key818, -1), (key818, -1), (key817, -1), (key817, -1), (key825, 2), (key818, 2), (key818, 2), (key908, 1), (key908, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key908, -1), (key908, -1), (key902, -1), (key902, -1), (key898, -1), (key898, -1), (key964, -2), (key960, -2), (key960, -2), (key964, 1), (key964, 1), (key962, 1), (key962, 1), (key960, 1), (key960, 1)]

theorem rawRowCheck2548 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form5 = rawRow2548 := by decide +kernel

def row2548 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

theorem rowCheck2548 : row2548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2548 := by decide +kernel

theorem rowEval2548 (x : Key → ℝ) : Integer.Sparse.eval row2548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2548, Integer.Sparse.eval_collectBalanced, rawRowCheck2548]

def rawRow2549 : Integer.Sparse Key := [(key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key817, 2), (key817, 2), (key817, 2), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key897, -1), (key897, -1), (key897, -1), (key897, -1), (key897, -1), (key897, -1), (key962, -2), (key962, -2), (key962, -2), (key960, 1), (key960, 1), (key960, 1), (key960, 1), (key960, 1), (key960, 1)]

theorem rawRowCheck2549 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form5 = rawRow2549 := by decide +kernel

def row2549 : Integer.Sparse Key := [(key817, 6), (key818, -6), (key897, -6), (key902, 6), (key960, 6), (key962, -6)]

theorem rowCheck2549 : row2549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2549 := by decide +kernel

theorem rowEval2549 (x : Key → ℝ) : Integer.Sparse.eval row2549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2549, Integer.Sparse.eval_collectBalanced, rawRowCheck2549]

def rawRow2550 : Integer.Sparse Key := [(key897, -1), (key898, -1), (key897, -1), (key908, -1), (key898, -1), (key908, -1), (key960, 2), (key960, 2), (key964, 2), (key817, 1), (key818, 1), (key817, 1), (key825, 1), (key818, 1), (key825, 1), (key960, -1), (key962, -1), (key960, -1), (key964, -1), (key962, -1), (key964, -1), (key818, -2), (key818, -2), (key825, -2), (key898, 1), (key902, 1), (key898, 1), (key908, 1), (key902, 1), (key908, 1)]

theorem rawRowCheck2550 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form5 = rawRow2550 := by decide +kernel

def row2550 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

theorem rowCheck2550 : row2550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2550 := by decide +kernel

theorem rowEval2550 (x : Key → ℝ) : Integer.Sparse.eval row2550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2550, Integer.Sparse.eval_collectBalanced, rawRowCheck2550]

def rawRow2551 : Integer.Sparse Key := [(key898, -1), (key897, -1), (key908, -1), (key897, -1), (key908, -1), (key898, -1), (key960, 2), (key964, 2), (key960, 2), (key818, 1), (key817, 1), (key825, 1), (key817, 1), (key825, 1), (key818, 1), (key962, -1), (key960, -1), (key964, -1), (key960, -1), (key964, -1), (key962, -1), (key818, -2), (key825, -2), (key818, -2), (key902, 1), (key898, 1), (key908, 1), (key898, 1), (key908, 1), (key902, 1)]

theorem rawRowCheck2551 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form5 = rawRow2551 := by decide +kernel

def row2551 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

theorem rowCheck2551 : row2551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2551 := by decide +kernel

theorem rowEval2551 (x : Key → ℝ) : Integer.Sparse.eval row2551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2551, Integer.Sparse.eval_collectBalanced, rawRowCheck2551]

def rawRow2552 : Integer.Sparse Key := [(key908, -1), (key908, -1), (key898, -1), (key898, -1), (key897, -1), (key897, -1), (key964, 2), (key960, 2), (key960, 2), (key825, 1), (key825, 1), (key818, 1), (key818, 1), (key817, 1), (key817, 1), (key964, -1), (key964, -1), (key962, -1), (key962, -1), (key960, -1), (key960, -1), (key825, -2), (key818, -2), (key818, -2), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key898, 1), (key898, 1)]

theorem rawRowCheck2552 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form5 = rawRow2552 := by decide +kernel

def row2552 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

theorem rowCheck2552 : row2552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2552 := by decide +kernel

theorem rowEval2552 (x : Key → ℝ) : Integer.Sparse.eval row2552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2552, Integer.Sparse.eval_collectBalanced, rawRowCheck2552]

def rawRow2553 : Integer.Sparse Key := [(key738, -1), (key738, -1), (key898, -1), (key898, -1), (key960, -1), (key960, -1), (key737, 2), (key897, 2), (key897, 2), (key743, 1), (key743, 1), (key902, 1), (key902, 1), (key962, 1), (key962, 1), (key737, -1), (key737, -1), (key817, -1), (key817, -1), (key897, -1), (key897, -1), (key743, -2), (key902, -2), (key902, -2), (key738, 1), (key738, 1), (key818, 1), (key818, 1), (key898, 1), (key898, 1)]

theorem rawRowCheck2553 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form5 = rawRow2553 := by decide +kernel

def row2553 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

theorem rowCheck2553 : row2553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2553 := by decide +kernel

theorem rowEval2553 (x : Key → ℝ) : Integer.Sparse.eval row2553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2553, Integer.Sparse.eval_collectBalanced, rawRowCheck2553]

def rawRow2554 : Integer.Sparse Key := [(key898, -1), (key960, -1), (key738, -1), (key960, -1), (key738, -1), (key898, -1), (key897, 2), (key737, 2), (key897, 2), (key902, 1), (key962, 1), (key743, 1), (key962, 1), (key743, 1), (key902, 1), (key817, -1), (key897, -1), (key737, -1), (key897, -1), (key737, -1), (key817, -1), (key902, -2), (key743, -2), (key902, -2), (key818, 1), (key898, 1), (key738, 1), (key898, 1), (key738, 1), (key818, 1)]

theorem rawRowCheck2554 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form5 = rawRow2554 := by decide +kernel

def row2554 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

theorem rowCheck2554 : row2554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2554 := by decide +kernel

theorem rowEval2554 (x : Key → ℝ) : Integer.Sparse.eval row2554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2554, Integer.Sparse.eval_collectBalanced, rawRowCheck2554]

def rawRow2555 : Integer.Sparse Key := [(key960, -1), (key898, -1), (key960, -1), (key738, -1), (key898, -1), (key738, -1), (key897, 2), (key897, 2), (key737, 2), (key962, 1), (key902, 1), (key962, 1), (key743, 1), (key902, 1), (key743, 1), (key897, -1), (key817, -1), (key897, -1), (key737, -1), (key817, -1), (key737, -1), (key902, -2), (key902, -2), (key743, -2), (key898, 1), (key818, 1), (key898, 1), (key738, 1), (key818, 1), (key738, 1)]

theorem rawRowCheck2555 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form5 = rawRow2555 := by decide +kernel

def row2555 : Integer.Sparse Key := [(key817, -2), (key818, 2), (key897, 2), (key902, -2), (key960, -2), (key962, 2)]

theorem rowCheck2555 : row2555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2555 := by decide +kernel

theorem rowEval2555 (x : Key → ℝ) : Integer.Sparse.eval row2555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2555, Integer.Sparse.eval_collectBalanced, rawRowCheck2555]

def rawRow2556 : Integer.Sparse Key := [(key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key962, 2), (key962, 2), (key962, 2), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key960, -1), (key960, -1), (key960, -1), (key960, -1), (key960, -1), (key960, -1), (key817, -2), (key817, -2), (key817, -2), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1)]

theorem rawRowCheck2556 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form5 = rawRow2556 := by decide +kernel

def row2556 : Integer.Sparse Key := [(key817, -6), (key818, 6), (key897, 6), (key902, -6), (key960, -6), (key962, 6)]

theorem rowCheck2556 : row2556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2556 := by decide +kernel

theorem rowEval2556 (x : Key → ℝ) : Integer.Sparse.eval row2556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2556, Integer.Sparse.eval_collectBalanced, rawRowCheck2556]

def rawRow2557 : Integer.Sparse Key := [(key743, -1), (key743, -1), (key902, -1), (key902, -1), (key962, -1), (key962, -1), (key743, 2), (key902, 2), (key902, 2), (key738, 1), (key738, 1), (key898, 1), (key898, 1), (key960, 1), (key960, 1), (key738, -1), (key738, -1), (key818, -1), (key818, -1), (key898, -1), (key898, -1), (key737, -2), (key897, -2), (key897, -2), (key737, 1), (key737, 1), (key817, 1), (key817, 1), (key897, 1), (key897, 1)]

theorem rawRowCheck2557 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form5 = rawRow2557 := by decide +kernel

def row2557 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

theorem rowCheck2557 : row2557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2557 := by decide +kernel

theorem rowEval2557 (x : Key → ℝ) : Integer.Sparse.eval row2557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2557, Integer.Sparse.eval_collectBalanced, rawRowCheck2557]

def rawRow2558 : Integer.Sparse Key := [(key902, -1), (key962, -1), (key743, -1), (key962, -1), (key743, -1), (key902, -1), (key902, 2), (key743, 2), (key902, 2), (key898, 1), (key960, 1), (key738, 1), (key960, 1), (key738, 1), (key898, 1), (key818, -1), (key898, -1), (key738, -1), (key898, -1), (key738, -1), (key818, -1), (key897, -2), (key737, -2), (key897, -2), (key817, 1), (key897, 1), (key737, 1), (key897, 1), (key737, 1), (key817, 1)]

theorem rawRowCheck2558 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form5 = rawRow2558 := by decide +kernel

def row2558 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

theorem rowCheck2558 : row2558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2558 := by decide +kernel

theorem rowEval2558 (x : Key → ℝ) : Integer.Sparse.eval row2558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2558, Integer.Sparse.eval_collectBalanced, rawRowCheck2558]

def rawRow2559 : Integer.Sparse Key := [(key962, -1), (key902, -1), (key962, -1), (key743, -1), (key902, -1), (key743, -1), (key902, 2), (key902, 2), (key743, 2), (key960, 1), (key898, 1), (key960, 1), (key738, 1), (key898, 1), (key738, 1), (key898, -1), (key818, -1), (key898, -1), (key738, -1), (key818, -1), (key738, -1), (key897, -2), (key897, -2), (key737, -2), (key897, 1), (key817, 1), (key897, 1), (key737, 1), (key817, 1), (key737, 1)]

theorem rawRowCheck2559 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form5 = rawRow2559 := by decide +kernel

def row2559 : Integer.Sparse Key := [(key817, 2), (key818, -2), (key897, -2), (key902, 2), (key960, 2), (key962, -2)]

theorem rowCheck2559 : row2559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2559 := by decide +kernel

theorem rowEval2559 (x : Key → ℝ) : Integer.Sparse.eval row2559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2559, Integer.Sparse.eval_collectBalanced, rawRowCheck2559]

end MUB6.Certificate.GramRows

end OAI

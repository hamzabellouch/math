import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
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

def rawRow2944 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2456, -2), (key2531, 6), (key2364, 2), (key2361, 2), (key2361, 2), (key2561, -2), (key2561, -2), (key2531, -2), (key2364, -6), (key2520, 2), (key2520, 2), (key2459, 2)]

theorem rawRowCheck2944 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form11 = rawRow2944 := by decide +kernel

def row2944 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2456, -4), (key2520, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck2944 : row2944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2944 := by decide +kernel

theorem rowEval2944 (x : Key → ℝ) : Integer.Sparse.eval row2944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2944, Integer.Sparse.eval_collectBalanced, rawRowCheck2944]

def rawRow2945 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2531, -2), (key2456, 6), (key2517, 2), (key2520, 2), (key2561, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2520, -6), (key2364, 2), (key2459, 2), (key2520, 2)]

theorem rawRowCheck2945 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form11 = rawRow2945 := by decide +kernel

def row2945 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

theorem rowCheck2945 : row2945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2945 := by decide +kernel

theorem rowEval2945 (x : Key → ℝ) : Integer.Sparse.eval row2945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2945, Integer.Sparse.eval_collectBalanced, rawRowCheck2945]

def rawRow2946 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2531, -2), (key2456, 6), (key2520, 2), (key2517, 2), (key2561, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2520, -6), (key2364, 2), (key2520, 2), (key2459, 2)]

theorem rawRowCheck2946 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form11 = rawRow2946 := by decide +kernel

def row2946 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

theorem rowCheck2946 : row2946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2946 := by decide +kernel

theorem rowEval2946 (x : Key → ℝ) : Integer.Sparse.eval row2946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2946, Integer.Sparse.eval_collectBalanced, rawRowCheck2946]

def rawRow2947 : Integer.Sparse Key := [(key2456, -2), (key2531, -2), (key2459, -2), (key2456, 6), (key2517, 2), (key2561, 2), (key2520, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2520, -6), (key2459, 2), (key2364, 2), (key2520, 2)]

theorem rawRowCheck2947 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form11 = rawRow2947 := by decide +kernel

def row2947 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

theorem rowCheck2947 : row2947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2947 := by decide +kernel

theorem rowEval2947 (x : Key → ℝ) : Integer.Sparse.eval row2947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2947, Integer.Sparse.eval_collectBalanced, rawRowCheck2947]

def rawRow2948 : Integer.Sparse Key := [(key2531, -2), (key2456, -2), (key2459, -2), (key2456, 6), (key2561, 2), (key2517, 2), (key2520, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2520, -6), (key2459, 2), (key2520, 2), (key2364, 2)]

theorem rawRowCheck2948 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form11 = rawRow2948 := by decide +kernel

def row2948 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

theorem rowCheck2948 : row2948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2948 := by decide +kernel

theorem rowEval2948 (x : Key → ℝ) : Integer.Sparse.eval row2948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2948, Integer.Sparse.eval_collectBalanced, rawRowCheck2948]

def rawRow2949 : Integer.Sparse Key := [(key2459, -2), (key2531, -2), (key2456, -2), (key2456, 6), (key2520, 2), (key2561, 2), (key2517, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2520, -6), (key2520, 2), (key2364, 2), (key2459, 2)]

theorem rawRowCheck2949 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form11 = rawRow2949 := by decide +kernel

def row2949 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

theorem rowCheck2949 : row2949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2949 := by decide +kernel

theorem rowEval2949 (x : Key → ℝ) : Integer.Sparse.eval row2949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2949, Integer.Sparse.eval_collectBalanced, rawRowCheck2949]

def rawRow2950 : Integer.Sparse Key := [(key2531, -2), (key2459, -2), (key2456, -2), (key2456, 6), (key2561, 2), (key2520, 2), (key2517, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2520, -6), (key2520, 2), (key2459, 2), (key2364, 2)]

theorem rawRowCheck2950 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form11 = rawRow2950 := by decide +kernel

def row2950 : Integer.Sparse Key := [(key2361, -2), (key2364, 2), (key2456, 2), (key2520, -2), (key2531, -2), (key2561, 2)]

theorem rowCheck2950 : row2950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2950 := by decide +kernel

theorem rowEval2950 (x : Key → ℝ) : Integer.Sparse.eval row2950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2950, Integer.Sparse.eval_collectBalanced, rawRowCheck2950]

def rawRow2951 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2520, -2), (key2561, 6), (key2361, 2), (key2364, 2), (key2364, 2), (key2531, -2), (key2531, -2), (key2561, -2), (key2361, -6), (key2456, 2), (key2456, 2), (key2517, 2)]

theorem rawRowCheck2951 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2951 := by decide +kernel

def row2951 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck2951 : row2951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2951 := by decide +kernel

theorem rowEval2951 (x : Key → ℝ) : Integer.Sparse.eval row2951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2951, Integer.Sparse.eval_collectBalanced, rawRowCheck2951]

def rawRow2952 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2520, -2), (key2561, 6), (key2364, 2), (key2361, 2), (key2364, 2), (key2531, -2), (key2561, -2), (key2531, -2), (key2361, -6), (key2456, 2), (key2517, 2), (key2456, 2)]

theorem rawRowCheck2952 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2952 := by decide +kernel

def row2952 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck2952 : row2952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2952 := by decide +kernel

theorem rowEval2952 (x : Key → ℝ) : Integer.Sparse.eval row2952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2952, Integer.Sparse.eval_collectBalanced, rawRowCheck2952]

def rawRow2953 : Integer.Sparse Key := [(key2520, -2), (key2520, -2), (key2517, -2), (key2561, 6), (key2364, 2), (key2364, 2), (key2361, 2), (key2561, -2), (key2531, -2), (key2531, -2), (key2361, -6), (key2517, 2), (key2456, 2), (key2456, 2)]

theorem rawRowCheck2953 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2953 := by decide +kernel

def row2953 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, 4), (key2520, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck2953 : row2953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2953 := by decide +kernel

theorem rowEval2953 (x : Key → ℝ) : Integer.Sparse.eval row2953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2953, Integer.Sparse.eval_collectBalanced, rawRowCheck2953]

def rawRow2954 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2561, -2), (key2520, 6), (key2456, 2), (key2459, 2), (key2531, 2), (key2364, -2), (key2459, -2), (key2520, -2), (key2456, -6), (key2361, 2), (key2456, 2), (key2517, 2)]

theorem rawRowCheck2954 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form11 = rawRow2954 := by decide +kernel

def row2954 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

theorem rowCheck2954 : row2954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2954 := by decide +kernel

theorem rowEval2954 (x : Key → ℝ) : Integer.Sparse.eval row2954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2954, Integer.Sparse.eval_collectBalanced, rawRowCheck2954]

def rawRow2955 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2561, -2), (key2520, 6), (key2459, 2), (key2456, 2), (key2531, 2), (key2364, -2), (key2520, -2), (key2459, -2), (key2456, -6), (key2361, 2), (key2517, 2), (key2456, 2)]

theorem rawRowCheck2955 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form11 = rawRow2955 := by decide +kernel

def row2955 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

theorem rowCheck2955 : row2955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2955 := by decide +kernel

theorem rowEval2955 (x : Key → ℝ) : Integer.Sparse.eval row2955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2955, Integer.Sparse.eval_collectBalanced, rawRowCheck2955]

def rawRow2956 : Integer.Sparse Key := [(key2517, -2), (key2561, -2), (key2520, -2), (key2520, 6), (key2456, 2), (key2531, 2), (key2459, 2), (key2459, -2), (key2364, -2), (key2520, -2), (key2456, -6), (key2456, 2), (key2361, 2), (key2517, 2)]

theorem rawRowCheck2956 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form11 = rawRow2956 := by decide +kernel

def row2956 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

theorem rowCheck2956 : row2956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2956 := by decide +kernel

theorem rowEval2956 (x : Key → ℝ) : Integer.Sparse.eval row2956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2956, Integer.Sparse.eval_collectBalanced, rawRowCheck2956]

def rawRow2957 : Integer.Sparse Key := [(key2561, -2), (key2517, -2), (key2520, -2), (key2520, 6), (key2531, 2), (key2456, 2), (key2459, 2), (key2459, -2), (key2520, -2), (key2364, -2), (key2456, -6), (key2456, 2), (key2517, 2), (key2361, 2)]

theorem rawRowCheck2957 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form11 = rawRow2957 := by decide +kernel

def row2957 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

theorem rowCheck2957 : row2957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2957 := by decide +kernel

theorem rowEval2957 (x : Key → ℝ) : Integer.Sparse.eval row2957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2957, Integer.Sparse.eval_collectBalanced, rawRowCheck2957]

def rawRow2958 : Integer.Sparse Key := [(key2520, -2), (key2561, -2), (key2517, -2), (key2520, 6), (key2459, 2), (key2531, 2), (key2456, 2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, -6), (key2517, 2), (key2361, 2), (key2456, 2)]

theorem rawRowCheck2958 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form11 = rawRow2958 := by decide +kernel

def row2958 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

theorem rowCheck2958 : row2958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2958 := by decide +kernel

theorem rowEval2958 (x : Key → ℝ) : Integer.Sparse.eval row2958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2958, Integer.Sparse.eval_collectBalanced, rawRowCheck2958]

def rawRow2959 : Integer.Sparse Key := [(key2561, -2), (key2520, -2), (key2517, -2), (key2520, 6), (key2531, 2), (key2459, 2), (key2456, 2), (key2520, -2), (key2459, -2), (key2364, -2), (key2456, -6), (key2517, 2), (key2456, 2), (key2361, 2)]

theorem rawRowCheck2959 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form11 = rawRow2959 := by decide +kernel

def row2959 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2456, -2), (key2520, 2), (key2531, 2), (key2561, -2)]

theorem rowCheck2959 : row2959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2959 := by decide +kernel

theorem rowEval2959 (x : Key → ℝ) : Integer.Sparse.eval row2959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2959, Integer.Sparse.eval_collectBalanced, rawRowCheck2959]

def rawRow2960 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2381, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2392, 1), (key2392, 1), (key2406, 2), (key2406, 2), (key2409, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2440, -1), (key2440, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2482, -1), (key2482, -1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2506, 1), (key2506, 1)]

theorem rawRowCheck2960 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form12 = rawRow2960 := by decide +kernel

def row2960 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

theorem rowCheck2960 : row2960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2960 := by decide +kernel

theorem rowEval2960 (x : Key → ℝ) : Integer.Sparse.eval row2960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2960, Integer.Sparse.eval_collectBalanced, rawRowCheck2960]

def rawRow2961 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2378, -2), (key2390, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2406, 2), (key2409, 2), (key2406, 2), (key2437, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2482, -1), (key2472, -1), (key2482, -1), (key2472, -1), (key2480, -1), (key2503, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, 1)]

theorem rawRowCheck2961 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form12 = rawRow2961 := by decide +kernel

def row2961 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

theorem rowCheck2961 : row2961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2961 := by decide +kernel

theorem rowEval2961 (x : Key → ℝ) : Integer.Sparse.eval row2961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2961, Integer.Sparse.eval_collectBalanced, rawRowCheck2961]

def rawRow2962 : Integer.Sparse Key := [(key2381, -2), (key2378, -2), (key2378, -2), (key2392, 1), (key2390, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2409, 2), (key2406, 2), (key2406, 2), (key2440, -1), (key2437, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2482, -1), (key2480, -1), (key2482, -1), (key2472, -1), (key2480, -1), (key2472, -1), (key2506, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2472, 1)]

theorem rawRowCheck2962 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form12 = rawRow2962 := by decide +kernel

def row2962 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

theorem rowCheck2962 : row2962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2962 := by decide +kernel

theorem rowEval2962 (x : Key → ℝ) : Integer.Sparse.eval row2962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2962, Integer.Sparse.eval_collectBalanced, rawRowCheck2962]

def rawRow2963 : Integer.Sparse Key := [(key2390, -2), (key2392, -2), (key2392, -2), (key2378, 1), (key2381, 1), (key2378, 1), (key2392, 1), (key2381, 1), (key2392, 1), (key2437, 2), (key2440, 2), (key2440, 2), (key2406, -1), (key2409, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2440, -1), (key2503, -1), (key2506, -1), (key2503, -1), (key2522, -1), (key2506, -1), (key2522, -1), (key2480, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2522, 1)]

theorem rawRowCheck2963 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form12 = rawRow2963 := by decide +kernel

def row2963 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

theorem rowCheck2963 : row2963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2963 := by decide +kernel

theorem rowEval2963 (x : Key → ℝ) : Integer.Sparse.eval row2963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2963, Integer.Sparse.eval_collectBalanced, rawRowCheck2963]

def rawRow2964 : Integer.Sparse Key := [(key2392, -2), (key2390, -2), (key2392, -2), (key2381, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2381, 1), (key2440, 2), (key2437, 2), (key2440, 2), (key2409, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2506, -1), (key2503, -1), (key2522, -1), (key2503, -1), (key2522, -1), (key2506, -1), (key2482, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, 1)]

theorem rawRowCheck2964 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form12 = rawRow2964 := by decide +kernel

def row2964 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

theorem rowCheck2964 : row2964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2964 := by decide +kernel

theorem rowEval2964 (x : Key → ℝ) : Integer.Sparse.eval row2964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2964, Integer.Sparse.eval_collectBalanced, rawRowCheck2964]

def rawRow2965 : Integer.Sparse Key := [(key2392, -2), (key2392, -2), (key2390, -2), (key2392, 1), (key2392, 1), (key2381, 1), (key2381, 1), (key2378, 1), (key2378, 1), (key2440, 2), (key2440, 2), (key2437, 2), (key2440, -1), (key2440, -1), (key2409, -1), (key2409, -1), (key2406, -1), (key2406, -1), (key2522, -1), (key2522, -1), (key2506, -1), (key2506, -1), (key2503, -1), (key2503, -1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1)]

theorem rawRowCheck2965 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form12 = rawRow2965 := by decide +kernel

def row2965 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

theorem rowCheck2965 : row2965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2965 := by decide +kernel

theorem rowEval2965 (x : Key → ℝ) : Integer.Sparse.eval row2965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2965, Integer.Sparse.eval_collectBalanced, rawRowCheck2965]

def rawRow2966 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2409, -2), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2482, 1), (key2482, 1), (key2378, 2), (key2378, 2), (key2381, 2), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2506, -1), (key2506, -1), (key2378, -1), (key2378, -1), (key2390, -1), (key2390, -1), (key2392, -1), (key2392, -1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2440, 1), (key2440, 1)]

theorem rawRowCheck2966 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form12 = rawRow2966 := by decide +kernel

def row2966 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

theorem rowCheck2966 : row2966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2966 := by decide +kernel

theorem rowEval2966 (x : Key → ℝ) : Integer.Sparse.eval row2966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2966, Integer.Sparse.eval_collectBalanced, rawRowCheck2966]

def rawRow2967 : Integer.Sparse Key := [(key2406, -2), (key2409, -2), (key2406, -2), (key2480, 1), (key2482, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2378, 2), (key2381, 2), (key2378, 2), (key2503, -1), (key2506, -1), (key2472, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2390, -1), (key2392, -1), (key2378, -1), (key2392, -1), (key2378, -1), (key2390, -1), (key2437, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2437, 1)]

theorem rawRowCheck2967 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form12 = rawRow2967 := by decide +kernel

def row2967 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

theorem rowCheck2967 : row2967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2967 := by decide +kernel

theorem rowEval2967 (x : Key → ℝ) : Integer.Sparse.eval row2967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2967, Integer.Sparse.eval_collectBalanced, rawRowCheck2967]

def rawRow2968 : Integer.Sparse Key := [(key2409, -2), (key2406, -2), (key2406, -2), (key2482, 1), (key2480, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2381, 2), (key2378, 2), (key2378, 2), (key2506, -1), (key2503, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2392, -1), (key2390, -1), (key2392, -1), (key2378, -1), (key2390, -1), (key2378, -1), (key2440, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2406, 1)]

theorem rawRowCheck2968 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form12 = rawRow2968 := by decide +kernel

def row2968 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2390, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2)]

theorem rowCheck2968 : row2968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2968 := by decide +kernel

theorem rowEval2968 (x : Key → ℝ) : Integer.Sparse.eval row2968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2968, Integer.Sparse.eval_collectBalanced, rawRowCheck2968]

def rawRow2969 : Integer.Sparse Key := [(key2480, -2), (key2482, -2), (key2543, -2), (key2406, 1), (key2409, 1), (key2472, 1), (key2482, 1), (key2538, 1), (key2543, 1), (key2503, 2), (key2506, 2), (key2554, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2506, -1), (key2538, -1), (key2554, -1), (key2437, -1), (key2440, -1), (key2503, -1), (key2522, -1), (key2554, -1), (key2563, -1), (key2390, 1), (key2392, 1), (key2480, 1), (key2522, 1), (key2543, 1), (key2563, 1)]

theorem rawRowCheck2969 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form12 = rawRow2969 := by decide +kernel

def row2969 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

theorem rowCheck2969 : row2969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2969 := by decide +kernel

theorem rowEval2969 (x : Key → ℝ) : Integer.Sparse.eval row2969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2969, Integer.Sparse.eval_collectBalanced, rawRowCheck2969]

def rawRow2970 : Integer.Sparse Key := [(key2482, -2), (key2480, -2), (key2543, -2), (key2409, 1), (key2406, 1), (key2482, 1), (key2472, 1), (key2543, 1), (key2538, 1), (key2506, 2), (key2503, 2), (key2554, 2), (key2381, -1), (key2378, -1), (key2506, -1), (key2472, -1), (key2554, -1), (key2538, -1), (key2440, -1), (key2437, -1), (key2522, -1), (key2503, -1), (key2563, -1), (key2554, -1), (key2392, 1), (key2390, 1), (key2522, 1), (key2480, 1), (key2563, 1), (key2543, 1)]

theorem rawRowCheck2970 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form12 = rawRow2970 := by decide +kernel

def row2970 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

theorem rowCheck2970 : row2970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2970 := by decide +kernel

theorem rowEval2970 (x : Key → ℝ) : Integer.Sparse.eval row2970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2970, Integer.Sparse.eval_collectBalanced, rawRowCheck2970]

def rawRow2971 : Integer.Sparse Key := [(key2480, -2), (key2543, -2), (key2482, -2), (key2472, 1), (key2538, 1), (key2406, 1), (key2543, 1), (key2409, 1), (key2482, 1), (key2503, 2), (key2554, 2), (key2506, 2), (key2472, -1), (key2538, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2503, -1), (key2554, -1), (key2437, -1), (key2563, -1), (key2440, -1), (key2522, -1), (key2480, 1), (key2543, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2522, 1)]

theorem rawRowCheck2971 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form12 = rawRow2971 := by decide +kernel

def row2971 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

theorem rowCheck2971 : row2971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2971 := by decide +kernel

theorem rowEval2971 (x : Key → ℝ) : Integer.Sparse.eval row2971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2971, Integer.Sparse.eval_collectBalanced, rawRowCheck2971]

def rawRow2972 : Integer.Sparse Key := [(key2543, -2), (key2480, -2), (key2482, -2), (key2538, 1), (key2472, 1), (key2543, 1), (key2406, 1), (key2482, 1), (key2409, 1), (key2554, 2), (key2503, 2), (key2506, 2), (key2538, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2506, -1), (key2381, -1), (key2554, -1), (key2503, -1), (key2563, -1), (key2437, -1), (key2522, -1), (key2440, -1), (key2543, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2522, 1), (key2392, 1)]

theorem rawRowCheck2972 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form12 = rawRow2972 := by decide +kernel

def row2972 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

theorem rowCheck2972 : row2972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2972 := by decide +kernel

theorem rowEval2972 (x : Key → ℝ) : Integer.Sparse.eval row2972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form12) x := by
  rw [rowCheck2972, Integer.Sparse.eval_collectBalanced, rawRowCheck2972]

def rawRow2973 : Integer.Sparse Key := [(key2482, -2), (key2543, -2), (key2480, -2), (key2482, 1), (key2543, 1), (key2409, 1), (key2538, 1), (key2406, 1), (key2472, 1), (key2506, 2), (key2554, 2), (key2503, 2), (key2506, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2378, -1), (key2472, -1), (key2522, -1), (key2563, -1), (key2440, -1), (key2554, -1), (key2437, -1), (key2503, -1), (key2522, 1), (key2563, 1), (key2392, 1), (key2543, 1), (key2390, 1), (key2480, 1)]

theorem rawRowCheck2973 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form12 = rawRow2973 := by decide +kernel

def row2973 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

theorem rowCheck2973 : row2973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2973 := by decide +kernel

theorem rowEval2973 (x : Key → ℝ) : Integer.Sparse.eval row2973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2973, Integer.Sparse.eval_collectBalanced, rawRowCheck2973]

def rawRow2974 : Integer.Sparse Key := [(key2543, -2), (key2482, -2), (key2480, -2), (key2543, 1), (key2482, 1), (key2538, 1), (key2409, 1), (key2472, 1), (key2406, 1), (key2554, 2), (key2506, 2), (key2503, 2), (key2554, -1), (key2506, -1), (key2538, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2563, -1), (key2522, -1), (key2554, -1), (key2440, -1), (key2503, -1), (key2437, -1), (key2563, 1), (key2522, 1), (key2543, 1), (key2392, 1), (key2480, 1), (key2390, 1)]

theorem rawRowCheck2974 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form12 = rawRow2974 := by decide +kernel

def row2974 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2406, 1), (key2409, 1), (key2437, -1), (key2440, -1), (key2480, -1), (key2482, -1), (key2503, 1), (key2506, 1)]

theorem rowCheck2974 : row2974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2974 := by decide +kernel

theorem rowEval2974 (x : Key → ℝ) : Integer.Sparse.eval row2974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form12) x := by
  rw [rowCheck2974, Integer.Sparse.eval_collectBalanced, rawRowCheck2974]

def rawRow2975 : Integer.Sparse Key := [(key2437, -2), (key2440, -2), (key2440, -2), (key2503, 1), (key2506, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2390, 2), (key2392, 2), (key2392, 2), (key2480, -1), (key2482, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2378, -1), (key2381, -1), (key2378, -1), (key2392, -1), (key2381, -1), (key2392, -1), (key2406, 1), (key2409, 1), (key2406, 1), (key2440, 1), (key2409, 1), (key2440, 1)]

theorem rawRowCheck2975 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form12 = rawRow2975 := by decide +kernel

def row2975 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

theorem rowCheck2975 : row2975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2975 := by decide +kernel

theorem rowEval2975 (x : Key → ℝ) : Integer.Sparse.eval row2975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2975, Integer.Sparse.eval_collectBalanced, rawRowCheck2975]

def rawRow2976 : Integer.Sparse Key := [(key2440, -2), (key2437, -2), (key2440, -2), (key2506, 1), (key2503, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2392, 2), (key2390, 2), (key2392, 2), (key2482, -1), (key2480, -1), (key2522, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2381, -1), (key2378, -1), (key2392, -1), (key2378, -1), (key2392, -1), (key2381, -1), (key2409, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2409, 1)]

theorem rawRowCheck2976 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form12 = rawRow2976 := by decide +kernel

def row2976 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

theorem rowCheck2976 : row2976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2976 := by decide +kernel

theorem rowEval2976 (x : Key → ℝ) : Integer.Sparse.eval row2976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2976, Integer.Sparse.eval_collectBalanced, rawRowCheck2976]

def rawRow2977 : Integer.Sparse Key := [(key2440, -2), (key2440, -2), (key2437, -2), (key2522, 1), (key2522, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1), (key2392, 2), (key2392, 2), (key2390, 2), (key2522, -1), (key2522, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2392, -1), (key2392, -1), (key2381, -1), (key2381, -1), (key2378, -1), (key2378, -1), (key2440, 1), (key2440, 1), (key2409, 1), (key2409, 1), (key2406, 1), (key2406, 1)]

theorem rawRowCheck2977 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form12 = rawRow2977 := by decide +kernel

def row2977 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2437, -2), (key2440, -2), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2)]

theorem rowCheck2977 : row2977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2977 := by decide +kernel

theorem rowEval2977 (x : Key → ℝ) : Integer.Sparse.eval row2977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2977, Integer.Sparse.eval_collectBalanced, rawRowCheck2977]

def rawRow2978 : Integer.Sparse Key := [(key2503, -2), (key2506, -2), (key2554, -2), (key2437, 1), (key2440, 1), (key2503, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2480, 2), (key2482, 2), (key2543, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2522, -1), (key2543, -1), (key2563, -1), (key2406, -1), (key2409, -1), (key2472, -1), (key2482, -1), (key2538, -1), (key2543, -1), (key2378, 1), (key2381, 1), (key2472, 1), (key2506, 1), (key2538, 1), (key2554, 1)]

theorem rawRowCheck2978 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form12 = rawRow2978 := by decide +kernel

def row2978 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

theorem rowCheck2978 : row2978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2978 := by decide +kernel

theorem rowEval2978 (x : Key → ℝ) : Integer.Sparse.eval row2978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2978, Integer.Sparse.eval_collectBalanced, rawRowCheck2978]

def rawRow2979 : Integer.Sparse Key := [(key2506, -2), (key2503, -2), (key2554, -2), (key2440, 1), (key2437, 1), (key2522, 1), (key2503, 1), (key2563, 1), (key2554, 1), (key2482, 2), (key2480, 2), (key2543, 2), (key2392, -1), (key2390, -1), (key2522, -1), (key2480, -1), (key2563, -1), (key2543, -1), (key2409, -1), (key2406, -1), (key2482, -1), (key2472, -1), (key2543, -1), (key2538, -1), (key2381, 1), (key2378, 1), (key2506, 1), (key2472, 1), (key2554, 1), (key2538, 1)]

theorem rawRowCheck2979 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form12 = rawRow2979 := by decide +kernel

def row2979 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

theorem rowCheck2979 : row2979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2979 := by decide +kernel

theorem rowEval2979 (x : Key → ℝ) : Integer.Sparse.eval row2979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2979, Integer.Sparse.eval_collectBalanced, rawRowCheck2979]

def rawRow2980 : Integer.Sparse Key := [(key2503, -2), (key2554, -2), (key2506, -2), (key2503, 1), (key2554, 1), (key2437, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2480, 2), (key2543, 2), (key2482, 2), (key2480, -1), (key2543, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2472, -1), (key2538, -1), (key2406, -1), (key2543, -1), (key2409, -1), (key2482, -1), (key2472, 1), (key2538, 1), (key2378, 1), (key2554, 1), (key2381, 1), (key2506, 1)]

theorem rawRowCheck2980 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form12 = rawRow2980 := by decide +kernel

def row2980 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

theorem rowCheck2980 : row2980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2980 := by decide +kernel

theorem rowEval2980 (x : Key → ℝ) : Integer.Sparse.eval row2980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2980, Integer.Sparse.eval_collectBalanced, rawRowCheck2980]

def rawRow2981 : Integer.Sparse Key := [(key2554, -2), (key2503, -2), (key2506, -2), (key2554, 1), (key2503, 1), (key2563, 1), (key2437, 1), (key2522, 1), (key2440, 1), (key2543, 2), (key2480, 2), (key2482, 2), (key2543, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2522, -1), (key2392, -1), (key2538, -1), (key2472, -1), (key2543, -1), (key2406, -1), (key2482, -1), (key2409, -1), (key2538, 1), (key2472, 1), (key2554, 1), (key2378, 1), (key2506, 1), (key2381, 1)]

theorem rawRowCheck2981 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form12 = rawRow2981 := by decide +kernel

def row2981 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

theorem rowCheck2981 : row2981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2981 := by decide +kernel

theorem rowEval2981 (x : Key → ℝ) : Integer.Sparse.eval row2981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form12) x := by
  rw [rowCheck2981, Integer.Sparse.eval_collectBalanced, rawRowCheck2981]

def rawRow2982 : Integer.Sparse Key := [(key2506, -2), (key2554, -2), (key2503, -2), (key2522, 1), (key2563, 1), (key2440, 1), (key2554, 1), (key2437, 1), (key2503, 1), (key2482, 2), (key2543, 2), (key2480, 2), (key2522, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2390, -1), (key2480, -1), (key2482, -1), (key2543, -1), (key2409, -1), (key2538, -1), (key2406, -1), (key2472, -1), (key2506, 1), (key2554, 1), (key2381, 1), (key2538, 1), (key2378, 1), (key2472, 1)]

theorem rawRowCheck2982 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form12 = rawRow2982 := by decide +kernel

def row2982 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

theorem rowCheck2982 : row2982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2982 := by decide +kernel

theorem rowEval2982 (x : Key → ℝ) : Integer.Sparse.eval row2982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2982, Integer.Sparse.eval_collectBalanced, rawRowCheck2982]

def rawRow2983 : Integer.Sparse Key := [(key2554, -2), (key2506, -2), (key2503, -2), (key2563, 1), (key2522, 1), (key2554, 1), (key2440, 1), (key2503, 1), (key2437, 1), (key2543, 2), (key2482, 2), (key2480, 2), (key2563, -1), (key2522, -1), (key2543, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2543, -1), (key2482, -1), (key2538, -1), (key2409, -1), (key2472, -1), (key2406, -1), (key2554, 1), (key2506, 1), (key2538, 1), (key2381, 1), (key2472, 1), (key2378, 1)]

theorem rawRowCheck2983 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form12 = rawRow2983 := by decide +kernel

def row2983 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2406, -1), (key2409, -1), (key2437, 1), (key2440, 1), (key2480, 1), (key2482, 1), (key2503, -1), (key2506, -1)]

theorem rowCheck2983 : row2983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2983 := by decide +kernel

theorem rowEval2983 (x : Key → ℝ) : Integer.Sparse.eval row2983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form12) x := by
  rw [rowCheck2983, Integer.Sparse.eval_collectBalanced, rawRowCheck2983]

def rawRow2984 : Integer.Sparse Key := [(key1999, -2), (key1999, -2), (key2003, -2), (key2003, 6), (key2268, 2), (key2268, 2), (key2272, 2), (key2272, -2), (key2324, -2), (key2324, -2), (key2294, -6), (key2294, 2), (key2336, 2), (key2336, 2)]

theorem rawRowCheck2984 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form13 = rawRow2984 := by decide +kernel

def row2984 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

theorem rowCheck2984 : row2984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2984 := by decide +kernel

theorem rowEval2984 (x : Key → ℝ) : Integer.Sparse.eval row2984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2984, Integer.Sparse.eval_collectBalanced, rawRowCheck2984]

def rawRow2985 : Integer.Sparse Key := [(key1999, -2), (key2003, -2), (key1999, -2), (key2003, 6), (key2268, 2), (key2272, 2), (key2268, 2), (key2324, -2), (key2272, -2), (key2324, -2), (key2294, -6), (key2336, 2), (key2294, 2), (key2336, 2)]

theorem rawRowCheck2985 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form13 = rawRow2985 := by decide +kernel

def row2985 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

theorem rowCheck2985 : row2985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2985 := by decide +kernel

theorem rowEval2985 (x : Key → ℝ) : Integer.Sparse.eval row2985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2985, Integer.Sparse.eval_collectBalanced, rawRowCheck2985]

def rawRow2986 : Integer.Sparse Key := [(key2003, -2), (key1999, -2), (key1999, -2), (key2003, 6), (key2272, 2), (key2268, 2), (key2268, 2), (key2324, -2), (key2324, -2), (key2272, -2), (key2294, -6), (key2336, 2), (key2336, 2), (key2294, 2)]

theorem rawRowCheck2986 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form13 = rawRow2986 := by decide +kernel

def row2986 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

theorem rowCheck2986 : row2986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2986 := by decide +kernel

theorem rowEval2986 (x : Key → ℝ) : Integer.Sparse.eval row2986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2986, Integer.Sparse.eval_collectBalanced, rawRowCheck2986]

def rawRow2987 : Integer.Sparse Key := [(key1999, -2), (key2003, -2), (key2003, -2), (key1999, 6), (key2323, 2), (key2324, 2), (key2324, 2), (key2268, -2), (key2268, -2), (key2323, -2), (key2336, -6), (key2294, 2), (key2294, 2), (key2336, 2)]

theorem rawRowCheck2987 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form13 = rawRow2987 := by decide +kernel

def row2987 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

theorem rowCheck2987 : row2987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2987 := by decide +kernel

theorem rowEval2987 (x : Key → ℝ) : Integer.Sparse.eval row2987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2987, Integer.Sparse.eval_collectBalanced, rawRowCheck2987]

def rawRow2988 : Integer.Sparse Key := [(key2003, -2), (key1999, -2), (key2003, -2), (key1999, 6), (key2324, 2), (key2323, 2), (key2324, 2), (key2268, -2), (key2323, -2), (key2268, -2), (key2336, -6), (key2294, 2), (key2336, 2), (key2294, 2)]

theorem rawRowCheck2988 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form13 = rawRow2988 := by decide +kernel

def row2988 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

theorem rowCheck2988 : row2988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2988 := by decide +kernel

theorem rowEval2988 (x : Key → ℝ) : Integer.Sparse.eval row2988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2988, Integer.Sparse.eval_collectBalanced, rawRowCheck2988]

def rawRow2989 : Integer.Sparse Key := [(key2003, -2), (key2003, -2), (key1999, -2), (key1999, 6), (key2324, 2), (key2324, 2), (key2323, 2), (key2323, -2), (key2268, -2), (key2268, -2), (key2336, -6), (key2336, 2), (key2294, 2), (key2294, 2)]

theorem rawRowCheck2989 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form13 = rawRow2989 := by decide +kernel

def row2989 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

theorem rowCheck2989 : row2989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2989 := by decide +kernel

theorem rowEval2989 (x : Key → ℝ) : Integer.Sparse.eval row2989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2989, Integer.Sparse.eval_collectBalanced, rawRowCheck2989]

def rawRow2990 : Integer.Sparse Key := [(key2268, -2), (key2268, -2), (key2272, -2), (key2294, 6), (key1999, 2), (key1999, 2), (key2003, 2), (key2294, -2), (key2336, -2), (key2336, -2), (key2003, -6), (key2272, 2), (key2324, 2), (key2324, 2)]

theorem rawRowCheck2990 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form13 = rawRow2990 := by decide +kernel

def row2990 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

theorem rowCheck2990 : row2990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2990 := by decide +kernel

theorem rowEval2990 (x : Key → ℝ) : Integer.Sparse.eval row2990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2990, Integer.Sparse.eval_collectBalanced, rawRowCheck2990]

def rawRow2991 : Integer.Sparse Key := [(key2268, -2), (key2272, -2), (key2268, -2), (key2294, 6), (key1999, 2), (key2003, 2), (key1999, 2), (key2336, -2), (key2294, -2), (key2336, -2), (key2003, -6), (key2324, 2), (key2272, 2), (key2324, 2)]

theorem rawRowCheck2991 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form13 = rawRow2991 := by decide +kernel

def row2991 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

theorem rowCheck2991 : row2991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2991 := by decide +kernel

theorem rowEval2991 (x : Key → ℝ) : Integer.Sparse.eval row2991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2991, Integer.Sparse.eval_collectBalanced, rawRowCheck2991]

def rawRow2992 : Integer.Sparse Key := [(key2272, -2), (key2268, -2), (key2268, -2), (key2294, 6), (key2003, 2), (key1999, 2), (key1999, 2), (key2336, -2), (key2336, -2), (key2294, -2), (key2003, -6), (key2324, 2), (key2324, 2), (key2272, 2)]

theorem rawRowCheck2992 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form13 = rawRow2992 := by decide +kernel

def row2992 : Integer.Sparse Key := [(key1999, 4), (key2003, -4), (key2268, -4), (key2294, 4), (key2324, 4), (key2336, -4)]

theorem rowCheck2992 : row2992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2992 := by decide +kernel

theorem rowEval2992 (x : Key → ℝ) : Integer.Sparse.eval row2992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2992, Integer.Sparse.eval_collectBalanced, rawRowCheck2992]

def rawRow2993 : Integer.Sparse Key := [(key2268, -2), (key2272, -2), (key2294, -2), (key2268, 6), (key2323, 2), (key2324, 2), (key2336, 2), (key1999, -2), (key2268, -2), (key2323, -2), (key2324, -6), (key2003, 2), (key2272, 2), (key2324, 2)]

theorem rawRowCheck2993 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form13 = rawRow2993 := by decide +kernel

def row2993 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

theorem rowCheck2993 : row2993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2993 := by decide +kernel

theorem rowEval2993 (x : Key → ℝ) : Integer.Sparse.eval row2993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2993, Integer.Sparse.eval_collectBalanced, rawRowCheck2993]

def rawRow2994 : Integer.Sparse Key := [(key2272, -2), (key2268, -2), (key2294, -2), (key2268, 6), (key2324, 2), (key2323, 2), (key2336, 2), (key1999, -2), (key2323, -2), (key2268, -2), (key2324, -6), (key2003, 2), (key2324, 2), (key2272, 2)]

theorem rawRowCheck2994 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form13 = rawRow2994 := by decide +kernel

def row2994 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

theorem rowCheck2994 : row2994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2994 := by decide +kernel

theorem rowEval2994 (x : Key → ℝ) : Integer.Sparse.eval row2994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2994, Integer.Sparse.eval_collectBalanced, rawRowCheck2994]

def rawRow2995 : Integer.Sparse Key := [(key2268, -2), (key2294, -2), (key2272, -2), (key2268, 6), (key2323, 2), (key2336, 2), (key2324, 2), (key2268, -2), (key1999, -2), (key2323, -2), (key2324, -6), (key2272, 2), (key2003, 2), (key2324, 2)]

theorem rawRowCheck2995 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form13 = rawRow2995 := by decide +kernel

def row2995 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

theorem rowCheck2995 : row2995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2995 := by decide +kernel

theorem rowEval2995 (x : Key → ℝ) : Integer.Sparse.eval row2995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2995, Integer.Sparse.eval_collectBalanced, rawRowCheck2995]

def rawRow2996 : Integer.Sparse Key := [(key2294, -2), (key2268, -2), (key2272, -2), (key2268, 6), (key2336, 2), (key2323, 2), (key2324, 2), (key2268, -2), (key2323, -2), (key1999, -2), (key2324, -6), (key2272, 2), (key2324, 2), (key2003, 2)]

theorem rawRowCheck2996 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form13 = rawRow2996 := by decide +kernel

def row2996 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

theorem rowCheck2996 : row2996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2996 := by decide +kernel

theorem rowEval2996 (x : Key → ℝ) : Integer.Sparse.eval row2996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form13) x := by
  rw [rowCheck2996, Integer.Sparse.eval_collectBalanced, rawRowCheck2996]

def rawRow2997 : Integer.Sparse Key := [(key2272, -2), (key2294, -2), (key2268, -2), (key2268, 6), (key2324, 2), (key2336, 2), (key2323, 2), (key2323, -2), (key1999, -2), (key2268, -2), (key2324, -6), (key2324, 2), (key2003, 2), (key2272, 2)]

theorem rawRowCheck2997 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form13 = rawRow2997 := by decide +kernel

def row2997 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

theorem rowCheck2997 : row2997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2997 := by decide +kernel

theorem rowEval2997 (x : Key → ℝ) : Integer.Sparse.eval row2997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2997, Integer.Sparse.eval_collectBalanced, rawRowCheck2997]

def rawRow2998 : Integer.Sparse Key := [(key2294, -2), (key2272, -2), (key2268, -2), (key2268, 6), (key2336, 2), (key2324, 2), (key2323, 2), (key2323, -2), (key2268, -2), (key1999, -2), (key2324, -6), (key2324, 2), (key2272, 2), (key2003, 2)]

theorem rawRowCheck2998 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form13 = rawRow2998 := by decide +kernel

def row2998 : Integer.Sparse Key := [(key1999, -2), (key2003, 2), (key2268, 2), (key2294, -2), (key2324, -2), (key2336, 2)]

theorem rowCheck2998 : row2998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2998 := by decide +kernel

theorem rowEval2998 (x : Key → ℝ) : Integer.Sparse.eval row2998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form13) x := by
  rw [rowCheck2998, Integer.Sparse.eval_collectBalanced, rawRowCheck2998]

def rawRow2999 : Integer.Sparse Key := [(key2323, -2), (key2324, -2), (key2324, -2), (key2336, 6), (key1999, 2), (key2003, 2), (key2003, 2), (key2294, -2), (key2294, -2), (key2336, -2), (key1999, -6), (key2268, 2), (key2268, 2), (key2323, 2)]

theorem rawRowCheck2999 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form13 = rawRow2999 := by decide +kernel

def row2999 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

theorem rowCheck2999 : row2999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2999 := by decide +kernel

theorem rowEval2999 (x : Key → ℝ) : Integer.Sparse.eval row2999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2999, Integer.Sparse.eval_collectBalanced, rawRowCheck2999]

def rawRow3000 : Integer.Sparse Key := [(key2324, -2), (key2323, -2), (key2324, -2), (key2336, 6), (key2003, 2), (key1999, 2), (key2003, 2), (key2294, -2), (key2336, -2), (key2294, -2), (key1999, -6), (key2268, 2), (key2323, 2), (key2268, 2)]

theorem rawRowCheck3000 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form13 = rawRow3000 := by decide +kernel

def row3000 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

theorem rowCheck3000 : row3000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3000 := by decide +kernel

theorem rowEval3000 (x : Key → ℝ) : Integer.Sparse.eval row3000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3000, Integer.Sparse.eval_collectBalanced, rawRowCheck3000]

def rawRow3001 : Integer.Sparse Key := [(key2324, -2), (key2324, -2), (key2323, -2), (key2336, 6), (key2003, 2), (key2003, 2), (key1999, 2), (key2336, -2), (key2294, -2), (key2294, -2), (key1999, -6), (key2323, 2), (key2268, 2), (key2268, 2)]

theorem rawRowCheck3001 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form13 = rawRow3001 := by decide +kernel

def row3001 : Integer.Sparse Key := [(key1999, -4), (key2003, 4), (key2268, 4), (key2294, -4), (key2324, -4), (key2336, 4)]

theorem rowCheck3001 : row3001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3001 := by decide +kernel

theorem rowEval3001 (x : Key → ℝ) : Integer.Sparse.eval row3001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3001, Integer.Sparse.eval_collectBalanced, rawRowCheck3001]

def rawRow3002 : Integer.Sparse Key := [(key2323, -2), (key2324, -2), (key2336, -2), (key2324, 6), (key2268, 2), (key2272, 2), (key2294, 2), (key2003, -2), (key2272, -2), (key2324, -2), (key2268, -6), (key1999, 2), (key2268, 2), (key2323, 2)]

theorem rawRowCheck3002 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form13 = rawRow3002 := by decide +kernel

def row3002 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

theorem rowCheck3002 : row3002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3002 := by decide +kernel

theorem rowEval3002 (x : Key → ℝ) : Integer.Sparse.eval row3002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3002, Integer.Sparse.eval_collectBalanced, rawRowCheck3002]

def rawRow3003 : Integer.Sparse Key := [(key2324, -2), (key2323, -2), (key2336, -2), (key2324, 6), (key2272, 2), (key2268, 2), (key2294, 2), (key2003, -2), (key2324, -2), (key2272, -2), (key2268, -6), (key1999, 2), (key2323, 2), (key2268, 2)]

theorem rawRowCheck3003 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form13 = rawRow3003 := by decide +kernel

def row3003 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

theorem rowCheck3003 : row3003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3003 := by decide +kernel

theorem rowEval3003 (x : Key → ℝ) : Integer.Sparse.eval row3003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3003, Integer.Sparse.eval_collectBalanced, rawRowCheck3003]

def rawRow3004 : Integer.Sparse Key := [(key2323, -2), (key2336, -2), (key2324, -2), (key2324, 6), (key2268, 2), (key2294, 2), (key2272, 2), (key2272, -2), (key2003, -2), (key2324, -2), (key2268, -6), (key2268, 2), (key1999, 2), (key2323, 2)]

theorem rawRowCheck3004 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form13 = rawRow3004 := by decide +kernel

def row3004 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

theorem rowCheck3004 : row3004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3004 := by decide +kernel

theorem rowEval3004 (x : Key → ℝ) : Integer.Sparse.eval row3004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3004, Integer.Sparse.eval_collectBalanced, rawRowCheck3004]

def rawRow3005 : Integer.Sparse Key := [(key2336, -2), (key2323, -2), (key2324, -2), (key2324, 6), (key2294, 2), (key2268, 2), (key2272, 2), (key2272, -2), (key2324, -2), (key2003, -2), (key2268, -6), (key2268, 2), (key2323, 2), (key1999, 2)]

theorem rawRowCheck3005 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form13 = rawRow3005 := by decide +kernel

def row3005 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

theorem rowCheck3005 : row3005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3005 := by decide +kernel

theorem rowEval3005 (x : Key → ℝ) : Integer.Sparse.eval row3005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form13) x := by
  rw [rowCheck3005, Integer.Sparse.eval_collectBalanced, rawRowCheck3005]

def rawRow3006 : Integer.Sparse Key := [(key2324, -2), (key2336, -2), (key2323, -2), (key2324, 6), (key2272, 2), (key2294, 2), (key2268, 2), (key2324, -2), (key2003, -2), (key2272, -2), (key2268, -6), (key2323, 2), (key1999, 2), (key2268, 2)]

theorem rawRowCheck3006 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form13 = rawRow3006 := by decide +kernel

def row3006 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

theorem rowCheck3006 : row3006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3006 := by decide +kernel

theorem rowEval3006 (x : Key → ℝ) : Integer.Sparse.eval row3006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3006, Integer.Sparse.eval_collectBalanced, rawRowCheck3006]

def rawRow3007 : Integer.Sparse Key := [(key2336, -2), (key2324, -2), (key2323, -2), (key2324, 6), (key2294, 2), (key2272, 2), (key2268, 2), (key2324, -2), (key2272, -2), (key2003, -2), (key2268, -6), (key2323, 2), (key2268, 2), (key1999, 2)]

theorem rawRowCheck3007 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form13 = rawRow3007 := by decide +kernel

def row3007 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2268, -2), (key2294, 2), (key2324, 2), (key2336, -2)]

theorem rowCheck3007 : row3007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3007 := by decide +kernel

theorem rowEval3007 (x : Key → ℝ) : Integer.Sparse.eval row3007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form13) x := by
  rw [rowCheck3007, Integer.Sparse.eval_collectBalanced, rawRowCheck3007]

def rawRow3008 : Integer.Sparse Key := [(key2362, -2), (key2365, -2), (key2365, -2), (key2365, 2), (key2365, 2), (key2367, 2), (key2457, 2), (key2460, 2), (key2460, 2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2525, -1), (key2532, -2), (key2532, -2), (key2533, -2), (key2532, 1), (key2532, 1), (key2562, 1), (key2562, 1), (key2564, 1), (key2564, 1)]

theorem rawRowCheck3008 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form14 = rawRow3008 := by decide +kernel

def row3008 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2)]

theorem rowCheck3008 : row3008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3008 := by decide +kernel

theorem rowEval3008 (x : Key → ℝ) : Integer.Sparse.eval row3008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3008, Integer.Sparse.eval_collectBalanced, rawRowCheck3008]

def rawRow3009 : Integer.Sparse Key := [(key2365, -2), (key2362, -2), (key2365, -2), (key2365, 2), (key2367, 2), (key2365, 2), (key2460, 2), (key2457, 2), (key2460, 2), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2532, -2), (key2533, -2), (key2532, -2), (key2562, 1), (key2564, 1), (key2532, 1), (key2564, 1), (key2532, 1), (key2562, 1)]

theorem rawRowCheck3009 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form14 = rawRow3009 := by decide +kernel

def row3009 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2)]

theorem rowCheck3009 : row3009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3009 := by decide +kernel

theorem rowEval3009 (x : Key → ℝ) : Integer.Sparse.eval row3009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3009, Integer.Sparse.eval_collectBalanced, rawRowCheck3009]

def rawRow3010 : Integer.Sparse Key := [(key2365, -2), (key2365, -2), (key2362, -2), (key2367, 2), (key2365, 2), (key2365, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2460, -1), (key2533, -2), (key2532, -2), (key2532, -2), (key2564, 1), (key2562, 1), (key2564, 1), (key2532, 1), (key2562, 1), (key2532, 1)]

theorem rawRowCheck3010 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form14 = rawRow3010 := by decide +kernel

def row3010 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2)]

theorem rowCheck3010 : row3010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3010 := by decide +kernel

theorem rowEval3010 (x : Key → ℝ) : Integer.Sparse.eval row3010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3010, Integer.Sparse.eval_collectBalanced, rawRowCheck3010]

def rawRow3011 : Integer.Sparse Key := [(key2365, -2), (key2365, -2), (key2367, -2), (key2362, 2), (key2365, 2), (key2365, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2562, -2), (key2564, -2), (key2564, -2), (key2532, 1), (key2533, 1), (key2532, 1), (key2564, 1), (key2533, 1), (key2564, 1)]

theorem rawRowCheck3011 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form14 = rawRow3011 := by decide +kernel

def row3011 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2)]

theorem rowCheck3011 : row3011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3011 := by decide +kernel

theorem rowEval3011 (x : Key → ℝ) : Integer.Sparse.eval row3011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3011, Integer.Sparse.eval_collectBalanced, rawRowCheck3011]

def rawRow3012 : Integer.Sparse Key := [(key2365, -2), (key2367, -2), (key2365, -2), (key2365, 2), (key2362, 2), (key2365, 2), (key2521, 2), (key2525, 2), (key2521, 2), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2564, -2), (key2562, -2), (key2564, -2), (key2533, 1), (key2532, 1), (key2564, 1), (key2532, 1), (key2564, 1), (key2533, 1)]

theorem rawRowCheck3012 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form14 = rawRow3012 := by decide +kernel

def row3012 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2)]

theorem rowCheck3012 : row3012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3012 := by decide +kernel

theorem rowEval3012 (x : Key → ℝ) : Integer.Sparse.eval row3012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3012, Integer.Sparse.eval_collectBalanced, rawRowCheck3012]

def rawRow3013 : Integer.Sparse Key := [(key2367, -2), (key2365, -2), (key2365, -2), (key2365, 2), (key2365, 2), (key2362, 2), (key2525, 2), (key2521, 2), (key2521, 2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2457, -1), (key2564, -2), (key2564, -2), (key2562, -2), (key2564, 1), (key2564, 1), (key2533, 1), (key2533, 1), (key2532, 1), (key2532, 1)]

theorem rawRowCheck3013 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form14 = rawRow3013 := by decide +kernel

def row3013 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2)]

theorem rowCheck3013 : row3013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3013 := by decide +kernel

theorem rowEval3013 (x : Key → ℝ) : Integer.Sparse.eval row3013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3013, Integer.Sparse.eval_collectBalanced, rawRowCheck3013]

def rawRow3014 : Integer.Sparse Key := [(key2457, -2), (key2460, -2), (key2460, -2), (key2521, 2), (key2521, 2), (key2525, 2), (key2362, 2), (key2365, 2), (key2365, 2), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, -1), (key2564, -1), (key2365, -2), (key2365, -2), (key2367, -2), (key2460, 1), (key2460, 1), (key2521, 1), (key2521, 1), (key2525, 1), (key2525, 1)]

theorem rawRowCheck3014 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form14 = rawRow3014 := by decide +kernel

def row3014 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 6), (key2525, 4), (key2532, -2), (key2562, -2), (key2564, -2)]

theorem rowCheck3014 : row3014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3014 := by decide +kernel

theorem rowEval3014 (x : Key → ℝ) : Integer.Sparse.eval row3014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3014, Integer.Sparse.eval_collectBalanced, rawRowCheck3014]

def rawRow3015 : Integer.Sparse Key := [(key2460, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2521, 2), (key2365, 2), (key2362, 2), (key2365, 2), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2365, -2), (key2367, -2), (key2365, -2), (key2521, 1), (key2525, 1), (key2460, 1), (key2525, 1), (key2460, 1), (key2521, 1)]

theorem rawRowCheck3015 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form14 = rawRow3015 := by decide +kernel

def row3015 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 6), (key2525, 4), (key2532, -2), (key2562, -2), (key2564, -2)]

theorem rowCheck3015 : row3015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3015 := by decide +kernel

theorem rowEval3015 (x : Key → ℝ) : Integer.Sparse.eval row3015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3015, Integer.Sparse.eval_collectBalanced, rawRowCheck3015]

def rawRow3016 : Integer.Sparse Key := [(key2460, -2), (key2460, -2), (key2457, -2), (key2525, 2), (key2521, 2), (key2521, 2), (key2365, 2), (key2365, 2), (key2362, 2), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2532, -1), (key2367, -2), (key2365, -2), (key2365, -2), (key2525, 1), (key2521, 1), (key2525, 1), (key2460, 1), (key2521, 1), (key2460, 1)]

theorem rawRowCheck3016 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form14 = rawRow3016 := by decide +kernel

def row3016 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, -2), (key2460, -2), (key2521, 6), (key2525, 4), (key2532, -2), (key2562, -2), (key2564, -2)]

theorem rowCheck3016 : row3016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3016 := by decide +kernel

theorem rowEval3016 (x : Key → ℝ) : Integer.Sparse.eval row3016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3016, Integer.Sparse.eval_collectBalanced, rawRowCheck3016]

def rawRow3017 : Integer.Sparse Key := [(key2460, -2), (key2521, -2), (key2525, -2), (key2457, 2), (key2460, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2564, 2), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2521, -2), (key2525, -2), (key2564, -2), (key2365, 1), (key2367, 1), (key2460, 1), (key2525, 1), (key2533, 1), (key2564, 1)]

theorem rawRowCheck3017 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form14 = rawRow3017 := by decide +kernel

def row3017 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

theorem rowCheck3017 : row3017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3017 := by decide +kernel

theorem rowEval3017 (x : Key → ℝ) : Integer.Sparse.eval row3017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3017, Integer.Sparse.eval_collectBalanced, rawRowCheck3017]

def rawRow3018 : Integer.Sparse Key := [(key2460, -2), (key2525, -2), (key2521, -2), (key2460, 2), (key2457, 2), (key2521, 2), (key2532, 2), (key2564, 2), (key2562, 2), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2532, -1), (key2525, -2), (key2521, -2), (key2564, -2), (key2367, 1), (key2365, 1), (key2525, 1), (key2460, 1), (key2564, 1), (key2533, 1)]

theorem rawRowCheck3018 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form14 = rawRow3018 := by decide +kernel

def row3018 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

theorem rowCheck3018 : row3018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3018 := by decide +kernel

theorem rowEval3018 (x : Key → ℝ) : Integer.Sparse.eval row3018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3018, Integer.Sparse.eval_collectBalanced, rawRowCheck3018]

def rawRow3019 : Integer.Sparse Key := [(key2521, -2), (key2460, -2), (key2525, -2), (key2457, 2), (key2521, 2), (key2460, 2), (key2562, 2), (key2532, 2), (key2564, 2), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, 1), (key2533, 1), (key2365, 1), (key2564, 1), (key2367, 1), (key2525, 1)]

theorem rawRowCheck3019 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form14 = rawRow3019 := by decide +kernel

def row3019 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -4), (key2525, -3), (key2532, 2), (key2533, 1), (key2562, 1), (key2564, 1)]

theorem rowCheck3019 : row3019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3019 := by decide +kernel

theorem rowEval3019 (x : Key → ℝ) : Integer.Sparse.eval row3019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3019, Integer.Sparse.eval_collectBalanced, rawRowCheck3019]

def rawRow3020 : Integer.Sparse Key := [(key2521, -2), (key2525, -2), (key2460, -2), (key2521, 2), (key2457, 2), (key2460, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, -1), (key2365, -1), (key2564, -2), (key2521, -2), (key2525, -2), (key2533, 1), (key2460, 1), (key2564, 1), (key2365, 1), (key2525, 1), (key2367, 1)]

theorem rawRowCheck3020 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form14 = rawRow3020 := by decide +kernel

def row3020 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -4), (key2525, -3), (key2532, 2), (key2533, 1), (key2562, 1), (key2564, 1)]

theorem rowCheck3020 : row3020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3020 := by decide +kernel

theorem rowEval3020 (x : Key → ℝ) : Integer.Sparse.eval row3020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form14) x := by
  rw [rowCheck3020, Integer.Sparse.eval_collectBalanced, rawRowCheck3020]

def rawRow3021 : Integer.Sparse Key := [(key2525, -2), (key2460, -2), (key2521, -2), (key2460, 2), (key2521, 2), (key2457, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, -1), (key2457, -1), (key2525, -2), (key2564, -2), (key2521, -2), (key2525, 1), (key2564, 1), (key2367, 1), (key2533, 1), (key2365, 1), (key2460, 1)]

theorem rawRowCheck3021 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form14 = rawRow3021 := by decide +kernel

def row3021 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

theorem rowCheck3021 : row3021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3021 := by decide +kernel

theorem rowEval3021 (x : Key → ℝ) : Integer.Sparse.eval row3021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3021, Integer.Sparse.eval_collectBalanced, rawRowCheck3021]

def rawRow3022 : Integer.Sparse Key := [(key2525, -2), (key2521, -2), (key2460, -2), (key2521, 2), (key2460, 2), (key2457, 2), (key2564, 2), (key2562, 2), (key2532, 2), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, -1), (key2362, -1), (key2564, -2), (key2525, -2), (key2521, -2), (key2564, 1), (key2525, 1), (key2533, 1), (key2367, 1), (key2460, 1), (key2365, 1)]

theorem rawRowCheck3022 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form14 = rawRow3022 := by decide +kernel

def row3022 : Integer.Sparse Key := [(key2362, -1), (key2367, 1), (key2457, 1), (key2460, 1), (key2521, -3), (key2525, -3), (key2532, 1), (key2533, 1), (key2562, 1), (key2564, 1)]

theorem rowCheck3022 : row3022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3022 := by decide +kernel

theorem rowEval3022 (x : Key → ℝ) : Integer.Sparse.eval row3022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form14) x := by
  rw [rowCheck3022, Integer.Sparse.eval_collectBalanced, rawRowCheck3022]

def rawRow3023 : Integer.Sparse Key := [(key2532, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2), (key2564, 2), (key2365, 2), (key2365, 2), (key2367, 2), (key2521, -1), (key2525, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2564, -1), (key2362, -2), (key2365, -2), (key2365, -2), (key2457, 1), (key2460, 1), (key2457, 1), (key2521, 1), (key2460, 1), (key2521, 1)]

theorem rawRowCheck3023 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form14 = rawRow3023 := by decide +kernel

def row3023 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2525, -2), (key2532, -4), (key2533, -2), (key2562, 2), (key2564, 2)]

theorem rowCheck3023 : row3023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3023 := by decide +kernel

theorem rowEval3023 (x : Key → ℝ) : Integer.Sparse.eval row3023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3023, Integer.Sparse.eval_collectBalanced, rawRowCheck3023]

def rawRow3024 : Integer.Sparse Key := [(key2532, -2), (key2533, -2), (key2532, -2), (key2564, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2367, 2), (key2365, 2), (key2525, -1), (key2521, -1), (key2564, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2365, -2), (key2362, -2), (key2365, -2), (key2460, 1), (key2457, 1), (key2521, 1), (key2457, 1), (key2521, 1), (key2460, 1)]

theorem rawRowCheck3024 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form14 = rawRow3024 := by decide +kernel

def row3024 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2525, -2), (key2532, -4), (key2533, -2), (key2562, 2), (key2564, 2)]

theorem rowCheck3024 : row3024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3024 := by decide +kernel

theorem rowEval3024 (x : Key → ℝ) : Integer.Sparse.eval row3024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3024, Integer.Sparse.eval_collectBalanced, rawRowCheck3024]

def rawRow3025 : Integer.Sparse Key := [(key2533, -2), (key2532, -2), (key2532, -2), (key2564, 2), (key2564, 2), (key2562, 2), (key2367, 2), (key2365, 2), (key2365, 2), (key2564, -1), (key2564, -1), (key2525, -1), (key2525, -1), (key2521, -1), (key2521, -1), (key2365, -2), (key2365, -2), (key2362, -2), (key2521, 1), (key2521, 1), (key2460, 1), (key2460, 1), (key2457, 1), (key2457, 1)]

theorem rawRowCheck3025 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form14 = rawRow3025 := by decide +kernel

def row3025 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, 2), (key2460, 2), (key2525, -2), (key2532, -4), (key2533, -2), (key2562, 2), (key2564, 2)]

theorem rowCheck3025 : row3025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3025 := by decide +kernel

theorem rowEval3025 (x : Key → ℝ) : Integer.Sparse.eval row3025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3025, Integer.Sparse.eval_collectBalanced, rawRowCheck3025]

def rawRow3026 : Integer.Sparse Key := [(key2532, -2), (key2562, -2), (key2564, -2), (key2532, 2), (key2533, 2), (key2564, 2), (key2460, 2), (key2521, 2), (key2525, 2), (key2365, -1), (key2367, -1), (key2460, -1), (key2533, -1), (key2525, -1), (key2564, -1), (key2457, -2), (key2460, -2), (key2521, -2), (key2362, 1), (key2365, 1), (key2457, 1), (key2521, 1), (key2532, 1), (key2562, 1)]

theorem rawRowCheck3026 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form14 = rawRow3026 := by decide +kernel

def row3026 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

theorem rowCheck3026 : row3026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3026 := by decide +kernel

theorem rowEval3026 (x : Key → ℝ) : Integer.Sparse.eval row3026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3026, Integer.Sparse.eval_collectBalanced, rawRowCheck3026]

def rawRow3027 : Integer.Sparse Key := [(key2532, -2), (key2564, -2), (key2562, -2), (key2533, 2), (key2532, 2), (key2564, 2), (key2460, 2), (key2525, 2), (key2521, 2), (key2367, -1), (key2365, -1), (key2533, -1), (key2460, -1), (key2564, -1), (key2525, -1), (key2460, -2), (key2457, -2), (key2521, -2), (key2365, 1), (key2362, 1), (key2521, 1), (key2457, 1), (key2562, 1), (key2532, 1)]

theorem rawRowCheck3027 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form14 = rawRow3027 := by decide +kernel

def row3027 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

theorem rowCheck3027 : row3027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3027 := by decide +kernel

theorem rowEval3027 (x : Key → ℝ) : Integer.Sparse.eval row3027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3027, Integer.Sparse.eval_collectBalanced, rawRowCheck3027]

def rawRow3028 : Integer.Sparse Key := [(key2562, -2), (key2532, -2), (key2564, -2), (key2532, 2), (key2564, 2), (key2533, 2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, -1), (key2525, -1), (key2365, -1), (key2564, -1), (key2367, -1), (key2533, -1), (key2457, -2), (key2521, -2), (key2460, -2), (key2457, 1), (key2521, 1), (key2362, 1), (key2562, 1), (key2365, 1), (key2521, 1)]

theorem rawRowCheck3028 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form14 = rawRow3028 := by decide +kernel

def row3028 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 2), (key2525, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

theorem rowCheck3028 : row3028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3028 := by decide +kernel

theorem rowEval3028 (x : Key → ℝ) : Integer.Sparse.eval row3028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3028, Integer.Sparse.eval_collectBalanced, rawRowCheck3028]

def rawRow3029 : Integer.Sparse Key := [(key2562, -2), (key2564, -2), (key2532, -2), (key2564, 2), (key2532, 2), (key2533, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2533, -1), (key2367, -1), (key2521, -2), (key2457, -2), (key2460, -2), (key2521, 1), (key2457, 1), (key2562, 1), (key2362, 1), (key2521, 1), (key2365, 1)]

theorem rawRowCheck3029 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form14 = rawRow3029 := by decide +kernel

def row3029 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 2), (key2525, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

theorem rowCheck3029 : row3029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3029 := by decide +kernel

theorem rowEval3029 (x : Key → ℝ) : Integer.Sparse.eval row3029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form14) x := by
  rw [rowCheck3029, Integer.Sparse.eval_collectBalanced, rawRowCheck3029]

def rawRow3030 : Integer.Sparse Key := [(key2564, -2), (key2532, -2), (key2562, -2), (key2533, 2), (key2564, 2), (key2532, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2533, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2365, -1), (key2460, -1), (key2460, -2), (key2521, -2), (key2457, -2), (key2532, 1), (key2562, 1), (key2365, 1), (key2521, 1), (key2362, 1), (key2457, 1)]

theorem rawRowCheck3030 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form14 = rawRow3030 := by decide +kernel

def row3030 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

theorem rowCheck3030 : row3030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3030 := by decide +kernel

theorem rowEval3030 (x : Key → ℝ) : Integer.Sparse.eval row3030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3030, Integer.Sparse.eval_collectBalanced, rawRowCheck3030]

def rawRow3031 : Integer.Sparse Key := [(key2564, -2), (key2562, -2), (key2532, -2), (key2564, 2), (key2533, 2), (key2532, 2), (key2525, 2), (key2521, 2), (key2460, 2), (key2564, -1), (key2533, -1), (key2525, -1), (key2367, -1), (key2460, -1), (key2365, -1), (key2521, -2), (key2460, -2), (key2457, -2), (key2562, 1), (key2532, 1), (key2521, 1), (key2365, 1), (key2457, 1), (key2362, 1)]

theorem rawRowCheck3031 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form14 = rawRow3031 := by decide +kernel

def row3031 : Integer.Sparse Key := [(key2362, 1), (key2367, -1), (key2457, -1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, 1), (key2533, 1), (key2562, -1), (key2564, -1)]

theorem rowCheck3031 : row3031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3031 := by decide +kernel

theorem rowEval3031 (x : Key → ℝ) : Integer.Sparse.eval row3031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form14) x := by
  rw [rowCheck3031, Integer.Sparse.eval_collectBalanced, rawRowCheck3031]

def rawRow3032 : Integer.Sparse Key := [(key2621, -2), (key2835, -2), (key2835, -2), (key2616, 1), (key2616, 1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2641, 2), (key2976, 2), (key2976, 2), (key2628, -1), (key2628, -1), (key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2653, -1), (key2653, -1), (key2897, -1), (key2897, -1), (key2998, -1), (key2998, -1), (key2648, 1), (key2648, 1), (key2737, 1), (key2737, 1), (key2997, 1), (key2997, 1)]

theorem rawRowCheck3032 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form0 = rawRow3032 := by decide +kernel

def row3032 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2737, 2), (key2809, 2), (key2829, 2), (key2835, -4), (key2897, -2), (key2972, -2), (key2976, 4), (key2997, 2), (key2998, -2)]

theorem rowCheck3032 : row3032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3032 := by decide +kernel

theorem rowEval3032 (x : Key → ℝ) : Integer.Sparse.eval row3032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3032, Integer.Sparse.eval_collectBalanced, rawRowCheck3032]

def rawRow3033 : Integer.Sparse Key := [(key2835, -2), (key2621, -2), (key2835, -2), (key2809, 1), (key2829, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2976, 2), (key2641, 2), (key2976, 2), (key2702, -1), (key2972, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2897, -1), (key2998, -1), (key2653, -1), (key2998, -1), (key2653, -1), (key2897, -1), (key2737, 1), (key2997, 1), (key2648, 1), (key2997, 1), (key2648, 1), (key2737, 1)]

theorem rawRowCheck3033 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form0 = rawRow3033 := by decide +kernel

def row3033 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2737, 2), (key2809, 2), (key2829, 2), (key2835, -4), (key2897, -2), (key2972, -2), (key2976, 4), (key2997, 2), (key2998, -2)]

theorem rowCheck3033 : row3033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3033 := by decide +kernel

theorem rowEval3033 (x : Key → ℝ) : Integer.Sparse.eval row3033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3033, Integer.Sparse.eval_collectBalanced, rawRowCheck3033]

def rawRow3034 : Integer.Sparse Key := [(key2835, -2), (key2835, -2), (key2621, -2), (key2829, 1), (key2809, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2616, 1), (key2976, 2), (key2976, 2), (key2641, 2), (key2972, -1), (key2702, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2628, -1), (key2998, -1), (key2897, -1), (key2998, -1), (key2653, -1), (key2897, -1), (key2653, -1), (key2997, 1), (key2737, 1), (key2997, 1), (key2648, 1), (key2737, 1), (key2648, 1)]

theorem rawRowCheck3034 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form0 = rawRow3034 := by decide +kernel

def row3034 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2737, 2), (key2809, 2), (key2829, 2), (key2835, -4), (key2897, -2), (key2972, -2), (key2976, 4), (key2997, 2), (key2998, -2)]

theorem rowCheck3034 : row3034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3034 := by decide +kernel

theorem rowEval3034 (x : Key → ℝ) : Integer.Sparse.eval row3034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3034, Integer.Sparse.eval_collectBalanced, rawRowCheck3034]

def rawRow3035 : Integer.Sparse Key := [(key2644, -2), (key2732, -2), (key2885, -2), (key2632, 1), (key2640, 1), (key2706, 1), (key2860, 1), (key2726, 1), (key2870, 1), (key2660, 2), (key2758, 2), (key2927, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2641, -1), (key2653, -1), (key2795, -1), (key2897, -1), (key2943, -1), (key2976, -1), (key2618, 1), (key2648, 1), (key2673, 1), (key2737, 1), (key2938, 1), (key2950, 1)]

theorem rawRowCheck3035 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form0 = rawRow3035 := by decide +kernel

def row3035 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

theorem rowCheck3035 : row3035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3035 := by decide +kernel

theorem rowEval3035 (x : Key → ℝ) : Integer.Sparse.eval row3035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3035, Integer.Sparse.eval_collectBalanced, rawRowCheck3035]

def rawRow3036 : Integer.Sparse Key := [(key2644, -2), (key2885, -2), (key2732, -2), (key2640, 1), (key2632, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2726, 1), (key2660, 2), (key2927, 2), (key2758, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2653, -1), (key2641, -1), (key2897, -1), (key2795, -1), (key2976, -1), (key2943, -1), (key2648, 1), (key2618, 1), (key2737, 1), (key2673, 1), (key2950, 1), (key2938, 1)]

theorem rawRowCheck3036 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form0 = rawRow3036 := by decide +kernel

def row3036 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

theorem rowCheck3036 : row3036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3036 := by decide +kernel

theorem rowEval3036 (x : Key → ℝ) : Integer.Sparse.eval row3036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3036, Integer.Sparse.eval_collectBalanced, rawRowCheck3036]

def rawRow3037 : Integer.Sparse Key := [(key2732, -2), (key2644, -2), (key2885, -2), (key2706, 1), (key2726, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2758, 2), (key2660, 2), (key2927, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2795, -1), (key2943, -1), (key2641, -1), (key2976, -1), (key2653, -1), (key2897, -1), (key2673, 1), (key2938, 1), (key2618, 1), (key2950, 1), (key2648, 1), (key2737, 1)]

theorem rawRowCheck3037 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form0 = rawRow3037 := by decide +kernel

def row3037 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

theorem rowCheck3037 : row3037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3037 := by decide +kernel

theorem rowEval3037 (x : Key → ℝ) : Integer.Sparse.eval row3037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3037, Integer.Sparse.eval_collectBalanced, rawRowCheck3037]

def rawRow3038 : Integer.Sparse Key := [(key2732, -2), (key2885, -2), (key2644, -2), (key2726, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2860, 1), (key2640, 1), (key2758, 2), (key2927, 2), (key2660, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2943, -1), (key2795, -1), (key2976, -1), (key2641, -1), (key2897, -1), (key2653, -1), (key2938, 1), (key2673, 1), (key2950, 1), (key2618, 1), (key2737, 1), (key2648, 1)]

theorem rawRowCheck3038 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form0 = rawRow3038 := by decide +kernel

def row3038 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

theorem rowCheck3038 : row3038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3038 := by decide +kernel

theorem rowEval3038 (x : Key → ℝ) : Integer.Sparse.eval row3038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3038, Integer.Sparse.eval_collectBalanced, rawRowCheck3038]

def rawRow3039 : Integer.Sparse Key := [(key2885, -2), (key2644, -2), (key2732, -2), (key2860, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2632, 1), (key2706, 1), (key2927, 2), (key2660, 2), (key2758, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2897, -1), (key2976, -1), (key2653, -1), (key2943, -1), (key2641, -1), (key2795, -1), (key2737, 1), (key2950, 1), (key2648, 1), (key2938, 1), (key2618, 1), (key2673, 1)]

theorem rawRowCheck3039 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form0 = rawRow3039 := by decide +kernel

def row3039 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

theorem rowCheck3039 : row3039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3039 := by decide +kernel

theorem rowEval3039 (x : Key → ℝ) : Integer.Sparse.eval row3039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3039, Integer.Sparse.eval_collectBalanced, rawRowCheck3039]

def rawRow3040 : Integer.Sparse Key := [(key2885, -2), (key2732, -2), (key2644, -2), (key2870, 1), (key2860, 1), (key2726, 1), (key2640, 1), (key2706, 1), (key2632, 1), (key2927, 2), (key2758, 2), (key2660, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2976, -1), (key2897, -1), (key2943, -1), (key2653, -1), (key2795, -1), (key2641, -1), (key2950, 1), (key2737, 1), (key2938, 1), (key2648, 1), (key2673, 1), (key2618, 1)]

theorem rawRowCheck3040 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form0 = rawRow3040 := by decide +kernel

def row3040 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

theorem rowCheck3040 : row3040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3040 := by decide +kernel

theorem rowEval3040 (x : Key → ℝ) : Integer.Sparse.eval row3040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3040, Integer.Sparse.eval_collectBalanced, rawRowCheck3040]

def rawRow3041 : Integer.Sparse Key := [(key2658, -2), (key2923, -2), (key2923, -2), (key2660, 1), (key2660, 1), (key2920, 1), (key2920, 1), (key2927, 1), (key2927, 1), (key2621, 2), (key2835, 2), (key2835, 2), (key2644, -1), (key2644, -1), (key2798, -1), (key2798, -1), (key2885, -1), (key2885, -1), (key2616, -1), (key2616, -1), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

theorem rawRowCheck3041 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow3041 := by decide +kernel

def row3041 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2920, 2), (key2923, -4), (key2927, 2)]

theorem rowCheck3041 : row3041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3041 := by decide +kernel

theorem rowEval3041 (x : Key → ℝ) : Integer.Sparse.eval row3041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3041, Integer.Sparse.eval_collectBalanced, rawRowCheck3041]

def rawRow3042 : Integer.Sparse Key := [(key2923, -2), (key2658, -2), (key2923, -2), (key2920, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2920, 1), (key2835, 2), (key2621, 2), (key2835, 2), (key2798, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

theorem rawRowCheck3042 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow3042 := by decide +kernel

def row3042 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2920, 2), (key2923, -4), (key2927, 2)]

theorem rowCheck3042 : row3042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3042 := by decide +kernel

theorem rowEval3042 (x : Key → ℝ) : Integer.Sparse.eval row3042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3042, Integer.Sparse.eval_collectBalanced, rawRowCheck3042]

def rawRow3043 : Integer.Sparse Key := [(key2923, -2), (key2923, -2), (key2658, -2), (key2927, 1), (key2920, 1), (key2927, 1), (key2660, 1), (key2920, 1), (key2660, 1), (key2835, 2), (key2835, 2), (key2621, 2), (key2885, -1), (key2798, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2644, -1), (key2829, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2616, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

theorem rawRowCheck3043 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow3043 := by decide +kernel

def row3043 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2920, 2), (key2923, -4), (key2927, 2)]

theorem rowCheck3043 : row3043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3043 := by decide +kernel

theorem rowEval3043 (x : Key → ℝ) : Integer.Sparse.eval row3043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3043, Integer.Sparse.eval_collectBalanced, rawRowCheck3043]

def rawRow3044 : Integer.Sparse Key := [(key2660, -2), (key2758, -2), (key2927, -2), (key2658, 1), (key2660, 1), (key2753, 1), (key2920, 1), (key2758, 1), (key2923, 1), (key2644, 2), (key2732, 2), (key2885, 2), (key2621, -1), (key2644, -1), (key2676, -1), (key2798, -1), (key2732, -1), (key2835, -1), (key2632, -1), (key2640, -1), (key2706, -1), (key2860, -1), (key2726, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

theorem rawRowCheck3044 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form0 = rawRow3044 := by decide +kernel

def row3044 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

theorem rowCheck3044 : row3044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3044 := by decide +kernel

theorem rowEval3044 (x : Key → ℝ) : Integer.Sparse.eval row3044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3044, Integer.Sparse.eval_collectBalanced, rawRowCheck3044]

def rawRow3045 : Integer.Sparse Key := [(key2660, -2), (key2927, -2), (key2758, -2), (key2660, 1), (key2658, 1), (key2920, 1), (key2753, 1), (key2923, 1), (key2758, 1), (key2644, 2), (key2885, 2), (key2732, 2), (key2644, -1), (key2621, -1), (key2798, -1), (key2676, -1), (key2835, -1), (key2732, -1), (key2640, -1), (key2632, -1), (key2860, -1), (key2706, -1), (key2870, -1), (key2726, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

theorem rawRowCheck3045 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form0 = rawRow3045 := by decide +kernel

def row3045 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

theorem rowCheck3045 : row3045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3045 := by decide +kernel

theorem rowEval3045 (x : Key → ℝ) : Integer.Sparse.eval row3045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3045, Integer.Sparse.eval_collectBalanced, rawRowCheck3045]

def rawRow3046 : Integer.Sparse Key := [(key2758, -2), (key2660, -2), (key2927, -2), (key2753, 1), (key2758, 1), (key2658, 1), (key2923, 1), (key2660, 1), (key2920, 1), (key2732, 2), (key2644, 2), (key2885, 2), (key2676, -1), (key2732, -1), (key2621, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2706, -1), (key2726, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

theorem rawRowCheck3046 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form0 = rawRow3046 := by decide +kernel

def row3046 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

theorem rowCheck3046 : row3046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3046 := by decide +kernel

theorem rowEval3046 (x : Key → ℝ) : Integer.Sparse.eval row3046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3046, Integer.Sparse.eval_collectBalanced, rawRowCheck3046]

def rawRow3047 : Integer.Sparse Key := [(key2758, -2), (key2927, -2), (key2660, -2), (key2758, 1), (key2753, 1), (key2923, 1), (key2658, 1), (key2920, 1), (key2660, 1), (key2732, 2), (key2885, 2), (key2644, 2), (key2732, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2798, -1), (key2644, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2860, -1), (key2640, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

theorem rawRowCheck3047 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form0 = rawRow3047 := by decide +kernel

def row3047 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

theorem rowCheck3047 : row3047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3047 := by decide +kernel

theorem rowEval3047 (x : Key → ℝ) : Integer.Sparse.eval row3047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3047, Integer.Sparse.eval_collectBalanced, rawRowCheck3047]

def rawRow3048 : Integer.Sparse Key := [(key2927, -2), (key2660, -2), (key2758, -2), (key2920, 1), (key2923, 1), (key2660, 1), (key2758, 1), (key2658, 1), (key2753, 1), (key2885, 2), (key2644, 2), (key2732, 2), (key2798, -1), (key2835, -1), (key2644, -1), (key2732, -1), (key2621, -1), (key2676, -1), (key2860, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2632, -1), (key2706, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

theorem rawRowCheck3048 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form0 = rawRow3048 := by decide +kernel

def row3048 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

theorem rowCheck3048 : row3048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3048 := by decide +kernel

theorem rowEval3048 (x : Key → ℝ) : Integer.Sparse.eval row3048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3048, Integer.Sparse.eval_collectBalanced, rawRowCheck3048]

def rawRow3049 : Integer.Sparse Key := [(key2927, -2), (key2758, -2), (key2660, -2), (key2923, 1), (key2920, 1), (key2758, 1), (key2660, 1), (key2753, 1), (key2658, 1), (key2885, 2), (key2732, 2), (key2644, 2), (key2835, -1), (key2798, -1), (key2732, -1), (key2644, -1), (key2676, -1), (key2621, -1), (key2870, -1), (key2860, -1), (key2726, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

theorem rawRowCheck3049 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form0 = rawRow3049 := by decide +kernel

def row3049 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

theorem rowCheck3049 : row3049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3049 := by decide +kernel

theorem rowEval3049 (x : Key → ℝ) : Integer.Sparse.eval row3049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3049, Integer.Sparse.eval_collectBalanced, rawRowCheck3049]

def rawRow3050 : Integer.Sparse Key := [(key1471, -6), (key1384, 2), (key1417, 2), (key1417, 2), (key1902, 6), (key1289, -2), (key1566, -2), (key1566, -2), (key1895, -2), (key1917, -2), (key1917, -2), (key1350, 2), (key1680, 2), (key1680, 2)]

theorem rawRowCheck3050 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3050 := by decide +kernel

def row3050 : Integer.Sparse Key := [(key1289, -2), (key1350, 2), (key1384, 2), (key1417, 4), (key1471, -6), (key1566, -4), (key1680, 4), (key1895, -2), (key1902, 6), (key1917, -4)]

theorem rowCheck3050 : row3050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3050 := by decide +kernel

theorem rowEval3050 (x : Key → ℝ) : Integer.Sparse.eval row3050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3050, Integer.Sparse.eval_collectBalanced, rawRowCheck3050]

def rawRow3051 : Integer.Sparse Key := [(key1471, -6), (key1417, 2), (key1384, 2), (key1417, 2), (key1902, 6), (key1566, -2), (key1289, -2), (key1566, -2), (key1917, -2), (key1895, -2), (key1917, -2), (key1680, 2), (key1350, 2), (key1680, 2)]

theorem rawRowCheck3051 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3051 := by decide +kernel

def row3051 : Integer.Sparse Key := [(key1289, -2), (key1350, 2), (key1384, 2), (key1417, 4), (key1471, -6), (key1566, -4), (key1680, 4), (key1895, -2), (key1902, 6), (key1917, -4)]

theorem rowCheck3051 : row3051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3051 := by decide +kernel

theorem rowEval3051 (x : Key → ℝ) : Integer.Sparse.eval row3051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3051, Integer.Sparse.eval_collectBalanced, rawRowCheck3051]

def rawRow3052 : Integer.Sparse Key := [(key1471, -6), (key1417, 2), (key1417, 2), (key1384, 2), (key1902, 6), (key1566, -2), (key1566, -2), (key1289, -2), (key1917, -2), (key1917, -2), (key1895, -2), (key1680, 2), (key1680, 2), (key1350, 2)]

theorem rawRowCheck3052 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3052 := by decide +kernel

def row3052 : Integer.Sparse Key := [(key1289, -2), (key1350, 2), (key1384, 2), (key1417, 4), (key1471, -6), (key1566, -4), (key1680, 4), (key1895, -2), (key1902, 6), (key1917, -4)]

theorem rowCheck3052 : row3052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3052 := by decide +kernel

theorem rowEval3052 (x : Key → ℝ) : Integer.Sparse.eval row3052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3052, Integer.Sparse.eval_collectBalanced, rawRowCheck3052]

def rawRow3053 : Integer.Sparse Key := [(key1680, -6), (key1539, 2), (key1566, 2), (key1615, 2), (key1917, 6), (key1309, -2), (key1417, -2), (key1615, -2), (key1895, -2), (key1902, -2), (key1917, -2), (key1350, 2), (key1471, 2), (key1680, 2)]

theorem rawRowCheck3053 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form1 = rawRow3053 := by decide +kernel

def row3053 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

theorem rowCheck3053 : row3053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3053 := by decide +kernel

theorem rowEval3053 (x : Key → ℝ) : Integer.Sparse.eval row3053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3053, Integer.Sparse.eval_collectBalanced, rawRowCheck3053]

def rawRow3054 : Integer.Sparse Key := [(key1680, -6), (key1539, 2), (key1615, 2), (key1566, 2), (key1917, 6), (key1309, -2), (key1615, -2), (key1417, -2), (key1895, -2), (key1917, -2), (key1902, -2), (key1350, 2), (key1680, 2), (key1471, 2)]

theorem rawRowCheck3054 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form1 = rawRow3054 := by decide +kernel

def row3054 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

theorem rowCheck3054 : row3054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3054 := by decide +kernel

theorem rowEval3054 (x : Key → ℝ) : Integer.Sparse.eval row3054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3054, Integer.Sparse.eval_collectBalanced, rawRowCheck3054]

def rawRow3055 : Integer.Sparse Key := [(key1680, -6), (key1566, 2), (key1539, 2), (key1615, 2), (key1917, 6), (key1417, -2), (key1309, -2), (key1615, -2), (key1902, -2), (key1895, -2), (key1917, -2), (key1471, 2), (key1350, 2), (key1680, 2)]

theorem rawRowCheck3055 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form1 = rawRow3055 := by decide +kernel

def row3055 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

theorem rowCheck3055 : row3055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3055 := by decide +kernel

theorem rowEval3055 (x : Key → ℝ) : Integer.Sparse.eval row3055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3055, Integer.Sparse.eval_collectBalanced, rawRowCheck3055]

def rawRow3056 : Integer.Sparse Key := [(key1680, -6), (key1566, 2), (key1615, 2), (key1539, 2), (key1917, 6), (key1417, -2), (key1615, -2), (key1309, -2), (key1902, -2), (key1917, -2), (key1895, -2), (key1471, 2), (key1680, 2), (key1350, 2)]

theorem rawRowCheck3056 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form1 = rawRow3056 := by decide +kernel

def row3056 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

theorem rowCheck3056 : row3056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3056 := by decide +kernel

theorem rowEval3056 (x : Key → ℝ) : Integer.Sparse.eval row3056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3056, Integer.Sparse.eval_collectBalanced, rawRowCheck3056]

def rawRow3057 : Integer.Sparse Key := [(key1680, -6), (key1615, 2), (key1539, 2), (key1566, 2), (key1917, 6), (key1615, -2), (key1309, -2), (key1417, -2), (key1917, -2), (key1895, -2), (key1902, -2), (key1680, 2), (key1350, 2), (key1471, 2)]

theorem rawRowCheck3057 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form1 = rawRow3057 := by decide +kernel

def row3057 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

theorem rowCheck3057 : row3057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3057 := by decide +kernel

theorem rowEval3057 (x : Key → ℝ) : Integer.Sparse.eval row3057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3057, Integer.Sparse.eval_collectBalanced, rawRowCheck3057]

def rawRow3058 : Integer.Sparse Key := [(key1680, -6), (key1615, 2), (key1566, 2), (key1539, 2), (key1917, 6), (key1615, -2), (key1417, -2), (key1309, -2), (key1917, -2), (key1902, -2), (key1895, -2), (key1680, 2), (key1471, 2), (key1350, 2)]

theorem rawRowCheck3058 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form1 = rawRow3058 := by decide +kernel

def row3058 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

theorem rowCheck3058 : row3058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3058 := by decide +kernel

theorem rowEval3058 (x : Key → ℝ) : Integer.Sparse.eval row3058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3058, Integer.Sparse.eval_collectBalanced, rawRowCheck3058]

def rawRow3059 : Integer.Sparse Key := [(key1902, -6), (key1895, 2), (key1917, 2), (key1917, 2), (key1471, 6), (key1350, -2), (key1680, -2), (key1680, -2), (key1384, -2), (key1417, -2), (key1417, -2), (key1289, 2), (key1566, 2), (key1566, 2)]

theorem rawRowCheck3059 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3059 := by decide +kernel

def row3059 : Integer.Sparse Key := [(key1289, 2), (key1350, -2), (key1384, -2), (key1417, -4), (key1471, 6), (key1566, 4), (key1680, -4), (key1895, 2), (key1902, -6), (key1917, 4)]

theorem rowCheck3059 : row3059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3059 := by decide +kernel

theorem rowEval3059 (x : Key → ℝ) : Integer.Sparse.eval row3059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3059, Integer.Sparse.eval_collectBalanced, rawRowCheck3059]

def rawRow3060 : Integer.Sparse Key := [(key1902, -6), (key1917, 2), (key1895, 2), (key1917, 2), (key1471, 6), (key1680, -2), (key1350, -2), (key1680, -2), (key1417, -2), (key1384, -2), (key1417, -2), (key1566, 2), (key1289, 2), (key1566, 2)]

theorem rawRowCheck3060 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3060 := by decide +kernel

def row3060 : Integer.Sparse Key := [(key1289, 2), (key1350, -2), (key1384, -2), (key1417, -4), (key1471, 6), (key1566, 4), (key1680, -4), (key1895, 2), (key1902, -6), (key1917, 4)]

theorem rowCheck3060 : row3060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3060 := by decide +kernel

theorem rowEval3060 (x : Key → ℝ) : Integer.Sparse.eval row3060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3060, Integer.Sparse.eval_collectBalanced, rawRowCheck3060]

def rawRow3061 : Integer.Sparse Key := [(key1902, -6), (key1917, 2), (key1917, 2), (key1895, 2), (key1471, 6), (key1680, -2), (key1680, -2), (key1350, -2), (key1417, -2), (key1417, -2), (key1384, -2), (key1566, 2), (key1566, 2), (key1289, 2)]

theorem rawRowCheck3061 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3061 := by decide +kernel

def row3061 : Integer.Sparse Key := [(key1289, 2), (key1350, -2), (key1384, -2), (key1417, -4), (key1471, 6), (key1566, 4), (key1680, -4), (key1895, 2), (key1902, -6), (key1917, 4)]

theorem rowCheck3061 : row3061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3061 := by decide +kernel

theorem rowEval3061 (x : Key → ℝ) : Integer.Sparse.eval row3061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3061, Integer.Sparse.eval_collectBalanced, rawRowCheck3061]

def rawRow3062 : Integer.Sparse Key := [(key1917, -6), (key1895, 2), (key1902, 2), (key1917, 2), (key1680, 6), (key1350, -2), (key1471, -2), (key1680, -2), (key1539, -2), (key1566, -2), (key1615, -2), (key1309, 2), (key1417, 2), (key1615, 2)]

theorem rawRowCheck3062 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form1 = rawRow3062 := by decide +kernel

def row3062 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

theorem rowCheck3062 : row3062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3062 := by decide +kernel

theorem rowEval3062 (x : Key → ℝ) : Integer.Sparse.eval row3062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3062, Integer.Sparse.eval_collectBalanced, rawRowCheck3062]

def rawRow3063 : Integer.Sparse Key := [(key1917, -6), (key1895, 2), (key1917, 2), (key1902, 2), (key1680, 6), (key1350, -2), (key1680, -2), (key1471, -2), (key1539, -2), (key1615, -2), (key1566, -2), (key1309, 2), (key1615, 2), (key1417, 2)]

theorem rawRowCheck3063 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form1 = rawRow3063 := by decide +kernel

def row3063 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

theorem rowCheck3063 : row3063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3063 := by decide +kernel

theorem rowEval3063 (x : Key → ℝ) : Integer.Sparse.eval row3063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3063, Integer.Sparse.eval_collectBalanced, rawRowCheck3063]

def rawRow3064 : Integer.Sparse Key := [(key1917, -6), (key1902, 2), (key1895, 2), (key1917, 2), (key1680, 6), (key1471, -2), (key1350, -2), (key1680, -2), (key1566, -2), (key1539, -2), (key1615, -2), (key1417, 2), (key1309, 2), (key1615, 2)]

theorem rawRowCheck3064 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form1 = rawRow3064 := by decide +kernel

def row3064 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

theorem rowCheck3064 : row3064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3064 := by decide +kernel

theorem rowEval3064 (x : Key → ℝ) : Integer.Sparse.eval row3064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3064, Integer.Sparse.eval_collectBalanced, rawRowCheck3064]

def rawRow3065 : Integer.Sparse Key := [(key1917, -6), (key1902, 2), (key1917, 2), (key1895, 2), (key1680, 6), (key1471, -2), (key1680, -2), (key1350, -2), (key1566, -2), (key1615, -2), (key1539, -2), (key1417, 2), (key1615, 2), (key1309, 2)]

theorem rawRowCheck3065 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form1 = rawRow3065 := by decide +kernel

def row3065 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

theorem rowCheck3065 : row3065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3065 := by decide +kernel

theorem rowEval3065 (x : Key → ℝ) : Integer.Sparse.eval row3065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3065, Integer.Sparse.eval_collectBalanced, rawRowCheck3065]

def rawRow3066 : Integer.Sparse Key := [(key1917, -6), (key1917, 2), (key1895, 2), (key1902, 2), (key1680, 6), (key1680, -2), (key1350, -2), (key1471, -2), (key1615, -2), (key1539, -2), (key1566, -2), (key1615, 2), (key1309, 2), (key1417, 2)]

theorem rawRowCheck3066 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form1 = rawRow3066 := by decide +kernel

def row3066 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

theorem rowCheck3066 : row3066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3066 := by decide +kernel

theorem rowEval3066 (x : Key → ℝ) : Integer.Sparse.eval row3066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3066, Integer.Sparse.eval_collectBalanced, rawRowCheck3066]

def rawRow3067 : Integer.Sparse Key := [(key1917, -6), (key1917, 2), (key1902, 2), (key1895, 2), (key1680, 6), (key1680, -2), (key1471, -2), (key1350, -2), (key1615, -2), (key1566, -2), (key1539, -2), (key1615, 2), (key1417, 2), (key1309, 2)]

theorem rawRowCheck3067 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form1 = rawRow3067 := by decide +kernel

def row3067 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

theorem rowCheck3067 : row3067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3067 := by decide +kernel

theorem rowEval3067 (x : Key → ℝ) : Integer.Sparse.eval row3067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3067, Integer.Sparse.eval_collectBalanced, rawRowCheck3067]

def rawRow3068 : Integer.Sparse Key := [(key2752, -2), (key2752, -2), (key2757, -2), (key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2724, 1), (key2724, 1), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2724, -1), (key2724, -1), (key2868, -1), (key2868, -1), (key3025, -1), (key3025, -1), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1)]

theorem rawRowCheck3068 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form2 = rawRow3068 := by decide +kernel

def row3068 : Integer.Sparse Key := [(key2614, -2), (key2638, 2), (key2669, 2), (key2704, 2), (key2752, -4), (key2757, -2), (key2807, -2), (key2827, -2), (key2858, 2), (key2868, -2), (key3011, 4), (key3016, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck3068 : row3068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3068 := by decide +kernel

theorem rowEval3068 (x : Key → ℝ) : Integer.Sparse.eval row3068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3068, Integer.Sparse.eval_collectBalanced, rawRowCheck3068]

def rawRow3069 : Integer.Sparse Key := [(key2752, -2), (key2757, -2), (key2752, -2), (key2704, 1), (key2724, 1), (key2669, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1)]

theorem rawRowCheck3069 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form2 = rawRow3069 := by decide +kernel

def row3069 : Integer.Sparse Key := [(key2614, -2), (key2638, 2), (key2669, 2), (key2704, 2), (key2752, -4), (key2757, -2), (key2807, -2), (key2827, -2), (key2858, 2), (key2868, -2), (key3011, 4), (key3016, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck3069 : row3069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3069 := by decide +kernel

theorem rowEval3069 (x : Key → ℝ) : Integer.Sparse.eval row3069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3069, Integer.Sparse.eval_collectBalanced, rawRowCheck3069]

def rawRow3070 : Integer.Sparse Key := [(key2757, -2), (key2752, -2), (key2752, -2), (key2724, 1), (key2704, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key3025, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1)]

theorem rawRowCheck3070 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form2 = rawRow3070 := by decide +kernel

def row3070 : Integer.Sparse Key := [(key2614, -2), (key2638, 2), (key2669, 2), (key2704, 2), (key2752, -4), (key2757, -2), (key2807, -2), (key2827, -2), (key2858, 2), (key2868, -2), (key3011, 4), (key3016, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck3070 : row3070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3070 := by decide +kernel

theorem rowEval3070 (x : Key → ℝ) : Integer.Sparse.eval row3070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3070, Integer.Sparse.eval_collectBalanced, rawRowCheck3070]

def rawRow3071 : Integer.Sparse Key := [(key2918, -2), (key2919, -2), (key2922, -2), (key2784, 1), (key2792, 1), (key2807, 1), (key2858, 1), (key2827, 1), (key2868, 1), (key3021, 2), (key3022, 2), (key3025, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3022, -1), (key3016, -1), (key3025, -1), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1)]

theorem rawRowCheck3071 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form2 = rawRow3071 := by decide +kernel

def row3071 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

theorem rowCheck3071 : row3071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3071 := by decide +kernel

theorem rowEval3071 (x : Key → ℝ) : Integer.Sparse.eval row3071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3071, Integer.Sparse.eval_collectBalanced, rawRowCheck3071]

end MUB6.Certificate.GramRows

end OAI

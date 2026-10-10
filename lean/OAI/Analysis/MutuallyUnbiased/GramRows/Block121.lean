import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
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
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12416 : Integer.Sparse Key := [(key1461, -6), (key1461, -6), (key1663, -6), (key1461, -6), (key1403, 2), (key1431, 2), (key1403, 2), (key1403, 2), (key1580, 2), (key1403, 2), (key1431, 2), (key1403, 2), (key1580, 2), (key1403, 2), (key1580, 2), (key1431, 2)]

theorem rawRowCheck12416 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form10 = rawRow12416 := by decide +kernel

def row12416 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

theorem rowCheck12416 : row12416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12416 := by decide +kernel

theorem rowEval12416 (x : Key → ℝ) : Integer.Sparse.eval row12416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12416, Integer.Sparse.eval_collectBalanced, rawRowCheck12416]

def rawRow12417 : Integer.Sparse Key := [(key1461, -6), (key1663, -6), (key1461, -6), (key1461, -6), (key1431, 2), (key1403, 2), (key1403, 2), (key1580, 2), (key1403, 2), (key1403, 2), (key1580, 2), (key1580, 2), (key1431, 2), (key1431, 2), (key1403, 2), (key1403, 2)]

theorem rawRowCheck12417 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form10 = rawRow12417 := by decide +kernel

def row12417 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

theorem rowCheck12417 : row12417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12417 := by decide +kernel

theorem rowEval12417 (x : Key → ℝ) : Integer.Sparse.eval row12417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12417, Integer.Sparse.eval_collectBalanced, rawRowCheck12417]

def rawRow12418 : Integer.Sparse Key := [(key1663, -6), (key1461, -6), (key1461, -6), (key1461, -6), (key1580, 2), (key1580, 2), (key1580, 2), (key1431, 2), (key1431, 2), (key1431, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2)]

theorem rawRowCheck12418 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form10 = rawRow12418 := by decide +kernel

def row12418 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

theorem rowCheck12418 : row12418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12418 := by decide +kernel

theorem rowEval12418 (x : Key → ℝ) : Integer.Sparse.eval row12418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12418, Integer.Sparse.eval_collectBalanced, rawRowCheck12418]

def rawRow12419 : Integer.Sparse Key := [(key2487, 6), (key2492, 6), (key2492, 6), (key2492, 6), (key3035, -6), (key3035, -6), (key3035, -6), (key3128, -6)]

theorem rawRowCheck12419 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form11 = rawRow12419 := by decide +kernel

def row12419 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

theorem rowCheck12419 : row12419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12419 := by decide +kernel

theorem rowEval12419 (x : Key → ℝ) : Integer.Sparse.eval row12419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12419, Integer.Sparse.eval_collectBalanced, rawRowCheck12419]

def rawRow12420 : Integer.Sparse Key := [(key2492, 6), (key2487, 6), (key2492, 6), (key2492, 6), (key3035, -6), (key3035, -6), (key3128, -6), (key3035, -6)]

theorem rawRowCheck12420 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form11 = rawRow12420 := by decide +kernel

def row12420 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

theorem rowCheck12420 : row12420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12420 := by decide +kernel

theorem rowEval12420 (x : Key → ℝ) : Integer.Sparse.eval row12420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12420, Integer.Sparse.eval_collectBalanced, rawRowCheck12420]

def rawRow12421 : Integer.Sparse Key := [(key2492, 6), (key2492, 6), (key2487, 6), (key2492, 6), (key3035, -6), (key3128, -6), (key3035, -6), (key3035, -6)]

theorem rawRowCheck12421 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form11 = rawRow12421 := by decide +kernel

def row12421 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

theorem rowCheck12421 : row12421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12421 := by decide +kernel

theorem rowEval12421 (x : Key → ℝ) : Integer.Sparse.eval row12421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12421, Integer.Sparse.eval_collectBalanced, rawRowCheck12421]

def rawRow12422 : Integer.Sparse Key := [(key2492, 6), (key2492, 6), (key2492, 6), (key2487, 6), (key3128, -6), (key3035, -6), (key3035, -6), (key3035, -6)]

theorem rawRowCheck12422 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form11 = rawRow12422 := by decide +kernel

def row12422 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

theorem rowCheck12422 : row12422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12422 := by decide +kernel

theorem rowEval12422 (x : Key → ℝ) : Integer.Sparse.eval row12422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12422, Integer.Sparse.eval_collectBalanced, rawRowCheck12422]

def rawRow12423 : Integer.Sparse Key := [(key2546, 6), (key2548, 6), (key2548, 6), (key2548, 6), (key2414, -6), (key3033, -6), (key3033, -6), (key3120, -6)]

theorem rawRowCheck12423 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form11 = rawRow12423 := by decide +kernel

def row12423 : Integer.Sparse Key := [(key2414, -6), (key2546, 6), (key2548, 18), (key3033, -12), (key3120, -6)]

theorem rowCheck12423 : row12423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12423 := by decide +kernel

theorem rowEval12423 (x : Key → ℝ) : Integer.Sparse.eval row12423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12423, Integer.Sparse.eval_collectBalanced, rawRowCheck12423]

def rawRow12424 : Integer.Sparse Key := [(key2548, 6), (key2546, 6), (key2548, 6), (key2548, 6), (key2414, -6), (key3033, -6), (key3120, -6), (key3033, -6)]

theorem rawRowCheck12424 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form11 = rawRow12424 := by decide +kernel

def row12424 : Integer.Sparse Key := [(key2414, -6), (key2546, 6), (key2548, 18), (key3033, -12), (key3120, -6)]

theorem rowCheck12424 : row12424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12424 := by decide +kernel

theorem rowEval12424 (x : Key → ℝ) : Integer.Sparse.eval row12424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12424, Integer.Sparse.eval_collectBalanced, rawRowCheck12424]

def rawRow12425 : Integer.Sparse Key := [(key2548, 6), (key2548, 6), (key2546, 6), (key2548, 6), (key2414, -6), (key3120, -6), (key3033, -6), (key3033, -6)]

theorem rawRowCheck12425 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form11 = rawRow12425 := by decide +kernel

def row12425 : Integer.Sparse Key := [(key2414, -6), (key2546, 6), (key2548, 18), (key3033, -12), (key3120, -6)]

theorem rowCheck12425 : row12425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12425 := by decide +kernel

theorem rowEval12425 (x : Key → ℝ) : Integer.Sparse.eval row12425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12425, Integer.Sparse.eval_collectBalanced, rawRowCheck12425]

def rawRow12426 : Integer.Sparse Key := [(key2548, 6), (key2548, 6), (key2548, 6), (key2546, 6), (key2487, -6), (key2414, -6), (key3033, -6), (key3033, -6)]

theorem rawRowCheck12426 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form11 = rawRow12426 := by decide +kernel

def row12426 : Integer.Sparse Key := [(key2414, -6), (key2487, -6), (key2546, 6), (key2548, 18), (key3033, -12)]

theorem rowCheck12426 : row12426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12426 := by decide +kernel

theorem rowEval12426 (x : Key → ℝ) : Integer.Sparse.eval row12426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck12426, Integer.Sparse.eval_collectBalanced, rawRowCheck12426]

def rawRow12427 : Integer.Sparse Key := [(key2488, 6), (key2493, 6), (key2493, 6), (key2493, 6), (key2418, -6), (key2418, -6), (key2418, -6), (key2547, -6)]

theorem rawRowCheck12427 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form12 = rawRow12427 := by decide +kernel

def row12427 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

theorem rowCheck12427 : row12427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12427 := by decide +kernel

theorem rowEval12427 (x : Key → ℝ) : Integer.Sparse.eval row12427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12427, Integer.Sparse.eval_collectBalanced, rawRowCheck12427]

def rawRow12428 : Integer.Sparse Key := [(key2493, 6), (key2488, 6), (key2493, 6), (key2493, 6), (key2418, -6), (key2418, -6), (key2547, -6), (key2418, -6)]

theorem rawRowCheck12428 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form12 = rawRow12428 := by decide +kernel

def row12428 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

theorem rowCheck12428 : row12428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12428 := by decide +kernel

theorem rowEval12428 (x : Key → ℝ) : Integer.Sparse.eval row12428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12428, Integer.Sparse.eval_collectBalanced, rawRowCheck12428]

def rawRow12429 : Integer.Sparse Key := [(key2493, 6), (key2493, 6), (key2488, 6), (key2493, 6), (key2418, -6), (key2547, -6), (key2418, -6), (key2418, -6)]

theorem rawRowCheck12429 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form12 = rawRow12429 := by decide +kernel

def row12429 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

theorem rowCheck12429 : row12429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12429 := by decide +kernel

theorem rowEval12429 (x : Key → ℝ) : Integer.Sparse.eval row12429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12429, Integer.Sparse.eval_collectBalanced, rawRowCheck12429]

def rawRow12430 : Integer.Sparse Key := [(key2493, 6), (key2493, 6), (key2493, 6), (key2488, 6), (key2547, -6), (key2418, -6), (key2418, -6), (key2418, -6)]

theorem rawRowCheck12430 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form12 = rawRow12430 := by decide +kernel

def row12430 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

theorem rowCheck12430 : row12430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12430 := by decide +kernel

theorem rowEval12430 (x : Key → ℝ) : Integer.Sparse.eval row12430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12430, Integer.Sparse.eval_collectBalanced, rawRowCheck12430]

def rawRow12431 : Integer.Sparse Key := [(key2547, 6), (key2549, 6), (key2549, 6), (key2549, 6), (key2415, -6), (key2415, -6), (key2415, -6), (key2488, -6)]

theorem rawRowCheck12431 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form12 = rawRow12431 := by decide +kernel

def row12431 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

theorem rowCheck12431 : row12431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12431 := by decide +kernel

theorem rowEval12431 (x : Key → ℝ) : Integer.Sparse.eval row12431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12431, Integer.Sparse.eval_collectBalanced, rawRowCheck12431]

def rawRow12432 : Integer.Sparse Key := [(key2549, 6), (key2547, 6), (key2549, 6), (key2549, 6), (key2415, -6), (key2415, -6), (key2488, -6), (key2415, -6)]

theorem rawRowCheck12432 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form12 = rawRow12432 := by decide +kernel

def row12432 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

theorem rowCheck12432 : row12432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12432 := by decide +kernel

theorem rowEval12432 (x : Key → ℝ) : Integer.Sparse.eval row12432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12432, Integer.Sparse.eval_collectBalanced, rawRowCheck12432]

def rawRow12433 : Integer.Sparse Key := [(key2549, 6), (key2549, 6), (key2547, 6), (key2549, 6), (key2415, -6), (key2488, -6), (key2415, -6), (key2415, -6)]

theorem rawRowCheck12433 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form12 = rawRow12433 := by decide +kernel

def row12433 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

theorem rowCheck12433 : row12433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12433 := by decide +kernel

theorem rowEval12433 (x : Key → ℝ) : Integer.Sparse.eval row12433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12433, Integer.Sparse.eval_collectBalanced, rawRowCheck12433]

def rawRow12434 : Integer.Sparse Key := [(key2549, 6), (key2549, 6), (key2549, 6), (key2547, 6), (key2488, -6), (key2415, -6), (key2415, -6), (key2415, -6)]

theorem rawRowCheck12434 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form12 = rawRow12434 := by decide +kernel

def row12434 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

theorem rowCheck12434 : row12434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12434 := by decide +kernel

theorem rowEval12434 (x : Key → ℝ) : Integer.Sparse.eval row12434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck12434, Integer.Sparse.eval_collectBalanced, rawRowCheck12434]

def rawRow12435 : Integer.Sparse Key := [(key2308, -6), (key2309, -6), (key2309, -6), (key2309, -6), (key2197, 2), (key2199, 2), (key2199, 2), (key2197, 2), (key2199, 2), (key2197, 2), (key2346, 2), (key2199, 2), (key2346, 2), (key2199, 2), (key2199, 2), (key2346, 2)]

theorem rawRowCheck12435 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form13 = rawRow12435 := by decide +kernel

def row12435 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

theorem rowCheck12435 : row12435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12435 := by decide +kernel

theorem rowEval12435 (x : Key → ℝ) : Integer.Sparse.eval row12435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12435, Integer.Sparse.eval_collectBalanced, rawRowCheck12435]

def rawRow12436 : Integer.Sparse Key := [(key2309, -6), (key2308, -6), (key2309, -6), (key2309, -6), (key2199, 2), (key2197, 2), (key2199, 2), (key2199, 2), (key2197, 2), (key2346, 2), (key2197, 2), (key2346, 2), (key2199, 2), (key2199, 2), (key2346, 2), (key2199, 2)]

theorem rawRowCheck12436 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form13 = rawRow12436 := by decide +kernel

def row12436 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

theorem rowCheck12436 : row12436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12436 := by decide +kernel

theorem rowEval12436 (x : Key → ℝ) : Integer.Sparse.eval row12436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12436, Integer.Sparse.eval_collectBalanced, rawRowCheck12436]

def rawRow12437 : Integer.Sparse Key := [(key2309, -6), (key2309, -6), (key2308, -6), (key2309, -6), (key2199, 2), (key2199, 2), (key2197, 2), (key2346, 2), (key2346, 2), (key2199, 2), (key2199, 2), (key2197, 2), (key2197, 2), (key2346, 2), (key2199, 2), (key2199, 2)]

theorem rawRowCheck12437 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form13 = rawRow12437 := by decide +kernel

def row12437 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

theorem rowCheck12437 : row12437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12437 := by decide +kernel

theorem rowEval12437 (x : Key → ℝ) : Integer.Sparse.eval row12437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12437, Integer.Sparse.eval_collectBalanced, rawRowCheck12437]

def rawRow12438 : Integer.Sparse Key := [(key2309, -6), (key2309, -6), (key2309, -6), (key2308, -6), (key2346, 2), (key2346, 2), (key2346, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2197, 2), (key2197, 2), (key2197, 2)]

theorem rawRowCheck12438 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form13 = rawRow12438 := by decide +kernel

def row12438 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

theorem rowCheck12438 : row12438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12438 := by decide +kernel

theorem rowEval12438 (x : Key → ℝ) : Integer.Sparse.eval row12438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12438, Integer.Sparse.eval_collectBalanced, rawRowCheck12438]

def rawRow12439 : Integer.Sparse Key := [(key2345, -6), (key2346, -6), (key2346, -6), (key2346, -6), (key2198, 2), (key2199, 2), (key2199, 2), (key2198, 2), (key2199, 2), (key2198, 2), (key2309, 2), (key2199, 2), (key2309, 2), (key2199, 2), (key2199, 2), (key2309, 2)]

theorem rawRowCheck12439 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form13 = rawRow12439 := by decide +kernel

def row12439 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

theorem rowCheck12439 : row12439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12439 := by decide +kernel

theorem rowEval12439 (x : Key → ℝ) : Integer.Sparse.eval row12439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12439, Integer.Sparse.eval_collectBalanced, rawRowCheck12439]

def rawRow12440 : Integer.Sparse Key := [(key2346, -6), (key2345, -6), (key2346, -6), (key2346, -6), (key2199, 2), (key2198, 2), (key2199, 2), (key2199, 2), (key2198, 2), (key2309, 2), (key2198, 2), (key2309, 2), (key2199, 2), (key2199, 2), (key2309, 2), (key2199, 2)]

theorem rawRowCheck12440 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form13 = rawRow12440 := by decide +kernel

def row12440 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

theorem rowCheck12440 : row12440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12440 := by decide +kernel

theorem rowEval12440 (x : Key → ℝ) : Integer.Sparse.eval row12440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12440, Integer.Sparse.eval_collectBalanced, rawRowCheck12440]

def rawRow12441 : Integer.Sparse Key := [(key2346, -6), (key2346, -6), (key2345, -6), (key2346, -6), (key2199, 2), (key2199, 2), (key2198, 2), (key2309, 2), (key2309, 2), (key2199, 2), (key2199, 2), (key2198, 2), (key2198, 2), (key2309, 2), (key2199, 2), (key2199, 2)]

theorem rawRowCheck12441 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form13 = rawRow12441 := by decide +kernel

def row12441 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

theorem rowCheck12441 : row12441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12441 := by decide +kernel

theorem rowEval12441 (x : Key → ℝ) : Integer.Sparse.eval row12441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12441, Integer.Sparse.eval_collectBalanced, rawRowCheck12441]

def rawRow12442 : Integer.Sparse Key := [(key2346, -6), (key2346, -6), (key2346, -6), (key2345, -6), (key2309, 2), (key2309, 2), (key2309, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2198, 2), (key2198, 2), (key2198, 2)]

theorem rawRowCheck12442 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form13 = rawRow12442 := by decide +kernel

def row12442 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

theorem rowCheck12442 : row12442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12442 := by decide +kernel

theorem rowEval12442 (x : Key → ℝ) : Integer.Sparse.eval row12442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck12442, Integer.Sparse.eval_collectBalanced, rawRowCheck12442]

def rawRow12443 : Integer.Sparse Key := [(key1135, 6), (key1140, 6), (key1140, 6), (key1140, 6), (key1052, -6), (key1052, -6), (key1052, -6), (key1205, -6)]

theorem rawRowCheck12443 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form14 = rawRow12443 := by decide +kernel

def row12443 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

theorem rowCheck12443 : row12443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12443 := by decide +kernel

theorem rowEval12443 (x : Key → ℝ) : Integer.Sparse.eval row12443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12443, Integer.Sparse.eval_collectBalanced, rawRowCheck12443]

def rawRow12444 : Integer.Sparse Key := [(key1140, 6), (key1135, 6), (key1140, 6), (key1140, 6), (key1052, -6), (key1052, -6), (key1205, -6), (key1052, -6)]

theorem rawRowCheck12444 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form14 = rawRow12444 := by decide +kernel

def row12444 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

theorem rowCheck12444 : row12444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12444 := by decide +kernel

theorem rowEval12444 (x : Key → ℝ) : Integer.Sparse.eval row12444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12444, Integer.Sparse.eval_collectBalanced, rawRowCheck12444]

def rawRow12445 : Integer.Sparse Key := [(key1140, 6), (key1140, 6), (key1135, 6), (key1140, 6), (key1052, -6), (key1205, -6), (key1052, -6), (key1052, -6)]

theorem rawRowCheck12445 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form14 = rawRow12445 := by decide +kernel

def row12445 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

theorem rowCheck12445 : row12445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12445 := by decide +kernel

theorem rowEval12445 (x : Key → ℝ) : Integer.Sparse.eval row12445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12445, Integer.Sparse.eval_collectBalanced, rawRowCheck12445]

def rawRow12446 : Integer.Sparse Key := [(key1140, 6), (key1140, 6), (key1140, 6), (key1135, 6), (key1205, -6), (key1052, -6), (key1052, -6), (key1052, -6)]

theorem rawRowCheck12446 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form14 = rawRow12446 := by decide +kernel

def row12446 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

theorem rowCheck12446 : row12446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12446 := by decide +kernel

theorem rowEval12446 (x : Key → ℝ) : Integer.Sparse.eval row12446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12446, Integer.Sparse.eval_collectBalanced, rawRowCheck12446]

def rawRow12447 : Integer.Sparse Key := [(key1205, 6), (key1207, 6), (key1207, 6), (key1207, 6), (key1049, -6), (key1049, -6), (key1049, -6), (key1135, -6)]

theorem rawRowCheck12447 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form14 = rawRow12447 := by decide +kernel

def row12447 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

theorem rowCheck12447 : row12447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12447 := by decide +kernel

theorem rowEval12447 (x : Key → ℝ) : Integer.Sparse.eval row12447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12447, Integer.Sparse.eval_collectBalanced, rawRowCheck12447]

def rawRow12448 : Integer.Sparse Key := [(key1207, 6), (key1205, 6), (key1207, 6), (key1207, 6), (key1049, -6), (key1049, -6), (key1135, -6), (key1049, -6)]

theorem rawRowCheck12448 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form14 = rawRow12448 := by decide +kernel

def row12448 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

theorem rowCheck12448 : row12448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12448 := by decide +kernel

theorem rowEval12448 (x : Key → ℝ) : Integer.Sparse.eval row12448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12448, Integer.Sparse.eval_collectBalanced, rawRowCheck12448]

def rawRow12449 : Integer.Sparse Key := [(key1207, 6), (key1207, 6), (key1205, 6), (key1207, 6), (key1049, -6), (key1135, -6), (key1049, -6), (key1049, -6)]

theorem rawRowCheck12449 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form14 = rawRow12449 := by decide +kernel

def row12449 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

theorem rowCheck12449 : row12449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12449 := by decide +kernel

theorem rowEval12449 (x : Key → ℝ) : Integer.Sparse.eval row12449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12449, Integer.Sparse.eval_collectBalanced, rawRowCheck12449]

def rawRow12450 : Integer.Sparse Key := [(key1207, 6), (key1207, 6), (key1207, 6), (key1205, 6), (key1135, -6), (key1049, -6), (key1049, -6), (key1049, -6)]

theorem rawRowCheck12450 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form14 = rawRow12450 := by decide +kernel

def row12450 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

theorem rowCheck12450 : row12450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12450 := by decide +kernel

theorem rowEval12450 (x : Key → ℝ) : Integer.Sparse.eval row12450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12450, Integer.Sparse.eval_collectBalanced, rawRowCheck12450]

def rawRow12451 : Integer.Sparse Key := [(key2487, -6), (key2492, -6), (key2492, -6), (key2492, -6), (key2414, 2), (key2424, 2), (key2424, 2), (key3033, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3138, 2)]

theorem rawRowCheck12451 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form15 = rawRow12451 := by decide +kernel

def row12451 : Integer.Sparse Key := [(key2414, 2), (key2424, 4), (key2487, -6), (key2492, -18), (key3033, 4), (key3039, 8), (key3138, 6)]

theorem rowCheck12451 : row12451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12451 := by decide +kernel

theorem rowEval12451 (x : Key → ℝ) : Integer.Sparse.eval row12451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12451, Integer.Sparse.eval_collectBalanced, rawRowCheck12451]

def rawRow12452 : Integer.Sparse Key := [(key2492, -6), (key2487, -6), (key2492, -6), (key2492, -6), (key2424, 2), (key2414, 2), (key2424, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3138, 2), (key3039, 2)]

theorem rawRowCheck12452 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form15 = rawRow12452 := by decide +kernel

def row12452 : Integer.Sparse Key := [(key2414, 2), (key2424, 4), (key2487, -6), (key2492, -18), (key3033, 4), (key3039, 8), (key3138, 6)]

theorem rowCheck12452 : row12452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12452 := by decide +kernel

theorem rowEval12452 (x : Key → ℝ) : Integer.Sparse.eval row12452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12452, Integer.Sparse.eval_collectBalanced, rawRowCheck12452]

def rawRow12453 : Integer.Sparse Key := [(key2492, -6), (key2492, -6), (key2487, -6), (key2492, -6), (key2424, 2), (key2424, 2), (key2414, 2), (key3138, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3033, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3039, 2)]

theorem rawRowCheck12453 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form15 = rawRow12453 := by decide +kernel

def row12453 : Integer.Sparse Key := [(key2414, 2), (key2424, 4), (key2487, -6), (key2492, -18), (key3033, 4), (key3039, 8), (key3138, 6)]

theorem rowCheck12453 : row12453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12453 := by decide +kernel

theorem rowEval12453 (x : Key → ℝ) : Integer.Sparse.eval row12453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12453, Integer.Sparse.eval_collectBalanced, rawRowCheck12453]

def rawRow12454 : Integer.Sparse Key := [(key2492, -6), (key2492, -6), (key2492, -6), (key2487, -6), (key2548, 2), (key2548, 2), (key2548, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2414, 2), (key3033, 2), (key3033, 2)]

theorem rawRowCheck12454 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form15 = rawRow12454 := by decide +kernel

def row12454 : Integer.Sparse Key := [(key2414, 2), (key2424, 12), (key2487, -6), (key2492, -18), (key2548, 6), (key3033, 4)]

theorem rowCheck12454 : row12454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12454 := by decide +kernel

theorem rowEval12454 (x : Key → ℝ) : Integer.Sparse.eval row12454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12454, Integer.Sparse.eval_collectBalanced, rawRowCheck12454]

def rawRow12455 : Integer.Sparse Key := [(key2546, -6), (key2548, -6), (key2548, -6), (key2548, -6), (key2417, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2424, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2492, 2)]

theorem rawRowCheck12455 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form15 = rawRow12455 := by decide +kernel

def row12455 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

theorem rowCheck12455 : row12455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12455 := by decide +kernel

theorem rowEval12455 (x : Key → ℝ) : Integer.Sparse.eval row12455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12455, Integer.Sparse.eval_collectBalanced, rawRowCheck12455]

def rawRow12456 : Integer.Sparse Key := [(key2548, -6), (key2546, -6), (key2548, -6), (key2548, -6), (key2424, 2), (key2417, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2492, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2492, 2), (key2424, 2)]

theorem rawRowCheck12456 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form15 = rawRow12456 := by decide +kernel

def row12456 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

theorem rowCheck12456 : row12456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12456 := by decide +kernel

theorem rowEval12456 (x : Key → ℝ) : Integer.Sparse.eval row12456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12456, Integer.Sparse.eval_collectBalanced, rawRowCheck12456]

def rawRow12457 : Integer.Sparse Key := [(key2548, -6), (key2548, -6), (key2546, -6), (key2548, -6), (key2424, 2), (key2424, 2), (key2417, 2), (key2492, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2424, 2)]

theorem rawRowCheck12457 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form15 = rawRow12457 := by decide +kernel

def row12457 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

theorem rowCheck12457 : row12457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12457 := by decide +kernel

theorem rowEval12457 (x : Key → ℝ) : Integer.Sparse.eval row12457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12457, Integer.Sparse.eval_collectBalanced, rawRowCheck12457]

def rawRow12458 : Integer.Sparse Key := [(key2548, -6), (key2548, -6), (key2548, -6), (key2546, -6), (key2492, 2), (key2492, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2417, 2), (key2417, 2)]

theorem rawRowCheck12458 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form15 = rawRow12458 := by decide +kernel

def row12458 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

theorem rowCheck12458 : row12458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12458 := by decide +kernel

theorem rowEval12458 (x : Key → ℝ) : Integer.Sparse.eval row12458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12458, Integer.Sparse.eval_collectBalanced, rawRowCheck12458]

def rawRow12459 : Integer.Sparse Key := [(key3095, -6), (key3095, -6), (key3095, -6), (key3123, -6), (key3060, 6), (key3060, 6), (key3060, 6), (key3125, 6)]

theorem rawRowCheck12459 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form16 = rawRow12459 := by decide +kernel

def row12459 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

theorem rowCheck12459 : row12459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12459 := by decide +kernel

theorem rowEval12459 (x : Key → ℝ) : Integer.Sparse.eval row12459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12459, Integer.Sparse.eval_collectBalanced, rawRowCheck12459]

def rawRow12460 : Integer.Sparse Key := [(key3095, -6), (key3095, -6), (key3123, -6), (key3095, -6), (key3060, 6), (key3060, 6), (key3125, 6), (key3060, 6)]

theorem rawRowCheck12460 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form16 = rawRow12460 := by decide +kernel

def row12460 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

theorem rowCheck12460 : row12460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12460 := by decide +kernel

theorem rowEval12460 (x : Key → ℝ) : Integer.Sparse.eval row12460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12460, Integer.Sparse.eval_collectBalanced, rawRowCheck12460]

def rawRow12461 : Integer.Sparse Key := [(key3095, -6), (key3123, -6), (key3095, -6), (key3095, -6), (key3060, 6), (key3125, 6), (key3060, 6), (key3060, 6)]

theorem rawRowCheck12461 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form16 = rawRow12461 := by decide +kernel

def row12461 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

theorem rowCheck12461 : row12461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12461 := by decide +kernel

theorem rowEval12461 (x : Key → ℝ) : Integer.Sparse.eval row12461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12461, Integer.Sparse.eval_collectBalanced, rawRowCheck12461]

def rawRow12462 : Integer.Sparse Key := [(key3123, -6), (key3095, -6), (key3095, -6), (key3095, -6), (key3125, 6), (key3060, 6), (key3060, 6), (key3060, 6)]

theorem rawRowCheck12462 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form16 = rawRow12462 := by decide +kernel

def row12462 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

theorem rowCheck12462 : row12462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12462 := by decide +kernel

theorem rowEval12462 (x : Key → ℝ) : Integer.Sparse.eval row12462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12462, Integer.Sparse.eval_collectBalanced, rawRowCheck12462]

def rawRow12463 : Integer.Sparse Key := [(key3101, -6), (key3101, -6), (key3101, -6), (key3125, -6), (key3064, 6), (key3064, 6), (key3064, 6), (key3123, 6)]

theorem rawRowCheck12463 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form16 = rawRow12463 := by decide +kernel

def row12463 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

theorem rowCheck12463 : row12463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12463 := by decide +kernel

theorem rowEval12463 (x : Key → ℝ) : Integer.Sparse.eval row12463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12463, Integer.Sparse.eval_collectBalanced, rawRowCheck12463]

def rawRow12464 : Integer.Sparse Key := [(key3101, -6), (key3101, -6), (key3125, -6), (key3101, -6), (key3064, 6), (key3064, 6), (key3123, 6), (key3064, 6)]

theorem rawRowCheck12464 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form16 = rawRow12464 := by decide +kernel

def row12464 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

theorem rowCheck12464 : row12464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12464 := by decide +kernel

theorem rowEval12464 (x : Key → ℝ) : Integer.Sparse.eval row12464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12464, Integer.Sparse.eval_collectBalanced, rawRowCheck12464]

def rawRow12465 : Integer.Sparse Key := [(key3101, -6), (key3125, -6), (key3101, -6), (key3101, -6), (key3064, 6), (key3123, 6), (key3064, 6), (key3064, 6)]

theorem rawRowCheck12465 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form16 = rawRow12465 := by decide +kernel

def row12465 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

theorem rowCheck12465 : row12465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12465 := by decide +kernel

theorem rowEval12465 (x : Key → ℝ) : Integer.Sparse.eval row12465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12465, Integer.Sparse.eval_collectBalanced, rawRowCheck12465]

def rawRow12466 : Integer.Sparse Key := [(key3125, -6), (key3101, -6), (key3101, -6), (key3101, -6), (key3123, 6), (key3064, 6), (key3064, 6), (key3064, 6)]

theorem rawRowCheck12466 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form16 = rawRow12466 := by decide +kernel

def row12466 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

theorem rowCheck12466 : row12466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12466 := by decide +kernel

theorem rowEval12466 (x : Key → ℝ) : Integer.Sparse.eval row12466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12466, Integer.Sparse.eval_collectBalanced, rawRowCheck12466]

def rawRow12467 : Integer.Sparse Key := [(key2719, -2), (key2719, -2), (key2731, -2), (key2719, -2), (key2719, -2), (key2986, -2), (key2719, -2), (key2731, -2), (key2719, -2), (key2986, -2), (key2731, -2), (key2986, -2), (key2693, 2), (key2693, 2), (key2750, 2), (key2693, 2), (key2693, 2), (key2963, 2), (key2693, 2), (key2750, 2), (key2693, 2), (key2963, 2), (key2750, 2), (key2963, 2)]

theorem rawRowCheck12467 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form17 = rawRow12467 := by decide +kernel

def row12467 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

theorem rowCheck12467 : row12467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12467 := by decide +kernel

theorem rowEval12467 (x : Key → ℝ) : Integer.Sparse.eval row12467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12467, Integer.Sparse.eval_collectBalanced, rawRowCheck12467]

def rawRow12468 : Integer.Sparse Key := [(key2719, -2), (key2731, -2), (key2719, -2), (key2719, -2), (key2986, -2), (key2719, -2), (key2731, -2), (key2719, -2), (key2986, -2), (key2719, -2), (key2986, -2), (key2731, -2), (key2693, 2), (key2750, 2), (key2693, 2), (key2693, 2), (key2963, 2), (key2693, 2), (key2750, 2), (key2693, 2), (key2963, 2), (key2693, 2), (key2963, 2), (key2750, 2)]

theorem rawRowCheck12468 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form17 = rawRow12468 := by decide +kernel

def row12468 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

theorem rowCheck12468 : row12468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12468 := by decide +kernel

theorem rowEval12468 (x : Key → ℝ) : Integer.Sparse.eval row12468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12468, Integer.Sparse.eval_collectBalanced, rawRowCheck12468]

def rawRow12469 : Integer.Sparse Key := [(key2731, -2), (key2719, -2), (key2719, -2), (key2986, -2), (key2719, -2), (key2719, -2), (key2986, -2), (key2986, -2), (key2731, -2), (key2731, -2), (key2719, -2), (key2719, -2), (key2750, 2), (key2693, 2), (key2693, 2), (key2963, 2), (key2693, 2), (key2693, 2), (key2963, 2), (key2963, 2), (key2750, 2), (key2750, 2), (key2693, 2), (key2693, 2)]

theorem rawRowCheck12469 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form17 = rawRow12469 := by decide +kernel

def row12469 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

theorem rowCheck12469 : row12469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12469 := by decide +kernel

theorem rowEval12469 (x : Key → ℝ) : Integer.Sparse.eval row12469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12469, Integer.Sparse.eval_collectBalanced, rawRowCheck12469]

def rawRow12470 : Integer.Sparse Key := [(key2986, -2), (key2986, -2), (key2986, -2), (key2731, -2), (key2731, -2), (key2731, -2), (key2719, -2), (key2719, -2), (key2719, -2), (key2719, -2), (key2719, -2), (key2719, -2), (key2963, 2), (key2963, 2), (key2963, 2), (key2750, 2), (key2750, 2), (key2750, 2), (key2693, 2), (key2693, 2), (key2693, 2), (key2693, 2), (key2693, 2), (key2693, 2)]

theorem rawRowCheck12470 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form17 = rawRow12470 := by decide +kernel

def row12470 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

theorem rowCheck12470 : row12470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12470 := by decide +kernel

theorem rowEval12470 (x : Key → ℝ) : Integer.Sparse.eval row12470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12470, Integer.Sparse.eval_collectBalanced, rawRowCheck12470]

def rawRow12471 : Integer.Sparse Key := [(key2744, -2), (key2744, -2), (key2750, -2), (key2744, -2), (key2744, -2), (key2907, -2), (key2744, -2), (key2750, -2), (key2744, -2), (key2907, -2), (key2750, -2), (key2907, -2), (key2694, 2), (key2694, 2), (key2731, 2), (key2694, 2), (key2694, 2), (key2834, 2), (key2694, 2), (key2731, 2), (key2694, 2), (key2834, 2), (key2731, 2), (key2834, 2)]

theorem rawRowCheck12471 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form17 = rawRow12471 := by decide +kernel

def row12471 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

theorem rowCheck12471 : row12471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12471 := by decide +kernel

theorem rowEval12471 (x : Key → ℝ) : Integer.Sparse.eval row12471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12471, Integer.Sparse.eval_collectBalanced, rawRowCheck12471]

def rawRow12472 : Integer.Sparse Key := [(key2744, -2), (key2750, -2), (key2744, -2), (key2744, -2), (key2907, -2), (key2744, -2), (key2750, -2), (key2744, -2), (key2907, -2), (key2744, -2), (key2907, -2), (key2750, -2), (key2694, 2), (key2731, 2), (key2694, 2), (key2694, 2), (key2834, 2), (key2694, 2), (key2731, 2), (key2694, 2), (key2834, 2), (key2694, 2), (key2834, 2), (key2731, 2)]

theorem rawRowCheck12472 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form17 = rawRow12472 := by decide +kernel

def row12472 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

theorem rowCheck12472 : row12472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12472 := by decide +kernel

theorem rowEval12472 (x : Key → ℝ) : Integer.Sparse.eval row12472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12472, Integer.Sparse.eval_collectBalanced, rawRowCheck12472]

def rawRow12473 : Integer.Sparse Key := [(key2750, -2), (key2744, -2), (key2744, -2), (key2907, -2), (key2744, -2), (key2744, -2), (key2907, -2), (key2907, -2), (key2750, -2), (key2750, -2), (key2744, -2), (key2744, -2), (key2731, 2), (key2694, 2), (key2694, 2), (key2834, 2), (key2694, 2), (key2694, 2), (key2834, 2), (key2834, 2), (key2731, 2), (key2731, 2), (key2694, 2), (key2694, 2)]

theorem rawRowCheck12473 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form17 = rawRow12473 := by decide +kernel

def row12473 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

theorem rowCheck12473 : row12473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12473 := by decide +kernel

theorem rowEval12473 (x : Key → ℝ) : Integer.Sparse.eval row12473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12473, Integer.Sparse.eval_collectBalanced, rawRowCheck12473]

def rawRow12474 : Integer.Sparse Key := [(key2907, -2), (key2907, -2), (key2907, -2), (key2750, -2), (key2750, -2), (key2750, -2), (key2744, -2), (key2744, -2), (key2744, -2), (key2744, -2), (key2744, -2), (key2744, -2), (key2834, 2), (key2834, 2), (key2834, 2), (key2731, 2), (key2731, 2), (key2731, 2), (key2694, 2), (key2694, 2), (key2694, 2), (key2694, 2), (key2694, 2), (key2694, 2)]

theorem rawRowCheck12474 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form17 = rawRow12474 := by decide +kernel

def row12474 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

theorem rowCheck12474 : row12474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12474 := by decide +kernel

theorem rowEval12474 (x : Key → ℝ) : Integer.Sparse.eval row12474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12474, Integer.Sparse.eval_collectBalanced, rawRowCheck12474]

def rawRow12475 : Integer.Sparse Key := [(key1064, 2), (key1064, 2), (key1079, 2), (key1064, 2), (key1064, 2), (key1215, 2), (key1064, 2), (key1079, 2), (key1064, 2), (key1215, 2), (key1079, 2), (key1215, 2), (key1056, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1208, -2)]

theorem rawRowCheck12475 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form18 = rawRow12475 := by decide +kernel

def row12475 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

theorem rowCheck12475 : row12475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12475 := by decide +kernel

theorem rowEval12475 (x : Key → ℝ) : Integer.Sparse.eval row12475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12475, Integer.Sparse.eval_collectBalanced, rawRowCheck12475]

def rawRow12476 : Integer.Sparse Key := [(key1064, 2), (key1079, 2), (key1064, 2), (key1064, 2), (key1215, 2), (key1064, 2), (key1079, 2), (key1064, 2), (key1215, 2), (key1064, 2), (key1215, 2), (key1079, 2), (key1065, -2), (key1056, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1208, -2), (key1065, -2)]

theorem rawRowCheck12476 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form18 = rawRow12476 := by decide +kernel

def row12476 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

theorem rowCheck12476 : row12476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12476 := by decide +kernel

theorem rowEval12476 (x : Key → ℝ) : Integer.Sparse.eval row12476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12476, Integer.Sparse.eval_collectBalanced, rawRowCheck12476]

def rawRow12477 : Integer.Sparse Key := [(key1079, 2), (key1064, 2), (key1064, 2), (key1215, 2), (key1064, 2), (key1064, 2), (key1215, 2), (key1215, 2), (key1079, 2), (key1079, 2), (key1064, 2), (key1064, 2), (key1065, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1065, -2)]

theorem rawRowCheck12477 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form18 = rawRow12477 := by decide +kernel

def row12477 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

theorem rowCheck12477 : row12477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12477 := by decide +kernel

theorem rowEval12477 (x : Key → ℝ) : Integer.Sparse.eval row12477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12477, Integer.Sparse.eval_collectBalanced, rawRowCheck12477]

def rawRow12478 : Integer.Sparse Key := [(key1215, 2), (key1215, 2), (key1215, 2), (key1079, 2), (key1079, 2), (key1079, 2), (key1064, 2), (key1064, 2), (key1064, 2), (key1064, 2), (key1064, 2), (key1064, 2), (key1208, -2), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1056, -2)]

theorem rawRowCheck12478 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form18 = rawRow12478 := by decide +kernel

def row12478 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

theorem rowCheck12478 : row12478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12478 := by decide +kernel

theorem rowEval12478 (x : Key → ℝ) : Integer.Sparse.eval row12478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12478, Integer.Sparse.eval_collectBalanced, rawRowCheck12478]

def rawRow12479 : Integer.Sparse Key := [(key1065, 2), (key1065, 2), (key1079, 2), (key1065, 2), (key1065, 2), (key1158, 2), (key1065, 2), (key1079, 2), (key1065, 2), (key1158, 2), (key1079, 2), (key1158, 2), (key1056, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1144, -2)]

theorem rawRowCheck12479 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form18 = rawRow12479 := by decide +kernel

def row12479 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

theorem rowCheck12479 : row12479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12479 := by decide +kernel

theorem rowEval12479 (x : Key → ℝ) : Integer.Sparse.eval row12479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12479, Integer.Sparse.eval_collectBalanced, rawRowCheck12479]

def rawRow12480 : Integer.Sparse Key := [(key1065, 2), (key1079, 2), (key1065, 2), (key1065, 2), (key1158, 2), (key1065, 2), (key1079, 2), (key1065, 2), (key1158, 2), (key1065, 2), (key1158, 2), (key1079, 2), (key1064, -2), (key1056, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1144, -2), (key1064, -2)]

theorem rawRowCheck12480 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form18 = rawRow12480 := by decide +kernel

def row12480 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

theorem rowCheck12480 : row12480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12480 := by decide +kernel

theorem rowEval12480 (x : Key → ℝ) : Integer.Sparse.eval row12480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12480, Integer.Sparse.eval_collectBalanced, rawRowCheck12480]

def rawRow12481 : Integer.Sparse Key := [(key1079, 2), (key1065, 2), (key1065, 2), (key1158, 2), (key1065, 2), (key1065, 2), (key1158, 2), (key1158, 2), (key1079, 2), (key1079, 2), (key1065, 2), (key1065, 2), (key1064, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1064, -2)]

theorem rawRowCheck12481 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form18 = rawRow12481 := by decide +kernel

def row12481 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

theorem rowCheck12481 : row12481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12481 := by decide +kernel

theorem rowEval12481 (x : Key → ℝ) : Integer.Sparse.eval row12481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12481, Integer.Sparse.eval_collectBalanced, rawRowCheck12481]

def rawRow12482 : Integer.Sparse Key := [(key1158, 2), (key1158, 2), (key1158, 2), (key1079, 2), (key1079, 2), (key1079, 2), (key1065, 2), (key1065, 2), (key1065, 2), (key1065, 2), (key1065, 2), (key1065, 2), (key1144, -2), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1056, -2)]

theorem rawRowCheck12482 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form18 = rawRow12482 := by decide +kernel

def row12482 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

theorem rowCheck12482 : row12482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12482 := by decide +kernel

theorem rowEval12482 (x : Key → ℝ) : Integer.Sparse.eval row12482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12482, Integer.Sparse.eval_collectBalanced, rawRowCheck12482]

def rawRow12483 : Integer.Sparse Key := [(key3085, -4), (key3085, -4), (key3100, -4), (key3085, -4), (key3100, -4), (key3100, -4), (key3080, 6), (key3087, 6), (key3087, 6), (key3087, 6)]

theorem rawRowCheck12483 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form19 = rawRow12483 := by decide +kernel

def row12483 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

theorem rowCheck12483 : row12483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12483 := by decide +kernel

theorem rowEval12483 (x : Key → ℝ) : Integer.Sparse.eval row12483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12483, Integer.Sparse.eval_collectBalanced, rawRowCheck12483]

def rawRow12484 : Integer.Sparse Key := [(key3085, -4), (key3100, -4), (key3085, -4), (key3100, -4), (key3085, -4), (key3100, -4), (key3087, 6), (key3080, 6), (key3087, 6), (key3087, 6)]

theorem rawRowCheck12484 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form19 = rawRow12484 := by decide +kernel

def row12484 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

theorem rowCheck12484 : row12484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12484 := by decide +kernel

theorem rowEval12484 (x : Key → ℝ) : Integer.Sparse.eval row12484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12484, Integer.Sparse.eval_collectBalanced, rawRowCheck12484]

def rawRow12485 : Integer.Sparse Key := [(key3100, -4), (key3085, -4), (key3085, -4), (key3100, -4), (key3100, -4), (key3085, -4), (key3087, 6), (key3087, 6), (key3080, 6), (key3087, 6)]

theorem rawRowCheck12485 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form19 = rawRow12485 := by decide +kernel

def row12485 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

theorem rowCheck12485 : row12485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12485 := by decide +kernel

theorem rowEval12485 (x : Key → ℝ) : Integer.Sparse.eval row12485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12485, Integer.Sparse.eval_collectBalanced, rawRowCheck12485]

def rawRow12486 : Integer.Sparse Key := [(key3100, -4), (key3100, -4), (key3100, -4), (key3085, -4), (key3085, -4), (key3085, -4), (key3087, 6), (key3087, 6), (key3087, 6), (key3080, 6)]

theorem rawRowCheck12486 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form19 = rawRow12486 := by decide +kernel

def row12486 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

theorem rowCheck12486 : row12486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12486 := by decide +kernel

theorem rowEval12486 (x : Key → ℝ) : Integer.Sparse.eval row12486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12486, Integer.Sparse.eval_collectBalanced, rawRowCheck12486]

def rawRow12487 : Integer.Sparse Key := [(key3087, -4), (key3087, -4), (key3100, -4), (key3087, -4), (key3100, -4), (key3100, -4), (key3080, 6), (key3085, 6), (key3085, 6), (key3085, 6)]

theorem rawRowCheck12487 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form19 = rawRow12487 := by decide +kernel

def row12487 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

theorem rowCheck12487 : row12487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12487 := by decide +kernel

theorem rowEval12487 (x : Key → ℝ) : Integer.Sparse.eval row12487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12487, Integer.Sparse.eval_collectBalanced, rawRowCheck12487]

def rawRow12488 : Integer.Sparse Key := [(key3087, -4), (key3100, -4), (key3087, -4), (key3100, -4), (key3087, -4), (key3100, -4), (key3085, 6), (key3080, 6), (key3085, 6), (key3085, 6)]

theorem rawRowCheck12488 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form19 = rawRow12488 := by decide +kernel

def row12488 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

theorem rowCheck12488 : row12488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12488 := by decide +kernel

theorem rowEval12488 (x : Key → ℝ) : Integer.Sparse.eval row12488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12488, Integer.Sparse.eval_collectBalanced, rawRowCheck12488]

def rawRow12489 : Integer.Sparse Key := [(key3100, -4), (key3087, -4), (key3087, -4), (key3100, -4), (key3100, -4), (key3087, -4), (key3085, 6), (key3085, 6), (key3080, 6), (key3085, 6)]

theorem rawRowCheck12489 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form19 = rawRow12489 := by decide +kernel

def row12489 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

theorem rowCheck12489 : row12489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12489 := by decide +kernel

theorem rowEval12489 (x : Key → ℝ) : Integer.Sparse.eval row12489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12489, Integer.Sparse.eval_collectBalanced, rawRowCheck12489]

def rawRow12490 : Integer.Sparse Key := [(key3100, -4), (key3100, -4), (key3100, -4), (key3087, -4), (key3087, -4), (key3087, -4), (key3085, 6), (key3085, 6), (key3085, 6), (key3080, 6)]

theorem rawRowCheck12490 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form19 = rawRow12490 := by decide +kernel

def row12490 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

theorem rowCheck12490 : row12490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12490 := by decide +kernel

theorem rowEval12490 (x : Key → ℝ) : Integer.Sparse.eval row12490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12490, Integer.Sparse.eval_collectBalanced, rawRowCheck12490]

def rawRow12491 : Integer.Sparse Key := [(key1943, 6), (key1946, 6), (key1946, 6), (key1946, 6), (key1944, -24)]

theorem rawRowCheck12491 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form20 = rawRow12491 := by decide +kernel

def row12491 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

theorem rowCheck12491 : row12491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12491 := by decide +kernel

theorem rowEval12491 (x : Key → ℝ) : Integer.Sparse.eval row12491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12491, Integer.Sparse.eval_collectBalanced, rawRowCheck12491]

def rawRow12492 : Integer.Sparse Key := [(key1946, 6), (key1943, 6), (key1946, 6), (key1946, 6), (key1944, -24)]

theorem rawRowCheck12492 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form20 = rawRow12492 := by decide +kernel

def row12492 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

theorem rowCheck12492 : row12492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12492 := by decide +kernel

theorem rowEval12492 (x : Key → ℝ) : Integer.Sparse.eval row12492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12492, Integer.Sparse.eval_collectBalanced, rawRowCheck12492]

def rawRow12493 : Integer.Sparse Key := [(key1946, 6), (key1946, 6), (key1943, 6), (key1946, 6), (key1944, -24)]

theorem rawRowCheck12493 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form20 = rawRow12493 := by decide +kernel

def row12493 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

theorem rowCheck12493 : row12493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12493 := by decide +kernel

theorem rowEval12493 (x : Key → ℝ) : Integer.Sparse.eval row12493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12493, Integer.Sparse.eval_collectBalanced, rawRowCheck12493]

def rawRow12494 : Integer.Sparse Key := [(key1946, 6), (key1946, 6), (key1946, 6), (key1943, 6), (key1944, -24)]

theorem rawRowCheck12494 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form20 = rawRow12494 := by decide +kernel

def row12494 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

theorem rowCheck12494 : row12494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12494 := by decide +kernel

theorem rowEval12494 (x : Key → ℝ) : Integer.Sparse.eval row12494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12494, Integer.Sparse.eval_collectBalanced, rawRowCheck12494]

def rawRow12495 : Integer.Sparse Key := [(key1944, 6), (key1946, 6), (key1946, 6), (key1946, 6), (key1943, -24)]

theorem rawRowCheck12495 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form20 = rawRow12495 := by decide +kernel

def row12495 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

theorem rowCheck12495 : row12495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12495 := by decide +kernel

theorem rowEval12495 (x : Key → ℝ) : Integer.Sparse.eval row12495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12495, Integer.Sparse.eval_collectBalanced, rawRowCheck12495]

def rawRow12496 : Integer.Sparse Key := [(key1946, 6), (key1944, 6), (key1946, 6), (key1946, 6), (key1943, -24)]

theorem rawRowCheck12496 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form20 = rawRow12496 := by decide +kernel

def row12496 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

theorem rowCheck12496 : row12496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12496 := by decide +kernel

theorem rowEval12496 (x : Key → ℝ) : Integer.Sparse.eval row12496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12496, Integer.Sparse.eval_collectBalanced, rawRowCheck12496]

def rawRow12497 : Integer.Sparse Key := [(key1946, 6), (key1946, 6), (key1944, 6), (key1946, 6), (key1943, -24)]

theorem rawRowCheck12497 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form20 = rawRow12497 := by decide +kernel

def row12497 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

theorem rowCheck12497 : row12497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12497 := by decide +kernel

theorem rowEval12497 (x : Key → ℝ) : Integer.Sparse.eval row12497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12497, Integer.Sparse.eval_collectBalanced, rawRowCheck12497]

def rawRow12498 : Integer.Sparse Key := [(key1946, 6), (key1946, 6), (key1946, 6), (key1944, 6), (key1943, -24)]

theorem rawRowCheck12498 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form20 = rawRow12498 := by decide +kernel

def row12498 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

theorem rowCheck12498 : row12498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12498 := by decide +kernel

theorem rowEval12498 (x : Key → ℝ) : Integer.Sparse.eval row12498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12498, Integer.Sparse.eval_collectBalanced, rawRowCheck12498]

def rawRow12499 : Integer.Sparse Key := [(key2679, 1), (key2689, 1), (key2679, 1), (key2742, 1), (key2689, 1), (key2742, 1), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3047, 1), (key3072, 1), (key3047, 1), (key3110, 1), (key3072, 1), (key3110, 1), (key3054, 1), (key3072, 1), (key3054, 1), (key3110, 1), (key3072, 1), (key3110, 1), (key3050, -2), (key3050, -2), (key3066, -2), (key3050, -2), (key3050, -2), (key3103, -2), (key3050, -2), (key3066, -2), (key3050, -2), (key3103, -2), (key3066, -2), (key3103, -2)]

theorem rawRowCheck12499 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form21 = rawRow12499 := by decide +kernel

def row12499 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2742, 2), (key3047, 3), (key3050, -12), (key3054, 3), (key3066, -6), (key3072, 4), (key3103, -6), (key3110, 6)]

theorem rowCheck12499 : row12499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12499 := by decide +kernel

theorem rowEval12499 (x : Key → ℝ) : Integer.Sparse.eval row12499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12499, Integer.Sparse.eval_collectBalanced, rawRowCheck12499]

def rawRow12500 : Integer.Sparse Key := [(key2689, 1), (key2679, 1), (key2742, 1), (key2679, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3072, 1), (key3047, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3054, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3072, 1), (key3050, -2), (key3066, -2), (key3050, -2), (key3050, -2), (key3103, -2), (key3050, -2), (key3066, -2), (key3050, -2), (key3103, -2), (key3050, -2), (key3103, -2), (key3066, -2)]

theorem rawRowCheck12500 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form21 = rawRow12500 := by decide +kernel

def row12500 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2742, 2), (key3047, 3), (key3050, -12), (key3054, 3), (key3066, -6), (key3072, 4), (key3103, -6), (key3110, 6)]

theorem rowCheck12500 : row12500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12500 := by decide +kernel

theorem rowEval12500 (x : Key → ℝ) : Integer.Sparse.eval row12500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12500, Integer.Sparse.eval_collectBalanced, rawRowCheck12500]

def rawRow12501 : Integer.Sparse Key := [(key2742, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key2679, 1), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3110, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3047, 1), (key3047, 1), (key3110, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3054, 1), (key3054, 1), (key3066, -2), (key3050, -2), (key3050, -2), (key3103, -2), (key3050, -2), (key3050, -2), (key3103, -2), (key3103, -2), (key3066, -2), (key3066, -2), (key3050, -2), (key3050, -2)]

theorem rawRowCheck12501 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form21 = rawRow12501 := by decide +kernel

def row12501 : Integer.Sparse Key := [(key2679, 3), (key2689, 4), (key2742, 2), (key2955, 2), (key3047, 3), (key3050, -12), (key3054, 2), (key3066, -6), (key3072, 4), (key3103, -6), (key3110, 4)]

theorem rowCheck12501 : row12501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12501 := by decide +kernel

theorem rowEval12501 (x : Key → ℝ) : Integer.Sparse.eval row12501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12501, Integer.Sparse.eval_collectBalanced, rawRowCheck12501]

def rawRow12502 : Integer.Sparse Key := [(key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key2679, 1), (key2679, 1), (key3047, 1), (key3047, 1), (key3047, 1), (key3103, -2), (key3103, -2), (key3103, -2), (key3066, -2), (key3066, -2), (key3066, -2), (key3050, -2), (key3050, -2), (key3050, -2), (key3050, -2), (key3050, -2), (key3050, -2)]

theorem rawRowCheck12502 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form21 = rawRow12502 := by decide +kernel

def row12502 : Integer.Sparse Key := [(key2679, 3), (key2689, 6), (key2742, 6), (key2955, 6), (key3047, 3), (key3050, -12), (key3066, -6), (key3103, -6)]

theorem rowCheck12502 : row12502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12502 := by decide +kernel

theorem rowEval12502 (x : Key → ℝ) : Integer.Sparse.eval row12502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12502, Integer.Sparse.eval_collectBalanced, rawRowCheck12502]

def rawRow12503 : Integer.Sparse Key := [(key2682, 1), (key2689, 1), (key2682, 1), (key2715, 1), (key2689, 1), (key2715, 1), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2682, 1), (key2715, 1), (key2682, 1), (key2818, 1), (key2715, 1), (key2818, 1), (key2689, 1), (key2715, 1), (key2689, 1), (key2818, 1), (key2715, 1), (key2818, 1), (key2679, -2), (key2679, -2), (key2710, -2), (key2679, -2), (key3047, -2), (key3096, -2), (key3047, -2), (key3061, -2), (key3047, -2), (key3096, -2), (key3061, -2), (key3096, -2)]

theorem rawRowCheck12503 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form21 = rawRow12503 := by decide +kernel

def row12503 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -2), (key2715, 6), (key2818, 6), (key3047, -6), (key3061, -4), (key3096, -6)]

theorem rowCheck12503 : row12503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12503 := by decide +kernel

theorem rowEval12503 (x : Key → ℝ) : Integer.Sparse.eval row12503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12503, Integer.Sparse.eval_collectBalanced, rawRowCheck12503]

def rawRow12504 : Integer.Sparse Key := [(key2689, 1), (key2682, 1), (key2715, 1), (key2682, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2715, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2715, 1), (key2679, -2), (key2710, -2), (key2679, -2), (key2679, -2), (key3096, -2), (key3047, -2), (key3061, -2), (key3047, -2), (key3096, -2), (key3047, -2), (key3096, -2), (key3061, -2)]

theorem rawRowCheck12504 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form21 = rawRow12504 := by decide +kernel

def row12504 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -2), (key2715, 6), (key2818, 6), (key3047, -6), (key3061, -4), (key3096, -6)]

theorem rowCheck12504 : row12504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12504 := by decide +kernel

theorem rowEval12504 (x : Key → ℝ) : Integer.Sparse.eval row12504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12504, Integer.Sparse.eval_collectBalanced, rawRowCheck12504]

def rawRow12505 : Integer.Sparse Key := [(key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2710, -2), (key2679, -2), (key2679, -2), (key2813, -2), (key2679, -2), (key3047, -2), (key3096, -2), (key3096, -2), (key3061, -2), (key3061, -2), (key3047, -2), (key3047, -2)]

theorem rawRowCheck12505 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form21 = rawRow12505 := by decide +kernel

def row12505 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -2), (key2715, 6), (key2813, -2), (key2818, 6), (key3047, -6), (key3061, -4), (key3096, -4)]

theorem rowCheck12505 : row12505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12505 := by decide +kernel

theorem rowEval12505 (x : Key → ℝ) : Integer.Sparse.eval row12505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12505, Integer.Sparse.eval_collectBalanced, rawRowCheck12505]

def rawRow12506 : Integer.Sparse Key := [(key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2813, -2), (key2813, -2), (key2813, -2), (key2710, -2), (key2710, -2), (key2710, -2), (key2679, -2), (key2679, -2), (key2679, -2), (key3047, -2), (key3047, -2), (key3047, -2)]

theorem rawRowCheck12506 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form21 = rawRow12506 := by decide +kernel

def row12506 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -6), (key2715, 6), (key2813, -6), (key2818, 6), (key3047, -6)]

theorem rowCheck12506 : row12506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12506 := by decide +kernel

theorem rowEval12506 (x : Key → ℝ) : Integer.Sparse.eval row12506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12506, Integer.Sparse.eval_collectBalanced, rawRowCheck12506]

def rawRow12507 : Integer.Sparse Key := [(key2710, -2), (key2715, -2), (key2715, -2), (key2710, -2), (key2715, -2), (key2710, -2), (key2979, -2), (key2715, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2979, -2), (key2679, 1), (key2689, 1), (key2679, 1), (key2742, 1), (key2689, 1), (key2742, 1), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3047, 1), (key3072, 1), (key3047, 1), (key3110, 1), (key3072, 1), (key3110, 1), (key3054, 1), (key3072, 1), (key3054, 1), (key3110, 1), (key3072, 1), (key3110, 1)]

theorem rawRowCheck12507 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form22 = rawRow12507 := by decide +kernel

def row12507 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2710, -6), (key2715, -12), (key2742, 2), (key2979, -6), (key3047, 3), (key3054, 3), (key3072, 4), (key3110, 6)]

theorem rowCheck12507 : row12507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12507 := by decide +kernel

theorem rowEval12507 (x : Key → ℝ) : Integer.Sparse.eval row12507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12507, Integer.Sparse.eval_collectBalanced, rawRowCheck12507]

def rawRow12508 : Integer.Sparse Key := [(key2715, -2), (key2710, -2), (key2715, -2), (key2715, -2), (key2710, -2), (key2979, -2), (key2710, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2979, -2), (key2715, -2), (key2689, 1), (key2679, 1), (key2742, 1), (key2679, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3072, 1), (key3047, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3054, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3072, 1)]

theorem rawRowCheck12508 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form22 = rawRow12508 := by decide +kernel

def row12508 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2710, -6), (key2715, -12), (key2742, 2), (key2979, -6), (key3047, 3), (key3054, 3), (key3072, 4), (key3110, 6)]

theorem rowCheck12508 : row12508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12508 := by decide +kernel

theorem rowEval12508 (x : Key → ℝ) : Integer.Sparse.eval row12508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12508, Integer.Sparse.eval_collectBalanced, rawRowCheck12508]

def rawRow12509 : Integer.Sparse Key := [(key2715, -2), (key2715, -2), (key2710, -2), (key2979, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2710, -2), (key2710, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2742, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key2679, 1), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3110, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3047, 1), (key3047, 1), (key3110, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3054, 1), (key3054, 1)]

theorem rawRowCheck12509 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form22 = rawRow12509 := by decide +kernel

def row12509 : Integer.Sparse Key := [(key2679, 3), (key2689, 4), (key2710, -6), (key2715, -12), (key2742, 2), (key2955, 2), (key2979, -6), (key3047, 3), (key3054, 2), (key3072, 4), (key3110, 4)]

theorem rowCheck12509 : row12509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12509 := by decide +kernel

theorem rowEval12509 (x : Key → ℝ) : Integer.Sparse.eval row12509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12509, Integer.Sparse.eval_collectBalanced, rawRowCheck12509]

def rawRow12510 : Integer.Sparse Key := [(key2979, -2), (key2979, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2715, -2), (key2715, -2), (key2715, -2), (key2715, -2), (key2710, -2), (key2710, -2), (key2710, -2), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key2679, 1), (key2679, 1), (key3047, 1), (key3047, 1), (key3047, 1)]

theorem rawRowCheck12510 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form22 = rawRow12510 := by decide +kernel

def row12510 : Integer.Sparse Key := [(key2679, 3), (key2689, 6), (key2710, -6), (key2715, -12), (key2742, 6), (key2955, 6), (key2979, -6), (key3047, 3)]

theorem rowCheck12510 : row12510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12510 := by decide +kernel

theorem rowEval12510 (x : Key → ℝ) : Integer.Sparse.eval row12510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12510, Integer.Sparse.eval_collectBalanced, rawRowCheck12510]

def rawRow12511 : Integer.Sparse Key := [(key2740, -2), (key2742, -2), (key2742, -2), (key2740, -2), (key2742, -2), (key2740, -2), (key2900, -2), (key2742, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2900, -2), (key2682, 1), (key2689, 1), (key2682, 1), (key2715, 1), (key2689, 1), (key2715, 1), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2682, 1), (key2715, 1), (key2682, 1), (key2818, 1), (key2715, 1), (key2818, 1), (key2689, 1), (key2715, 1), (key2689, 1), (key2818, 1), (key2715, 1), (key2818, 1)]

theorem rawRowCheck12511 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form22 = rawRow12511 := by decide +kernel

def row12511 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

theorem rowCheck12511 : row12511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12511 := by decide +kernel

theorem rowEval12511 (x : Key → ℝ) : Integer.Sparse.eval row12511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12511, Integer.Sparse.eval_collectBalanced, rawRowCheck12511]

def rawRow12512 : Integer.Sparse Key := [(key2742, -2), (key2740, -2), (key2742, -2), (key2742, -2), (key2740, -2), (key2900, -2), (key2740, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2900, -2), (key2742, -2), (key2689, 1), (key2682, 1), (key2715, 1), (key2682, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2715, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2715, 1)]

theorem rawRowCheck12512 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form22 = rawRow12512 := by decide +kernel

def row12512 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

theorem rowCheck12512 : row12512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12512 := by decide +kernel

theorem rowEval12512 (x : Key → ℝ) : Integer.Sparse.eval row12512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12512, Integer.Sparse.eval_collectBalanced, rawRowCheck12512]

def rawRow12513 : Integer.Sparse Key := [(key2742, -2), (key2742, -2), (key2740, -2), (key2900, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2740, -2), (key2740, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1)]

theorem rawRowCheck12513 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form22 = rawRow12513 := by decide +kernel

def row12513 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

theorem rowCheck12513 : row12513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12513 := by decide +kernel

theorem rowEval12513 (x : Key → ℝ) : Integer.Sparse.eval row12513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12513, Integer.Sparse.eval_collectBalanced, rawRowCheck12513]

def rawRow12514 : Integer.Sparse Key := [(key2900, -2), (key2900, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2742, -2), (key2742, -2), (key2742, -2), (key2742, -2), (key2740, -2), (key2740, -2), (key2740, -2), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1)]

theorem rawRowCheck12514 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form22 = rawRow12514 := by decide +kernel

def row12514 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

theorem rowCheck12514 : row12514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12514 := by decide +kernel

theorem rowEval12514 (x : Key → ℝ) : Integer.Sparse.eval row12514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form22) x := by
  rw [rowCheck12514, Integer.Sparse.eval_collectBalanced, rawRowCheck12514]

def rawRow12515 : Integer.Sparse Key := [(key2496, -4), (key2496, -4), (key2508, -4), (key2496, -4), (key2508, -4), (key2508, -4), (key2428, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2556, 2), (key2442, 2), (key2556, 2)]

theorem rawRowCheck12515 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form23 = rawRow12515 := by decide +kernel

def row12515 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

theorem rowCheck12515 : row12515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12515 := by decide +kernel

theorem rowEval12515 (x : Key → ℝ) : Integer.Sparse.eval row12515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12515, Integer.Sparse.eval_collectBalanced, rawRowCheck12515]

def rawRow12516 : Integer.Sparse Key := [(key2496, -4), (key2508, -4), (key2496, -4), (key2508, -4), (key2496, -4), (key2508, -4), (key2428, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2556, 2), (key2442, 2)]

theorem rawRowCheck12516 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form23 = rawRow12516 := by decide +kernel

def row12516 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

theorem rowCheck12516 : row12516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12516 := by decide +kernel

theorem rowEval12516 (x : Key → ℝ) : Integer.Sparse.eval row12516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12516, Integer.Sparse.eval_collectBalanced, rawRowCheck12516]

def rawRow12517 : Integer.Sparse Key := [(key2508, -4), (key2496, -4), (key2496, -4), (key2508, -4), (key2508, -4), (key2496, -4), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2556, 2), (key2442, 2), (key2442, 2), (key2428, 2), (key2428, 2)]

theorem rawRowCheck12517 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form23 = rawRow12517 := by decide +kernel

def row12517 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

theorem rowCheck12517 : row12517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12517 := by decide +kernel

theorem rowEval12517 (x : Key → ℝ) : Integer.Sparse.eval row12517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12517, Integer.Sparse.eval_collectBalanced, rawRowCheck12517]

def rawRow12518 : Integer.Sparse Key := [(key2508, -4), (key2508, -4), (key2508, -4), (key2496, -4), (key2496, -4), (key2496, -4), (key2556, 2), (key2556, 2), (key2556, 2), (key2442, 2), (key2442, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2)]

theorem rawRowCheck12518 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form23 = rawRow12518 := by decide +kernel

def row12518 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

theorem rowCheck12518 : row12518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12518 := by decide +kernel

theorem rowEval12518 (x : Key → ℝ) : Integer.Sparse.eval row12518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12518, Integer.Sparse.eval_collectBalanced, rawRowCheck12518]

def rawRow12519 : Integer.Sparse Key := [(key2550, -4), (key2550, -4), (key2556, -4), (key2550, -4), (key2556, -4), (key2556, -4), (key2429, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2508, 2), (key2442, 2), (key2508, 2)]

theorem rawRowCheck12519 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form23 = rawRow12519 := by decide +kernel

def row12519 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

theorem rowCheck12519 : row12519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12519 := by decide +kernel

theorem rowEval12519 (x : Key → ℝ) : Integer.Sparse.eval row12519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12519, Integer.Sparse.eval_collectBalanced, rawRowCheck12519]

def rawRow12520 : Integer.Sparse Key := [(key2550, -4), (key2556, -4), (key2550, -4), (key2556, -4), (key2550, -4), (key2556, -4), (key2429, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2508, 2), (key2442, 2)]

theorem rawRowCheck12520 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form23 = rawRow12520 := by decide +kernel

def row12520 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

theorem rowCheck12520 : row12520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12520 := by decide +kernel

theorem rowEval12520 (x : Key → ℝ) : Integer.Sparse.eval row12520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12520, Integer.Sparse.eval_collectBalanced, rawRowCheck12520]

def rawRow12521 : Integer.Sparse Key := [(key2556, -4), (key2550, -4), (key2550, -4), (key2556, -4), (key2556, -4), (key2550, -4), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2508, 2), (key2442, 2), (key2442, 2), (key2429, 2), (key2429, 2)]

theorem rawRowCheck12521 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form23 = rawRow12521 := by decide +kernel

def row12521 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

theorem rowCheck12521 : row12521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12521 := by decide +kernel

theorem rowEval12521 (x : Key → ℝ) : Integer.Sparse.eval row12521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12521, Integer.Sparse.eval_collectBalanced, rawRowCheck12521]

def rawRow12522 : Integer.Sparse Key := [(key2556, -4), (key2556, -4), (key2556, -4), (key2550, -4), (key2550, -4), (key2550, -4), (key2508, 2), (key2508, 2), (key2508, 2), (key2442, 2), (key2442, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2)]

theorem rawRowCheck12522 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form23 = rawRow12522 := by decide +kernel

def row12522 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

theorem rowCheck12522 : row12522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12522 := by decide +kernel

theorem rowEval12522 (x : Key → ℝ) : Integer.Sparse.eval row12522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form23) x := by
  rw [rowCheck12522, Integer.Sparse.eval_collectBalanced, rawRowCheck12522]

def rawRow12523 : Integer.Sparse Key := [(key1731, -24), (key1499, 6), (key1499, 6), (key1499, 6), (key1873, 6)]

theorem rawRowCheck12523 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form24 = rawRow12523 := by decide +kernel

def row12523 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

theorem rowCheck12523 : row12523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12523 := by decide +kernel

theorem rowEval12523 (x : Key → ℝ) : Integer.Sparse.eval row12523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12523, Integer.Sparse.eval_collectBalanced, rawRowCheck12523]

def rawRow12524 : Integer.Sparse Key := [(key1731, -24), (key1499, 6), (key1499, 6), (key1873, 6), (key1499, 6)]

theorem rawRowCheck12524 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form24 = rawRow12524 := by decide +kernel

def row12524 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

theorem rowCheck12524 : row12524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12524 := by decide +kernel

theorem rowEval12524 (x : Key → ℝ) : Integer.Sparse.eval row12524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12524, Integer.Sparse.eval_collectBalanced, rawRowCheck12524]

def rawRow12525 : Integer.Sparse Key := [(key1731, -24), (key1499, 6), (key1873, 6), (key1499, 6), (key1499, 6)]

theorem rawRowCheck12525 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form24 = rawRow12525 := by decide +kernel

def row12525 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

theorem rowCheck12525 : row12525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12525 := by decide +kernel

theorem rowEval12525 (x : Key → ℝ) : Integer.Sparse.eval row12525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12525, Integer.Sparse.eval_collectBalanced, rawRowCheck12525]

def rawRow12526 : Integer.Sparse Key := [(key1731, -24), (key1873, 6), (key1499, 6), (key1499, 6), (key1499, 6)]

theorem rawRowCheck12526 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form24 = rawRow12526 := by decide +kernel

def row12526 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

theorem rowCheck12526 : row12526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12526 := by decide +kernel

theorem rowEval12526 (x : Key → ℝ) : Integer.Sparse.eval row12526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12526, Integer.Sparse.eval_collectBalanced, rawRowCheck12526]

def rawRow12527 : Integer.Sparse Key := [(key1873, -24), (key1499, 6), (key1499, 6), (key1499, 6), (key1731, 6)]

theorem rawRowCheck12527 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form24 = rawRow12527 := by decide +kernel

def row12527 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

theorem rowCheck12527 : row12527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12527 := by decide +kernel

theorem rowEval12527 (x : Key → ℝ) : Integer.Sparse.eval row12527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12527, Integer.Sparse.eval_collectBalanced, rawRowCheck12527]

def rawRow12528 : Integer.Sparse Key := [(key1873, -24), (key1499, 6), (key1499, 6), (key1731, 6), (key1499, 6)]

theorem rawRowCheck12528 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form24 = rawRow12528 := by decide +kernel

def row12528 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

theorem rowCheck12528 : row12528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12528 := by decide +kernel

theorem rowEval12528 (x : Key → ℝ) : Integer.Sparse.eval row12528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12528, Integer.Sparse.eval_collectBalanced, rawRowCheck12528]

def rawRow12529 : Integer.Sparse Key := [(key1873, -24), (key1499, 6), (key1731, 6), (key1499, 6), (key1499, 6)]

theorem rawRowCheck12529 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form24 = rawRow12529 := by decide +kernel

def row12529 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

theorem rowCheck12529 : row12529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12529 := by decide +kernel

theorem rowEval12529 (x : Key → ℝ) : Integer.Sparse.eval row12529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12529, Integer.Sparse.eval_collectBalanced, rawRowCheck12529]

def rawRow12530 : Integer.Sparse Key := [(key1873, -24), (key1731, 6), (key1499, 6), (key1499, 6), (key1499, 6)]

theorem rawRowCheck12530 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form24 = rawRow12530 := by decide +kernel

def row12530 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

theorem rowCheck12530 : row12530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12530 := by decide +kernel

theorem rowEval12530 (x : Key → ℝ) : Integer.Sparse.eval row12530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12530, Integer.Sparse.eval_collectBalanced, rawRowCheck12530]

def rawRow12531 : Integer.Sparse Key := [(key3081, 6), (key3091, 6), (key3091, 6), (key3091, 6), (key3082, -6), (key3088, -6), (key3088, -6), (key3088, -6)]

theorem rawRowCheck12531 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form25 = rawRow12531 := by decide +kernel

def row12531 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

theorem rowCheck12531 : row12531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12531 := by decide +kernel

theorem rowEval12531 (x : Key → ℝ) : Integer.Sparse.eval row12531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12531, Integer.Sparse.eval_collectBalanced, rawRowCheck12531]

def rawRow12532 : Integer.Sparse Key := [(key3091, 6), (key3081, 6), (key3091, 6), (key3091, 6), (key3088, -6), (key3082, -6), (key3088, -6), (key3088, -6)]

theorem rawRowCheck12532 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form25 = rawRow12532 := by decide +kernel

def row12532 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

theorem rowCheck12532 : row12532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12532 := by decide +kernel

theorem rowEval12532 (x : Key → ℝ) : Integer.Sparse.eval row12532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12532, Integer.Sparse.eval_collectBalanced, rawRowCheck12532]

def rawRow12533 : Integer.Sparse Key := [(key3091, 6), (key3091, 6), (key3081, 6), (key3091, 6), (key3088, -6), (key3088, -6), (key3082, -6), (key3088, -6)]

theorem rawRowCheck12533 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form25 = rawRow12533 := by decide +kernel

def row12533 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

theorem rowCheck12533 : row12533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12533 := by decide +kernel

theorem rowEval12533 (x : Key → ℝ) : Integer.Sparse.eval row12533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12533, Integer.Sparse.eval_collectBalanced, rawRowCheck12533]

def rawRow12534 : Integer.Sparse Key := [(key3091, 6), (key3091, 6), (key3091, 6), (key3081, 6), (key3088, -6), (key3088, -6), (key3088, -6), (key3082, -6)]

theorem rawRowCheck12534 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form25 = rawRow12534 := by decide +kernel

def row12534 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

theorem rowCheck12534 : row12534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12534 := by decide +kernel

theorem rowEval12534 (x : Key → ℝ) : Integer.Sparse.eval row12534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12534, Integer.Sparse.eval_collectBalanced, rawRowCheck12534]

def rawRow12535 : Integer.Sparse Key := [(key3082, 6), (key3088, 6), (key3088, 6), (key3088, 6), (key3081, -6), (key3086, -6), (key3086, -6), (key3086, -6)]

theorem rawRowCheck12535 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form25 = rawRow12535 := by decide +kernel

def row12535 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

theorem rowCheck12535 : row12535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12535 := by decide +kernel

theorem rowEval12535 (x : Key → ℝ) : Integer.Sparse.eval row12535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form25) x := by
  rw [rowCheck12535, Integer.Sparse.eval_collectBalanced, rawRowCheck12535]

def rawRow12536 : Integer.Sparse Key := [(key3088, 6), (key3082, 6), (key3088, 6), (key3088, 6), (key3086, -6), (key3081, -6), (key3086, -6), (key3086, -6)]

theorem rawRowCheck12536 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form25 = rawRow12536 := by decide +kernel

def row12536 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

theorem rowCheck12536 : row12536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12536 := by decide +kernel

theorem rowEval12536 (x : Key → ℝ) : Integer.Sparse.eval row12536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12536, Integer.Sparse.eval_collectBalanced, rawRowCheck12536]

def rawRow12537 : Integer.Sparse Key := [(key3088, 6), (key3088, 6), (key3082, 6), (key3088, 6), (key3086, -6), (key3086, -6), (key3081, -6), (key3086, -6)]

theorem rawRowCheck12537 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form25 = rawRow12537 := by decide +kernel

def row12537 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

theorem rowCheck12537 : row12537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12537 := by decide +kernel

theorem rowEval12537 (x : Key → ℝ) : Integer.Sparse.eval row12537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12537, Integer.Sparse.eval_collectBalanced, rawRowCheck12537]

def rawRow12538 : Integer.Sparse Key := [(key3088, 6), (key3088, 6), (key3088, 6), (key3082, 6), (key3086, -6), (key3086, -6), (key3086, -6), (key3081, -6)]

theorem rawRowCheck12538 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form25 = rawRow12538 := by decide +kernel

def row12538 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

theorem rowCheck12538 : row12538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12538 := by decide +kernel

theorem rowEval12538 (x : Key → ℝ) : Integer.Sparse.eval row12538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form25) x := by
  rw [rowCheck12538, Integer.Sparse.eval_collectBalanced, rawRowCheck12538]

def rawRow12539 : Integer.Sparse Key := [(key1280, 2), (key1284, 2), (key1284, 2), (key1703, 2), (key1757, 2), (key1757, 2), (key1856, 2), (key1856, 2), (key1887, 2), (key1887, 2), (key1890, 2), (key1890, 2), (key1284, -2), (key1284, -2), (key1286, -2), (key1707, -2), (key1707, -2), (key1757, -2), (key1757, -2), (key1760, -2), (key1760, -2), (key1858, -2), (key1890, -2), (key1890, -2)]

theorem rawRowCheck12539 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form0 = rawRow12539 := by decide +kernel

def row12539 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12539 : row12539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12539 := by decide +kernel

theorem rowEval12539 (x : Key → ℝ) : Integer.Sparse.eval row12539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12539, Integer.Sparse.eval_collectBalanced, rawRowCheck12539]

def rawRow12540 : Integer.Sparse Key := [(key1284, 2), (key1280, 2), (key1284, 2), (key1757, 2), (key1703, 2), (key1757, 2), (key1887, 2), (key1890, 2), (key1856, 2), (key1890, 2), (key1856, 2), (key1887, 2), (key1284, -2), (key1286, -2), (key1284, -2), (key1757, -2), (key1760, -2), (key1707, -2), (key1760, -2), (key1707, -2), (key1757, -2), (key1890, -2), (key1858, -2), (key1890, -2)]

theorem rawRowCheck12540 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form0 = rawRow12540 := by decide +kernel

def row12540 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12540 : row12540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12540 := by decide +kernel

theorem rowEval12540 (x : Key → ℝ) : Integer.Sparse.eval row12540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12540, Integer.Sparse.eval_collectBalanced, rawRowCheck12540]

def rawRow12541 : Integer.Sparse Key := [(key1284, 2), (key1284, 2), (key1280, 2), (key1757, 2), (key1757, 2), (key1703, 2), (key1890, 2), (key1887, 2), (key1890, 2), (key1856, 2), (key1887, 2), (key1856, 2), (key1286, -2), (key1284, -2), (key1284, -2), (key1760, -2), (key1757, -2), (key1760, -2), (key1707, -2), (key1757, -2), (key1707, -2), (key1890, -2), (key1890, -2), (key1858, -2)]

theorem rawRowCheck12541 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form0 = rawRow12541 := by decide +kernel

def row12541 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12541 : row12541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12541 := by decide +kernel

theorem rowEval12541 (x : Key → ℝ) : Integer.Sparse.eval row12541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12541, Integer.Sparse.eval_collectBalanced, rawRowCheck12541]

def rawRow12542 : Integer.Sparse Key := [(key1703, 2), (key1856, 2), (key1856, 2), (key1280, 2), (key1887, 2), (key1887, 2), (key1284, 2), (key1284, 2), (key1757, 2), (key1757, 2), (key1890, 2), (key1890, 2), (key1707, -2), (key1707, -2), (key1858, -2), (key1284, -2), (key1284, -2), (key1757, -2), (key1757, -2), (key1890, -2), (key1890, -2), (key1286, -2), (key1760, -2), (key1760, -2)]

theorem rawRowCheck12542 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form0 = rawRow12542 := by decide +kernel

def row12542 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12542 : row12542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12542 := by decide +kernel

theorem rowEval12542 (x : Key → ℝ) : Integer.Sparse.eval row12542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12542, Integer.Sparse.eval_collectBalanced, rawRowCheck12542]

def rawRow12543 : Integer.Sparse Key := [(key1856, 2), (key1703, 2), (key1856, 2), (key1887, 2), (key1280, 2), (key1887, 2), (key1757, 2), (key1890, 2), (key1284, 2), (key1890, 2), (key1284, 2), (key1757, 2), (key1707, -2), (key1858, -2), (key1707, -2), (key1757, -2), (key1890, -2), (key1284, -2), (key1890, -2), (key1284, -2), (key1757, -2), (key1760, -2), (key1286, -2), (key1760, -2)]

theorem rawRowCheck12543 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form0 = rawRow12543 := by decide +kernel

def row12543 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

theorem rowCheck12543 : row12543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12543 := by decide +kernel

theorem rowEval12543 (x : Key → ℝ) : Integer.Sparse.eval row12543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12543, Integer.Sparse.eval_collectBalanced, rawRowCheck12543]

end MUB6.Certificate.GramRows

end OAI

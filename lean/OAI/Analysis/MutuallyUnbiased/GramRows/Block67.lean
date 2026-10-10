import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
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

def rawRow5504 : Integer.Sparse Key := [(key192, -4), (key189, 2), (key169, 2), (key192, 2), (key170, 2), (key169, -4), (key163, 2), (key158, -1), (key96, -1), (key192, 2), (key158, -1), (key13, -1), (key192, -1), (key170, -1), (key163, -1), (key15, -1), (key96, 2), (key13, 2), (key158, -1), (key96, -1), (key93, 2), (key189, -1), (key169, -1), (key158, 2), (key13, 2), (key93, -1), (key10, -1), (key158, 2), (key96, -1), (key13, -1)]

theorem rawRowCheck5504 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5504 := by decide +kernel

def row5504 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

theorem rowCheck5504 : row5504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5504 := by decide +kernel

theorem rowEval5504 (x : Key → ℝ) : Integer.Sparse.eval row5504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5504, Integer.Sparse.eval_collectBalanced, rawRowCheck5504]

def rawRow5505 : Integer.Sparse Key := [(key170, -4), (key192, 2), (key192, 2), (key169, 2), (key169, 2), (key189, -4), (key170, 2), (key192, -1), (key192, -1), (key15, 2), (key163, -1), (key163, -1), (key13, -1), (key13, -1), (key96, -1), (key96, -1), (key158, 2), (key158, 2), (key169, -1), (key169, -1), (key189, 2), (key13, -1), (key13, -1), (key96, 2), (key96, 2), (key158, -1), (key158, -1), (key10, 2), (key93, -1), (key93, -1)]

theorem rawRowCheck5505 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3 = rawRow5505 := by decide +kernel

def row5505 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck5505 : row5505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5505 := by decide +kernel

theorem rowEval5505 (x : Key → ℝ) : Integer.Sparse.eval row5505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5505, Integer.Sparse.eval_collectBalanced, rawRowCheck5505]

def rawRow5506 : Integer.Sparse Key := [(key192, -4), (key170, 2), (key192, 2), (key169, 2), (key189, 2), (key169, -4), (key192, 2), (key170, -1), (key192, -1), (key163, 2), (key15, -1), (key163, -1), (key96, -1), (key158, -1), (key13, -1), (key158, -1), (key13, 2), (key96, 2), (key169, -1), (key189, -1), (key169, 2), (key96, -1), (key158, -1), (key13, 2), (key158, 2), (key13, -1), (key96, -1), (key93, 2), (key10, -1), (key93, -1)]

theorem rawRowCheck5506 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3 = rawRow5506 := by decide +kernel

def row5506 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

theorem rowCheck5506 : row5506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5506 := by decide +kernel

theorem rowEval5506 (x : Key → ℝ) : Integer.Sparse.eval row5506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5506, Integer.Sparse.eval_collectBalanced, rawRowCheck5506]

def rawRow5507 : Integer.Sparse Key := [(key192, -4), (key192, 2), (key170, 2), (key189, 2), (key169, 2), (key169, -4), (key192, 2), (key192, -1), (key170, -1), (key163, 2), (key163, -1), (key15, -1), (key158, -1), (key96, -1), (key158, -1), (key13, -1), (key96, 2), (key13, 2), (key189, -1), (key169, -1), (key169, 2), (key158, -1), (key96, -1), (key158, 2), (key13, 2), (key96, -1), (key13, -1), (key93, 2), (key93, -1), (key10, -1)]

theorem rawRowCheck5507 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3 = rawRow5507 := by decide +kernel

def row5507 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

theorem rowCheck5507 : row5507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5507 := by decide +kernel

theorem rowEval5507 (x : Key → ℝ) : Integer.Sparse.eval row5507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5507, Integer.Sparse.eval_collectBalanced, rawRowCheck5507]

def rawRow5508 : Integer.Sparse Key := [(key2378, -1), (key2378, -1), (key2383, 2), (key2378, -1), (key2378, -1), (key2390, 2), (key2390, 2), (key2394, -1), (key2394, -1), (key2383, 2), (key2394, -1), (key2394, -1), (key2406, 1), (key2406, 1), (key2411, -2), (key2406, 1), (key2406, 1), (key2437, -2), (key2437, -2), (key2443, 1), (key2443, 1), (key2411, -2), (key2443, 1), (key2443, 1), (key2480, -1), (key2480, -1), (key2484, 1), (key2484, 1), (key2503, 1), (key2503, 1), (key2509, -1), (key2509, -1), (key2480, -1), (key2480, -1), (key2503, 1), (key2503, 1), (key2484, 1), (key2484, 1), (key2509, -1), (key2509, -1)]

theorem rawRowCheck5508 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form0 = rawRow5508 := by decide +kernel

def row5508 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2480, -4), (key2484, 4), (key2503, 4), (key2509, -4)]

theorem rowCheck5508 : row5508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5508 := by decide +kernel

theorem rowEval5508 (x : Key → ℝ) : Integer.Sparse.eval row5508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5508, Integer.Sparse.eval_collectBalanced, rawRowCheck5508]

def rawRow5509 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2378, 2), (key2390, -1), (key2394, -1), (key2378, 2), (key2394, 2), (key2378, -1), (key2390, -1), (key2394, 2), (key2383, -1), (key2394, -1), (key2406, 1), (key2411, 1), (key2406, -2), (key2437, 1), (key2443, 1), (key2406, -2), (key2443, -2), (key2406, 1), (key2437, 1), (key2443, -2), (key2411, 1), (key2443, 1), (key2472, -1), (key2484, -1), (key2472, 1), (key2480, 1), (key2472, 1), (key2509, 1), (key2472, -1), (key2503, -1), (key2503, -1), (key2524, -1), (key2480, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2484, -1), (key2524, -1)]

theorem rawRowCheck5509 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form0 = rawRow5509 := by decide +kernel

def row5509 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

theorem rowCheck5509 : row5509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5509 := by decide +kernel

theorem rowEval5509 (x : Key → ℝ) : Integer.Sparse.eval row5509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5509, Integer.Sparse.eval_collectBalanced, rawRowCheck5509]

def rawRow5510 : Integer.Sparse Key := [(key2383, -1), (key2378, -1), (key2378, 2), (key2394, -1), (key2390, -1), (key2394, 2), (key2378, 2), (key2390, -1), (key2378, -1), (key2394, 2), (key2394, -1), (key2383, -1), (key2411, 1), (key2406, 1), (key2406, -2), (key2443, 1), (key2437, 1), (key2443, -2), (key2406, -2), (key2437, 1), (key2406, 1), (key2443, -2), (key2443, 1), (key2411, 1), (key2484, -1), (key2472, -1), (key2480, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, -1), (key2472, -1), (key2524, -1), (key2503, -1), (key2524, 1), (key2480, 1), (key2524, 1), (key2509, 1), (key2524, -1), (key2484, -1)]

theorem rawRowCheck5510 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form0 = rawRow5510 := by decide +kernel

def row5510 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

theorem rowCheck5510 : row5510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5510 := by decide +kernel

theorem rowEval5510 (x : Key → ℝ) : Integer.Sparse.eval row5510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5510, Integer.Sparse.eval_collectBalanced, rawRowCheck5510]

def rawRow5511 : Integer.Sparse Key := [(key2390, -1), (key2394, -1), (key2394, 2), (key2378, -1), (key2383, -1), (key2378, 2), (key2394, 2), (key2383, -1), (key2394, -1), (key2378, 2), (key2378, -1), (key2390, -1), (key2437, 1), (key2443, 1), (key2443, -2), (key2406, 1), (key2411, 1), (key2406, -2), (key2443, -2), (key2411, 1), (key2443, 1), (key2406, -2), (key2406, 1), (key2437, 1), (key2503, -1), (key2524, -1), (key2509, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, -1), (key2524, -1), (key2472, -1), (key2484, -1), (key2472, 1), (key2509, 1), (key2472, 1), (key2480, 1), (key2472, -1), (key2503, -1)]

theorem rawRowCheck5511 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form0 = rawRow5511 := by decide +kernel

def row5511 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

theorem rowCheck5511 : row5511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5511 := by decide +kernel

theorem rowEval5511 (x : Key → ℝ) : Integer.Sparse.eval row5511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5511, Integer.Sparse.eval_collectBalanced, rawRowCheck5511]

def rawRow5512 : Integer.Sparse Key := [(key2394, -1), (key2390, -1), (key2394, 2), (key2383, -1), (key2378, -1), (key2394, 2), (key2378, 2), (key2394, -1), (key2383, -1), (key2378, 2), (key2390, -1), (key2378, -1), (key2443, 1), (key2437, 1), (key2443, -2), (key2411, 1), (key2406, 1), (key2443, -2), (key2406, -2), (key2443, 1), (key2411, 1), (key2406, -2), (key2437, 1), (key2406, 1), (key2524, -1), (key2503, -1), (key2524, 1), (key2509, 1), (key2524, 1), (key2480, 1), (key2524, -1), (key2484, -1), (key2484, -1), (key2472, -1), (key2509, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, -1), (key2472, -1)]

theorem rawRowCheck5512 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form0 = rawRow5512 := by decide +kernel

def row5512 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

theorem rowCheck5512 : row5512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5512 := by decide +kernel

theorem rowEval5512 (x : Key → ℝ) : Integer.Sparse.eval row5512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5512, Integer.Sparse.eval_collectBalanced, rawRowCheck5512]

def rawRow5513 : Integer.Sparse Key := [(key2394, -1), (key2394, -1), (key2390, 2), (key2394, -1), (key2394, -1), (key2383, 2), (key2383, 2), (key2378, -1), (key2378, -1), (key2390, 2), (key2378, -1), (key2378, -1), (key2443, 1), (key2443, 1), (key2437, -2), (key2443, 1), (key2443, 1), (key2411, -2), (key2411, -2), (key2406, 1), (key2406, 1), (key2437, -2), (key2406, 1), (key2406, 1), (key2509, -1), (key2509, -1), (key2503, 1), (key2503, 1), (key2484, 1), (key2484, 1), (key2480, -1), (key2480, -1), (key2509, -1), (key2509, -1), (key2484, 1), (key2484, 1), (key2503, 1), (key2503, 1), (key2480, -1), (key2480, -1)]

theorem rawRowCheck5513 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form0 = rawRow5513 := by decide +kernel

def row5513 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2480, -4), (key2484, 4), (key2503, 4), (key2509, -4)]

theorem rowCheck5513 : row5513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5513 := by decide +kernel

theorem rowEval5513 (x : Key → ℝ) : Integer.Sparse.eval row5513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5513, Integer.Sparse.eval_collectBalanced, rawRowCheck5513]

def rawRow5514 : Integer.Sparse Key := [(key2766, -1), (key2766, -1), (key2772, 2), (key2843, -1), (key2843, -1), (key2887, 2), (key2887, 2), (key2889, -1), (key2889, -1), (key2880, 2), (key2910, -1), (key2910, -1), (key2587, 1), (key2587, 1), (key2593, -2), (key2843, 1), (key2843, 1), (key2966, -2), (key2966, -2), (key2968, 1), (key2968, 1), (key2880, -2), (key2989, 1), (key2989, 1), (key2390, -1), (key2390, -1), (key2394, 1), (key2394, 1), (key2437, 1), (key2437, 1), (key2443, -1), (key2443, -1), (key2480, -1), (key2480, -1), (key2503, 1), (key2503, 1), (key2571, 1), (key2571, 1), (key2576, -1), (key2576, -1)]

theorem rawRowCheck5514 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form0 = rawRow5514 := by decide +kernel

def row5514 : Integer.Sparse Key := [(key2390, -2), (key2394, 2), (key2437, 2), (key2443, -2), (key2480, -2), (key2503, 2), (key2571, 2), (key2576, -2), (key2587, 2), (key2593, -2), (key2766, -2), (key2772, 2), (key2887, 4), (key2889, -2), (key2910, -2), (key2966, -4), (key2968, 2), (key2989, 2)]

theorem rowCheck5514 : row5514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5514 := by decide +kernel

theorem rowEval5514 (x : Key → ℝ) : Integer.Sparse.eval row5514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5514, Integer.Sparse.eval_collectBalanced, rawRowCheck5514]

def rawRow5515 : Integer.Sparse Key := [(key2766, -1), (key2772, -1), (key2766, 2), (key2887, -1), (key2889, -1), (key2843, 2), (key2889, 2), (key2843, -1), (key2887, -1), (key2910, 2), (key2880, -1), (key2910, -1), (key2587, 1), (key2593, 1), (key2587, -2), (key2966, 1), (key2968, 1), (key2843, -2), (key2968, -2), (key2843, 1), (key2966, 1), (key2989, -2), (key2880, 1), (key2989, 1), (key2378, -1), (key2394, -1), (key2378, 1), (key2390, 1), (key2406, 1), (key2443, 1), (key2406, -1), (key2437, -1), (key2503, -1), (key2524, -1), (key2480, 1), (key2524, 1), (key2576, 1), (key2580, 1), (key2571, -1), (key2580, -1)]

theorem rawRowCheck5515 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form0 = rawRow5515 := by decide +kernel

def row5515 : Integer.Sparse Key := [(key2390, 1), (key2394, -1), (key2437, -1), (key2443, 1), (key2480, 1), (key2503, -1), (key2571, -1), (key2576, 1), (key2587, -1), (key2593, 1), (key2766, 1), (key2772, -1), (key2887, -2), (key2889, 1), (key2910, 1), (key2966, 2), (key2968, -1), (key2989, -1)]

theorem rowCheck5515 : row5515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5515 := by decide +kernel

theorem rowEval5515 (x : Key → ℝ) : Integer.Sparse.eval row5515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5515, Integer.Sparse.eval_collectBalanced, rawRowCheck5515]

def rawRow5516 : Integer.Sparse Key := [(key2772, -1), (key2766, -1), (key2766, 2), (key2889, -1), (key2887, -1), (key2889, 2), (key2843, 2), (key2887, -1), (key2843, -1), (key2910, 2), (key2910, -1), (key2880, -1), (key2593, 1), (key2587, 1), (key2587, -2), (key2968, 1), (key2966, 1), (key2968, -2), (key2843, -2), (key2966, 1), (key2843, 1), (key2989, -2), (key2989, 1), (key2880, 1), (key2394, -1), (key2378, -1), (key2390, 1), (key2378, 1), (key2443, 1), (key2406, 1), (key2437, -1), (key2406, -1), (key2524, -1), (key2503, -1), (key2524, 1), (key2480, 1), (key2580, 1), (key2576, 1), (key2580, -1), (key2571, -1)]

theorem rawRowCheck5516 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form0 = rawRow5516 := by decide +kernel

def row5516 : Integer.Sparse Key := [(key2390, 1), (key2394, -1), (key2437, -1), (key2443, 1), (key2480, 1), (key2503, -1), (key2571, -1), (key2576, 1), (key2587, -1), (key2593, 1), (key2766, 1), (key2772, -1), (key2887, -2), (key2889, 1), (key2910, 1), (key2966, 2), (key2968, -1), (key2989, -1)]

theorem rowCheck5516 : row5516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5516 := by decide +kernel

theorem rowEval5516 (x : Key → ℝ) : Integer.Sparse.eval row5516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5516, Integer.Sparse.eval_collectBalanced, rawRowCheck5516]

def rawRow5517 : Integer.Sparse Key := [(key2843, -1), (key2843, -1), (key2880, 2), (key2766, -1), (key2766, -1), (key2887, 2), (key2887, 2), (key2910, -1), (key2910, -1), (key2772, 2), (key2889, -1), (key2889, -1), (key2843, 1), (key2843, 1), (key2880, -2), (key2587, 1), (key2587, 1), (key2966, -2), (key2966, -2), (key2989, 1), (key2989, 1), (key2593, -2), (key2968, 1), (key2968, 1), (key2887, -1), (key2887, -1), (key2910, 1), (key2910, 1), (key2966, 1), (key2966, 1), (key2989, -1), (key2989, -1), (key2390, -1), (key2390, -1), (key2437, 1), (key2437, 1), (key2394, 1), (key2394, 1), (key2443, -1), (key2443, -1)]

theorem rawRowCheck5517 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form0 = rawRow5517 := by decide +kernel

def row5517 : Integer.Sparse Key := [(key2390, -2), (key2394, 2), (key2437, 2), (key2443, -2), (key2587, 2), (key2593, -2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2966, -2), (key2968, 2)]

theorem rowCheck5517 : row5517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5517 := by decide +kernel

theorem rowEval5517 (x : Key → ℝ) : Integer.Sparse.eval row5517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5517, Integer.Sparse.eval_collectBalanced, rawRowCheck5517]

def rawRow5518 : Integer.Sparse Key := [(key2843, -1), (key2880, -1), (key2843, 2), (key2887, -1), (key2910, -1), (key2766, 2), (key2910, 2), (key2766, -1), (key2887, -1), (key2889, 2), (key2772, -1), (key2889, -1), (key2843, 1), (key2880, 1), (key2843, -2), (key2966, 1), (key2989, 1), (key2587, -2), (key2989, -2), (key2587, 1), (key2966, 1), (key2968, -2), (key2593, 1), (key2968, 1), (key2766, -1), (key2910, -1), (key2766, 1), (key2887, 1), (key2587, 1), (key2989, 1), (key2587, -1), (key2966, -1), (key2929, -1), (key3002, -1), (key2598, 1), (key3002, 1), (key2443, 1), (key2524, 1), (key2394, -1), (key2524, -1)]

theorem rawRowCheck5518 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form0 = rawRow5518 := by decide +kernel

def row5518 : Integer.Sparse Key := [(key2394, -1), (key2443, 1), (key2587, -1), (key2593, 1), (key2598, 1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2966, 1), (key2968, -1)]

theorem rowCheck5518 : row5518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5518 := by decide +kernel

theorem rowEval5518 (x : Key → ℝ) : Integer.Sparse.eval row5518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5518, Integer.Sparse.eval_collectBalanced, rawRowCheck5518]

def rawRow5519 : Integer.Sparse Key := [(key2880, -1), (key2843, -1), (key2843, 2), (key2910, -1), (key2887, -1), (key2910, 2), (key2766, 2), (key2887, -1), (key2766, -1), (key2889, 2), (key2889, -1), (key2772, -1), (key2880, 1), (key2843, 1), (key2843, -2), (key2989, 1), (key2966, 1), (key2989, -2), (key2587, -2), (key2966, 1), (key2587, 1), (key2968, -2), (key2968, 1), (key2593, 1), (key2910, -1), (key2766, -1), (key2887, 1), (key2766, 1), (key2989, 1), (key2587, 1), (key2966, -1), (key2587, -1), (key3002, -1), (key2929, -1), (key3002, 1), (key2598, 1), (key2524, 1), (key2443, 1), (key2524, -1), (key2394, -1)]

theorem rawRowCheck5519 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form0 = rawRow5519 := by decide +kernel

def row5519 : Integer.Sparse Key := [(key2394, -1), (key2443, 1), (key2587, -1), (key2593, 1), (key2598, 1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2966, 1), (key2968, -1)]

theorem rowCheck5519 : row5519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5519 := by decide +kernel

theorem rowEval5519 (x : Key → ℝ) : Integer.Sparse.eval row5519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5519, Integer.Sparse.eval_collectBalanced, rawRowCheck5519]

def rawRow5520 : Integer.Sparse Key := [(key2887, -1), (key2889, -1), (key2910, 2), (key2766, -1), (key2772, -1), (key2843, 2), (key2889, 2), (key2880, -1), (key2910, -1), (key2766, 2), (key2843, -1), (key2887, -1), (key2966, 1), (key2968, 1), (key2989, -2), (key2587, 1), (key2593, 1), (key2843, -2), (key2968, -2), (key2880, 1), (key2989, 1), (key2587, -2), (key2843, 1), (key2966, 1), (key2966, -1), (key2995, -1), (key2989, 1), (key3002, 1), (key2887, 1), (key2995, 1), (key2910, -1), (key3002, -1), (key2587, -1), (key2600, -1), (key2766, 1), (key2931, 1), (key2378, 1), (key2390, 1), (key2406, -1), (key2437, -1)]

theorem rawRowCheck5520 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form0 = rawRow5520 := by decide +kernel

def row5520 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, -1), (key2437, -1), (key2587, -2), (key2593, 1), (key2600, -1), (key2766, 2), (key2772, -1), (key2887, -1), (key2889, 1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5520 : row5520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5520 := by decide +kernel

theorem rowEval5520 (x : Key → ℝ) : Integer.Sparse.eval row5520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5520, Integer.Sparse.eval_collectBalanced, rawRowCheck5520]

def rawRow5521 : Integer.Sparse Key := [(key2889, -1), (key2887, -1), (key2910, 2), (key2772, -1), (key2766, -1), (key2889, 2), (key2843, 2), (key2910, -1), (key2880, -1), (key2766, 2), (key2887, -1), (key2843, -1), (key2968, 1), (key2966, 1), (key2989, -2), (key2593, 1), (key2587, 1), (key2968, -2), (key2843, -2), (key2989, 1), (key2880, 1), (key2587, -2), (key2966, 1), (key2843, 1), (key2995, -1), (key2966, -1), (key3002, 1), (key2989, 1), (key2995, 1), (key2887, 1), (key3002, -1), (key2910, -1), (key2600, -1), (key2587, -1), (key2931, 1), (key2766, 1), (key2390, 1), (key2378, 1), (key2437, -1), (key2406, -1)]

theorem rawRowCheck5521 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form0 = rawRow5521 := by decide +kernel

def row5521 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, -1), (key2437, -1), (key2587, -2), (key2593, 1), (key2600, -1), (key2766, 2), (key2772, -1), (key2887, -1), (key2889, 1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5521 : row5521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5521 := by decide +kernel

theorem rowEval5521 (x : Key → ℝ) : Integer.Sparse.eval row5521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5521, Integer.Sparse.eval_collectBalanced, rawRowCheck5521]

def rawRow5522 : Integer.Sparse Key := [(key2887, -1), (key2910, -1), (key2889, 2), (key2843, -1), (key2880, -1), (key2766, 2), (key2910, 2), (key2772, -1), (key2889, -1), (key2843, 2), (key2766, -1), (key2887, -1), (key2966, 1), (key2989, 1), (key2968, -2), (key2843, 1), (key2880, 1), (key2587, -2), (key2989, -2), (key2593, 1), (key2968, 1), (key2843, -2), (key2587, 1), (key2966, 1), (key2929, -1), (key3002, -1), (key2931, 1), (key2995, 1), (key2598, 1), (key3002, 1), (key2600, -1), (key2995, -1), (key2766, -1), (key2910, -1), (key2587, 1), (key2989, 1), (key2406, 1), (key2480, 1), (key2378, -1), (key2503, -1)]

theorem rawRowCheck5522 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form0 = rawRow5522 := by decide +kernel

def row5522 : Integer.Sparse Key := [(key2378, -1), (key2406, 1), (key2480, 1), (key2503, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2772, -1), (key2887, -2), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 2), (key2968, -1)]

theorem rowCheck5522 : row5522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5522 := by decide +kernel

theorem rowEval5522 (x : Key → ℝ) : Integer.Sparse.eval row5522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5522, Integer.Sparse.eval_collectBalanced, rawRowCheck5522]

def rawRow5523 : Integer.Sparse Key := [(key2910, -1), (key2887, -1), (key2889, 2), (key2880, -1), (key2843, -1), (key2910, 2), (key2766, 2), (key2889, -1), (key2772, -1), (key2843, 2), (key2887, -1), (key2766, -1), (key2989, 1), (key2966, 1), (key2968, -2), (key2880, 1), (key2843, 1), (key2989, -2), (key2587, -2), (key2968, 1), (key2593, 1), (key2843, -2), (key2966, 1), (key2587, 1), (key3002, -1), (key2929, -1), (key2995, 1), (key2931, 1), (key3002, 1), (key2598, 1), (key2995, -1), (key2600, -1), (key2910, -1), (key2766, -1), (key2989, 1), (key2587, 1), (key2480, 1), (key2406, 1), (key2503, -1), (key2378, -1)]

theorem rawRowCheck5523 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form0 = rawRow5523 := by decide +kernel

def row5523 : Integer.Sparse Key := [(key2378, -1), (key2406, 1), (key2480, 1), (key2503, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2772, -1), (key2887, -2), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 2), (key2968, -1)]

theorem rowCheck5523 : row5523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5523 := by decide +kernel

theorem rowEval5523 (x : Key → ℝ) : Integer.Sparse.eval row5523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5523, Integer.Sparse.eval_collectBalanced, rawRowCheck5523]

def rawRow5524 : Integer.Sparse Key := [(key2889, -1), (key2910, -1), (key2887, 2), (key2889, -1), (key2910, -1), (key2772, 2), (key2880, 2), (key2766, -1), (key2843, -1), (key2887, 2), (key2766, -1), (key2843, -1), (key2968, 1), (key2989, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2593, -2), (key2880, -2), (key2587, 1), (key2843, 1), (key2966, -2), (key2587, 1), (key2843, 1), (key2931, -1), (key2989, -1), (key2929, 1), (key2966, 1), (key2600, 1), (key2910, 1), (key2598, -1), (key2887, -1), (key2931, -1), (key2989, -1), (key2600, 1), (key2910, 1), (key2437, 1), (key2503, 1), (key2390, -1), (key2480, -1)]

theorem rawRowCheck5524 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form0 = rawRow5524 := by decide +kernel

def row5524 : Integer.Sparse Key := [(key2390, -1), (key2437, 1), (key2480, -1), (key2503, 1), (key2587, 2), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 3), (key2889, -2), (key2929, 1), (key2931, -2), (key2966, -3), (key2968, 2)]

theorem rowCheck5524 : row5524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5524 := by decide +kernel

theorem rowEval5524 (x : Key → ℝ) : Integer.Sparse.eval row5524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5524, Integer.Sparse.eval_collectBalanced, rawRowCheck5524]

def rawRow5525 : Integer.Sparse Key := [(key2910, -1), (key2889, -1), (key2887, 2), (key2910, -1), (key2889, -1), (key2880, 2), (key2772, 2), (key2843, -1), (key2766, -1), (key2887, 2), (key2843, -1), (key2766, -1), (key2989, 1), (key2968, 1), (key2966, -2), (key2989, 1), (key2968, 1), (key2880, -2), (key2593, -2), (key2843, 1), (key2587, 1), (key2966, -2), (key2843, 1), (key2587, 1), (key2989, -1), (key2931, -1), (key2966, 1), (key2929, 1), (key2910, 1), (key2600, 1), (key2887, -1), (key2598, -1), (key2989, -1), (key2931, -1), (key2910, 1), (key2600, 1), (key2503, 1), (key2437, 1), (key2480, -1), (key2390, -1)]

theorem rawRowCheck5525 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form0 = rawRow5525 := by decide +kernel

def row5525 : Integer.Sparse Key := [(key2390, -1), (key2437, 1), (key2480, -1), (key2503, 1), (key2587, 2), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 3), (key2889, -2), (key2929, 1), (key2931, -2), (key2966, -3), (key2968, 2)]

theorem rowCheck5525 : row5525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5525 := by decide +kernel

theorem rowEval5525 (x : Key → ℝ) : Integer.Sparse.eval row5525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5525, Integer.Sparse.eval_collectBalanced, rawRowCheck5525]

def rawRow5526 : Integer.Sparse Key := [(key2929, -1), (key2931, -1), (key2931, 2), (key2966, -1), (key2968, -1), (key2966, 2), (key2995, 2), (key2968, -1), (key2995, -1), (key2989, 2), (key2989, -1), (key3002, -1), (key2598, 1), (key2600, 1), (key2600, -2), (key2887, 1), (key2889, 1), (key2887, -2), (key2995, -2), (key2889, 1), (key2995, 1), (key2910, -2), (key2910, 1), (key3002, 1), (key2587, -1), (key2600, -1), (key2593, 1), (key2600, 1), (key2766, 1), (key2931, 1), (key2772, -1), (key2931, -1), (key2843, -1), (key2889, -1), (key2843, 1), (key2968, 1), (key2880, 1), (key2910, 1), (key2880, -1), (key2989, -1)]

theorem rawRowCheck5526 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form0 = rawRow5526 := by decide +kernel

def row5526 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5526 : row5526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5526 := by decide +kernel

theorem rowEval5526 (x : Key → ℝ) : Integer.Sparse.eval row5526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5526, Integer.Sparse.eval_collectBalanced, rawRowCheck5526]

def rawRow5527 : Integer.Sparse Key := [(key2931, -1), (key2929, -1), (key2931, 2), (key2968, -1), (key2966, -1), (key2995, 2), (key2966, 2), (key2995, -1), (key2968, -1), (key2989, 2), (key3002, -1), (key2989, -1), (key2600, 1), (key2598, 1), (key2600, -2), (key2889, 1), (key2887, 1), (key2995, -2), (key2887, -2), (key2995, 1), (key2889, 1), (key2910, -2), (key3002, 1), (key2910, 1), (key2600, -1), (key2587, -1), (key2600, 1), (key2593, 1), (key2931, 1), (key2766, 1), (key2931, -1), (key2772, -1), (key2889, -1), (key2843, -1), (key2968, 1), (key2843, 1), (key2910, 1), (key2880, 1), (key2989, -1), (key2880, -1)]

theorem rawRowCheck5527 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form0 = rawRow5527 := by decide +kernel

def row5527 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5527 : row5527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5527 := by decide +kernel

theorem rowEval5527 (x : Key → ℝ) : Integer.Sparse.eval row5527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5527, Integer.Sparse.eval_collectBalanced, rawRowCheck5527]

def rawRow5528 : Integer.Sparse Key := [(key2931, -1), (key2931, -1), (key2929, 2), (key2995, -1), (key2995, -1), (key2968, 2), (key2968, 2), (key2966, -1), (key2966, -1), (key3002, 2), (key2989, -1), (key2989, -1), (key2600, 1), (key2600, 1), (key2598, -2), (key2995, 1), (key2995, 1), (key2889, -2), (key2889, -2), (key2887, 1), (key2887, 1), (key3002, -2), (key2910, 1), (key2910, 1), (key2593, -1), (key2593, -1), (key2587, 1), (key2587, 1), (key2772, 1), (key2772, 1), (key2766, -1), (key2766, -1), (key2968, -1), (key2968, -1), (key2889, 1), (key2889, 1), (key2989, 1), (key2989, 1), (key2910, -1), (key2910, -1)]

theorem rawRowCheck5528 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form0 = rawRow5528 := by decide +kernel

def row5528 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

theorem rowCheck5528 : row5528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5528 := by decide +kernel

theorem rowEval5528 (x : Key → ℝ) : Integer.Sparse.eval row5528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5528, Integer.Sparse.eval_collectBalanced, rawRowCheck5528]

def rawRow5529 : Integer.Sparse Key := [(key2966, -1), (key2968, -1), (key2989, 2), (key2929, -1), (key2931, -1), (key2966, 2), (key2995, 2), (key2989, -1), (key3002, -1), (key2931, 2), (key2968, -1), (key2995, -1), (key2887, 1), (key2889, 1), (key2910, -2), (key2598, 1), (key2600, 1), (key2887, -2), (key2995, -2), (key2910, 1), (key3002, 1), (key2600, -2), (key2889, 1), (key2995, 1), (key2843, -1), (key2889, -1), (key2880, 1), (key2910, 1), (key2843, 1), (key2968, 1), (key2880, -1), (key2989, -1), (key2587, -1), (key2600, -1), (key2766, 1), (key2931, 1), (key2593, 1), (key2600, 1), (key2772, -1), (key2931, -1)]

theorem rawRowCheck5529 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form0 = rawRow5529 := by decide +kernel

def row5529 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5529 : row5529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5529 := by decide +kernel

theorem rowEval5529 (x : Key → ℝ) : Integer.Sparse.eval row5529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5529, Integer.Sparse.eval_collectBalanced, rawRowCheck5529]

def rawRow5530 : Integer.Sparse Key := [(key2968, -1), (key2966, -1), (key2989, 2), (key2931, -1), (key2929, -1), (key2995, 2), (key2966, 2), (key3002, -1), (key2989, -1), (key2931, 2), (key2995, -1), (key2968, -1), (key2889, 1), (key2887, 1), (key2910, -2), (key2600, 1), (key2598, 1), (key2995, -2), (key2887, -2), (key3002, 1), (key2910, 1), (key2600, -2), (key2995, 1), (key2889, 1), (key2889, -1), (key2843, -1), (key2910, 1), (key2880, 1), (key2968, 1), (key2843, 1), (key2989, -1), (key2880, -1), (key2600, -1), (key2587, -1), (key2931, 1), (key2766, 1), (key2600, 1), (key2593, 1), (key2931, -1), (key2772, -1)]

theorem rawRowCheck5530 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form0 = rawRow5530 := by decide +kernel

def row5530 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5530 : row5530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5530 := by decide +kernel

theorem rowEval5530 (x : Key → ℝ) : Integer.Sparse.eval row5530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5530, Integer.Sparse.eval_collectBalanced, rawRowCheck5530]

def rawRow5531 : Integer.Sparse Key := [(key2966, -1), (key2989, -1), (key2968, 2), (key2966, -1), (key2989, -1), (key2929, 2), (key3002, 2), (key2931, -1), (key2995, -1), (key2968, 2), (key2931, -1), (key2995, -1), (key2887, 1), (key2910, 1), (key2889, -2), (key2887, 1), (key2910, 1), (key2598, -2), (key3002, -2), (key2600, 1), (key2995, 1), (key2889, -2), (key2600, 1), (key2995, 1), (key2766, -1), (key2910, -1), (key2772, 1), (key2889, 1), (key2587, 1), (key2989, 1), (key2593, -1), (key2968, -1), (key2766, -1), (key2910, -1), (key2587, 1), (key2989, 1), (key2772, 1), (key2889, 1), (key2593, -1), (key2968, -1)]

theorem rawRowCheck5531 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form0 = rawRow5531 := by decide +kernel

def row5531 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

theorem rowCheck5531 : row5531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5531 := by decide +kernel

theorem rowEval5531 (x : Key → ℝ) : Integer.Sparse.eval row5531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5531, Integer.Sparse.eval_collectBalanced, rawRowCheck5531]

def rawRow5532 : Integer.Sparse Key := [(key2989, -1), (key2966, -1), (key2968, 2), (key2989, -1), (key2966, -1), (key3002, 2), (key2929, 2), (key2995, -1), (key2931, -1), (key2968, 2), (key2995, -1), (key2931, -1), (key2910, 1), (key2887, 1), (key2889, -2), (key2910, 1), (key2887, 1), (key3002, -2), (key2598, -2), (key2995, 1), (key2600, 1), (key2889, -2), (key2995, 1), (key2600, 1), (key2910, -1), (key2766, -1), (key2889, 1), (key2772, 1), (key2989, 1), (key2587, 1), (key2968, -1), (key2593, -1), (key2910, -1), (key2766, -1), (key2989, 1), (key2587, 1), (key2889, 1), (key2772, 1), (key2968, -1), (key2593, -1)]

theorem rawRowCheck5532 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form0 = rawRow5532 := by decide +kernel

def row5532 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

theorem rowCheck5532 : row5532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5532 := by decide +kernel

theorem rowEval5532 (x : Key → ℝ) : Integer.Sparse.eval row5532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5532, Integer.Sparse.eval_collectBalanced, rawRowCheck5532]

def rawRow5533 : Integer.Sparse Key := [(key2968, -1), (key2989, -1), (key2966, 2), (key2995, -1), (key3002, -1), (key2931, 2), (key2989, 2), (key2929, -1), (key2966, -1), (key2995, 2), (key2931, -1), (key2968, -1), (key2889, 1), (key2910, 1), (key2887, -2), (key2995, 1), (key3002, 1), (key2600, -2), (key2910, -2), (key2598, 1), (key2887, 1), (key2995, -2), (key2600, 1), (key2889, 1), (key2772, -1), (key2880, -1), (key2766, 1), (key2843, 1), (key2593, 1), (key2880, 1), (key2587, -1), (key2843, -1), (key2931, -1), (key2989, -1), (key2600, 1), (key2910, 1), (key2931, 1), (key2968, 1), (key2600, -1), (key2889, -1)]

theorem rawRowCheck5533 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form0 = rawRow5533 := by decide +kernel

def row5533 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5533 : row5533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5533 := by decide +kernel

theorem rowEval5533 (x : Key → ℝ) : Integer.Sparse.eval row5533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5533, Integer.Sparse.eval_collectBalanced, rawRowCheck5533]

def rawRow5534 : Integer.Sparse Key := [(key2989, -1), (key2968, -1), (key2966, 2), (key3002, -1), (key2995, -1), (key2989, 2), (key2931, 2), (key2966, -1), (key2929, -1), (key2995, 2), (key2968, -1), (key2931, -1), (key2910, 1), (key2889, 1), (key2887, -2), (key3002, 1), (key2995, 1), (key2910, -2), (key2600, -2), (key2887, 1), (key2598, 1), (key2995, -2), (key2889, 1), (key2600, 1), (key2880, -1), (key2772, -1), (key2843, 1), (key2766, 1), (key2880, 1), (key2593, 1), (key2843, -1), (key2587, -1), (key2989, -1), (key2931, -1), (key2910, 1), (key2600, 1), (key2968, 1), (key2931, 1), (key2889, -1), (key2600, -1)]

theorem rawRowCheck5534 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form0 = rawRow5534 := by decide +kernel

def row5534 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5534 : row5534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5534 := by decide +kernel

theorem rowEval5534 (x : Key → ℝ) : Integer.Sparse.eval row5534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5534, Integer.Sparse.eval_collectBalanced, rawRowCheck5534]

def rawRow5535 : Integer.Sparse Key := [(key2995, -1), (key2995, -1), (key3002, 2), (key2931, -1), (key2931, -1), (key2968, 2), (key2968, 2), (key2989, -1), (key2989, -1), (key2929, 2), (key2966, -1), (key2966, -1), (key2995, 1), (key2995, 1), (key3002, -2), (key2600, 1), (key2600, 1), (key2889, -2), (key2889, -2), (key2910, 1), (key2910, 1), (key2598, -2), (key2887, 1), (key2887, 1), (key2968, -1), (key2968, -1), (key2989, 1), (key2989, 1), (key2889, 1), (key2889, 1), (key2910, -1), (key2910, -1), (key2593, -1), (key2593, -1), (key2772, 1), (key2772, 1), (key2587, 1), (key2587, 1), (key2766, -1), (key2766, -1)]

theorem rawRowCheck5535 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form0 = rawRow5535 := by decide +kernel

def row5535 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

theorem rowCheck5535 : row5535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5535 := by decide +kernel

theorem rowEval5535 (x : Key → ℝ) : Integer.Sparse.eval row5535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5535, Integer.Sparse.eval_collectBalanced, rawRowCheck5535]

def rawRow5536 : Integer.Sparse Key := [(key2995, -1), (key3002, -1), (key2995, 2), (key2968, -1), (key2989, -1), (key2931, 2), (key2989, 2), (key2931, -1), (key2968, -1), (key2966, 2), (key2929, -1), (key2966, -1), (key2995, 1), (key3002, 1), (key2995, -2), (key2889, 1), (key2910, 1), (key2600, -2), (key2910, -2), (key2600, 1), (key2889, 1), (key2887, -2), (key2598, 1), (key2887, 1), (key2931, -1), (key2989, -1), (key2931, 1), (key2968, 1), (key2600, 1), (key2910, 1), (key2600, -1), (key2889, -1), (key2772, -1), (key2880, -1), (key2593, 1), (key2880, 1), (key2766, 1), (key2843, 1), (key2587, -1), (key2843, -1)]

theorem rawRowCheck5536 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form0 = rawRow5536 := by decide +kernel

def row5536 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5536 : row5536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5536 := by decide +kernel

theorem rowEval5536 (x : Key → ℝ) : Integer.Sparse.eval row5536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5536, Integer.Sparse.eval_collectBalanced, rawRowCheck5536]

def rawRow5537 : Integer.Sparse Key := [(key3002, -1), (key2995, -1), (key2995, 2), (key2989, -1), (key2968, -1), (key2989, 2), (key2931, 2), (key2968, -1), (key2931, -1), (key2966, 2), (key2966, -1), (key2929, -1), (key3002, 1), (key2995, 1), (key2995, -2), (key2910, 1), (key2889, 1), (key2910, -2), (key2600, -2), (key2889, 1), (key2600, 1), (key2887, -2), (key2887, 1), (key2598, 1), (key2989, -1), (key2931, -1), (key2968, 1), (key2931, 1), (key2910, 1), (key2600, 1), (key2889, -1), (key2600, -1), (key2880, -1), (key2772, -1), (key2880, 1), (key2593, 1), (key2843, 1), (key2766, 1), (key2843, -1), (key2587, -1)]

theorem rawRowCheck5537 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form0 = rawRow5537 := by decide +kernel

def row5537 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

theorem rowCheck5537 : row5537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5537 := by decide +kernel

theorem rowEval5537 (x : Key → ℝ) : Integer.Sparse.eval row5537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5537, Integer.Sparse.eval_collectBalanced, rawRowCheck5537]

def rawRow5538 : Integer.Sparse Key := [(key1256, -1), (key1256, -1), (key1261, 2), (key1256, -1), (key1256, -1), (key1265, 2), (key1265, 2), (key1268, -1), (key1268, -1), (key1261, 2), (key1268, -1), (key1268, -1), (key1531, 1), (key1531, 1), (key1536, -2), (key1531, 1), (key1531, 1), (key1765, -2), (key1765, -2), (key1768, 1), (key1768, 1), (key1536, -2), (key1768, 1), (key1768, 1), (key1648, -1), (key1648, -1), (key1651, 1), (key1651, 1), (key1806, 1), (key1806, 1), (key1809, -1), (key1809, -1), (key1648, -1), (key1648, -1), (key1806, 1), (key1806, 1), (key1651, 1), (key1651, 1), (key1809, -1), (key1809, -1)]

theorem rawRowCheck5538 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5538 := by decide +kernel

def row5538 : Integer.Sparse Key := [(key1256, -4), (key1261, 4), (key1265, 4), (key1268, -4), (key1531, 4), (key1536, -4), (key1648, -4), (key1651, 4), (key1765, -4), (key1768, 4), (key1806, 4), (key1809, -4)]

theorem rowCheck5538 : row5538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5538 := by decide +kernel

theorem rowEval5538 (x : Key → ℝ) : Integer.Sparse.eval row5538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5538, Integer.Sparse.eval_collectBalanced, rawRowCheck5538]

def rawRow5539 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1256, 2), (key1265, -1), (key1268, -1), (key1256, 2), (key1268, 2), (key1256, -1), (key1265, -1), (key1268, 2), (key1261, -1), (key1268, -1), (key1531, 1), (key1536, 1), (key1531, -2), (key1765, 1), (key1768, 1), (key1531, -2), (key1768, -2), (key1531, 1), (key1765, 1), (key1768, -2), (key1536, 1), (key1768, 1), (key1609, -1), (key1651, -1), (key1609, 1), (key1648, 1), (key1609, 1), (key1809, 1), (key1609, -1), (key1806, -1), (key1806, -1), (key1837, -1), (key1648, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1651, -1), (key1837, -1)]

theorem rawRowCheck5539 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5539 := by decide +kernel

def row5539 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5539 : row5539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5539 := by decide +kernel

theorem rowEval5539 (x : Key → ℝ) : Integer.Sparse.eval row5539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5539, Integer.Sparse.eval_collectBalanced, rawRowCheck5539]

def rawRow5540 : Integer.Sparse Key := [(key1261, -1), (key1256, -1), (key1256, 2), (key1268, -1), (key1265, -1), (key1268, 2), (key1256, 2), (key1265, -1), (key1256, -1), (key1268, 2), (key1268, -1), (key1261, -1), (key1536, 1), (key1531, 1), (key1531, -2), (key1768, 1), (key1765, 1), (key1768, -2), (key1531, -2), (key1765, 1), (key1531, 1), (key1768, -2), (key1768, 1), (key1536, 1), (key1651, -1), (key1609, -1), (key1648, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, -1), (key1609, -1), (key1837, -1), (key1806, -1), (key1837, 1), (key1648, 1), (key1837, 1), (key1809, 1), (key1837, -1), (key1651, -1)]

theorem rawRowCheck5540 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5540 := by decide +kernel

def row5540 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5540 : row5540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5540 := by decide +kernel

theorem rowEval5540 (x : Key → ℝ) : Integer.Sparse.eval row5540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5540, Integer.Sparse.eval_collectBalanced, rawRowCheck5540]

def rawRow5541 : Integer.Sparse Key := [(key1265, -1), (key1268, -1), (key1268, 2), (key1256, -1), (key1261, -1), (key1256, 2), (key1268, 2), (key1261, -1), (key1268, -1), (key1256, 2), (key1256, -1), (key1265, -1), (key1765, 1), (key1768, 1), (key1768, -2), (key1531, 1), (key1536, 1), (key1531, -2), (key1768, -2), (key1536, 1), (key1768, 1), (key1531, -2), (key1531, 1), (key1765, 1), (key1806, -1), (key1837, -1), (key1809, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, -1), (key1837, -1), (key1609, -1), (key1651, -1), (key1609, 1), (key1809, 1), (key1609, 1), (key1648, 1), (key1609, -1), (key1806, -1)]

theorem rawRowCheck5541 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5541 := by decide +kernel

def row5541 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5541 : row5541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5541 := by decide +kernel

theorem rowEval5541 (x : Key → ℝ) : Integer.Sparse.eval row5541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5541, Integer.Sparse.eval_collectBalanced, rawRowCheck5541]

def rawRow5542 : Integer.Sparse Key := [(key1268, -1), (key1265, -1), (key1268, 2), (key1261, -1), (key1256, -1), (key1268, 2), (key1256, 2), (key1268, -1), (key1261, -1), (key1256, 2), (key1265, -1), (key1256, -1), (key1768, 1), (key1765, 1), (key1768, -2), (key1536, 1), (key1531, 1), (key1768, -2), (key1531, -2), (key1768, 1), (key1536, 1), (key1531, -2), (key1765, 1), (key1531, 1), (key1837, -1), (key1806, -1), (key1837, 1), (key1809, 1), (key1837, 1), (key1648, 1), (key1837, -1), (key1651, -1), (key1651, -1), (key1609, -1), (key1809, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1806, -1), (key1609, -1)]

theorem rawRowCheck5542 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5542 := by decide +kernel

def row5542 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5542 : row5542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5542 := by decide +kernel

theorem rowEval5542 (x : Key → ℝ) : Integer.Sparse.eval row5542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5542, Integer.Sparse.eval_collectBalanced, rawRowCheck5542]

def rawRow5543 : Integer.Sparse Key := [(key1268, -1), (key1268, -1), (key1265, 2), (key1268, -1), (key1268, -1), (key1261, 2), (key1261, 2), (key1256, -1), (key1256, -1), (key1265, 2), (key1256, -1), (key1256, -1), (key1768, 1), (key1768, 1), (key1765, -2), (key1768, 1), (key1768, 1), (key1536, -2), (key1536, -2), (key1531, 1), (key1531, 1), (key1765, -2), (key1531, 1), (key1531, 1), (key1809, -1), (key1809, -1), (key1806, 1), (key1806, 1), (key1651, 1), (key1651, 1), (key1648, -1), (key1648, -1), (key1809, -1), (key1809, -1), (key1651, 1), (key1651, 1), (key1806, 1), (key1806, 1), (key1648, -1), (key1648, -1)]

theorem rawRowCheck5543 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5543 := by decide +kernel

def row5543 : Integer.Sparse Key := [(key1256, -4), (key1261, 4), (key1265, 4), (key1268, -4), (key1531, 4), (key1536, -4), (key1648, -4), (key1651, 4), (key1765, -4), (key1768, 4), (key1806, 4), (key1809, -4)]

theorem rowCheck5543 : row5543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5543 := by decide +kernel

theorem rowEval5543 (x : Key → ℝ) : Integer.Sparse.eval row5543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5543, Integer.Sparse.eval_collectBalanced, rawRowCheck5543]

def rawRow5544 : Integer.Sparse Key := [(key1531, -1), (key1531, -1), (key1536, 2), (key1609, -1), (key1609, -1), (key1648, 2), (key1648, 2), (key1651, -1), (key1651, -1), (key1642, 2), (key1674, -1), (key1674, -1), (key1256, 1), (key1256, 1), (key1261, -2), (key1609, 1), (key1609, 1), (key1806, -2), (key1806, -2), (key1809, 1), (key1809, 1), (key1642, -2), (key1832, 1), (key1832, 1), (key1265, -1), (key1265, -1), (key1268, 1), (key1268, 1), (key1765, 1), (key1765, 1), (key1768, -1), (key1768, -1), (key1648, -1), (key1648, -1), (key1806, 1), (key1806, 1), (key1674, 1), (key1674, 1), (key1832, -1), (key1832, -1)]

theorem rawRowCheck5544 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5544 := by decide +kernel

def row5544 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5544 : row5544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5544 := by decide +kernel

theorem rowEval5544 (x : Key → ℝ) : Integer.Sparse.eval row5544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5544, Integer.Sparse.eval_collectBalanced, rawRowCheck5544]

def rawRow5545 : Integer.Sparse Key := [(key1531, -1), (key1536, -1), (key1531, 2), (key1648, -1), (key1651, -1), (key1609, 2), (key1651, 2), (key1609, -1), (key1648, -1), (key1674, 2), (key1642, -1), (key1674, -1), (key1256, 1), (key1261, 1), (key1256, -2), (key1806, 1), (key1809, 1), (key1609, -2), (key1809, -2), (key1609, 1), (key1806, 1), (key1832, -2), (key1642, 1), (key1832, 1), (key1256, -1), (key1268, -1), (key1256, 1), (key1265, 1), (key1531, 1), (key1768, 1), (key1531, -1), (key1765, -1), (key1806, -1), (key1837, -1), (key1648, 1), (key1837, 1), (key1832, 1), (key1848, 1), (key1674, -1), (key1848, -1)]

theorem rawRowCheck5545 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5545 := by decide +kernel

def row5545 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5545 : row5545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5545 := by decide +kernel

theorem rowEval5545 (x : Key → ℝ) : Integer.Sparse.eval row5545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5545, Integer.Sparse.eval_collectBalanced, rawRowCheck5545]

def rawRow5546 : Integer.Sparse Key := [(key1536, -1), (key1531, -1), (key1531, 2), (key1651, -1), (key1648, -1), (key1651, 2), (key1609, 2), (key1648, -1), (key1609, -1), (key1674, 2), (key1674, -1), (key1642, -1), (key1261, 1), (key1256, 1), (key1256, -2), (key1809, 1), (key1806, 1), (key1809, -2), (key1609, -2), (key1806, 1), (key1609, 1), (key1832, -2), (key1832, 1), (key1642, 1), (key1268, -1), (key1256, -1), (key1265, 1), (key1256, 1), (key1768, 1), (key1531, 1), (key1765, -1), (key1531, -1), (key1837, -1), (key1806, -1), (key1837, 1), (key1648, 1), (key1848, 1), (key1832, 1), (key1848, -1), (key1674, -1)]

theorem rawRowCheck5546 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5546 := by decide +kernel

def row5546 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5546 : row5546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5546 := by decide +kernel

theorem rowEval5546 (x : Key → ℝ) : Integer.Sparse.eval row5546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5546, Integer.Sparse.eval_collectBalanced, rawRowCheck5546]

def rawRow5547 : Integer.Sparse Key := [(key1609, -1), (key1609, -1), (key1642, 2), (key1531, -1), (key1531, -1), (key1648, 2), (key1648, 2), (key1674, -1), (key1674, -1), (key1536, 2), (key1651, -1), (key1651, -1), (key1609, 1), (key1609, 1), (key1642, -2), (key1256, 1), (key1256, 1), (key1806, -2), (key1806, -2), (key1832, 1), (key1832, 1), (key1261, -2), (key1809, 1), (key1809, 1), (key1648, -1), (key1648, -1), (key1674, 1), (key1674, 1), (key1806, 1), (key1806, 1), (key1832, -1), (key1832, -1), (key1265, -1), (key1265, -1), (key1765, 1), (key1765, 1), (key1268, 1), (key1268, 1), (key1768, -1), (key1768, -1)]

theorem rawRowCheck5547 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1 = rawRow5547 := by decide +kernel

def row5547 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5547 : row5547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5547 := by decide +kernel

theorem rowEval5547 (x : Key → ℝ) : Integer.Sparse.eval row5547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5547, Integer.Sparse.eval_collectBalanced, rawRowCheck5547]

def rawRow5548 : Integer.Sparse Key := [(key1609, -1), (key1642, -1), (key1609, 2), (key1648, -1), (key1674, -1), (key1531, 2), (key1674, 2), (key1531, -1), (key1648, -1), (key1651, 2), (key1536, -1), (key1651, -1), (key1609, 1), (key1642, 1), (key1609, -2), (key1806, 1), (key1832, 1), (key1256, -2), (key1832, -2), (key1256, 1), (key1806, 1), (key1809, -2), (key1261, 1), (key1809, 1), (key1531, -1), (key1674, -1), (key1531, 1), (key1648, 1), (key1256, 1), (key1832, 1), (key1256, -1), (key1806, -1), (key1765, -1), (key1848, -1), (key1265, 1), (key1848, 1), (key1768, 1), (key1837, 1), (key1268, -1), (key1837, -1)]

theorem rawRowCheck5548 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1 = rawRow5548 := by decide +kernel

def row5548 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5548 : row5548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5548 := by decide +kernel

theorem rowEval5548 (x : Key → ℝ) : Integer.Sparse.eval row5548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5548, Integer.Sparse.eval_collectBalanced, rawRowCheck5548]

def rawRow5549 : Integer.Sparse Key := [(key1642, -1), (key1609, -1), (key1609, 2), (key1674, -1), (key1648, -1), (key1674, 2), (key1531, 2), (key1648, -1), (key1531, -1), (key1651, 2), (key1651, -1), (key1536, -1), (key1642, 1), (key1609, 1), (key1609, -2), (key1832, 1), (key1806, 1), (key1832, -2), (key1256, -2), (key1806, 1), (key1256, 1), (key1809, -2), (key1809, 1), (key1261, 1), (key1674, -1), (key1531, -1), (key1648, 1), (key1531, 1), (key1832, 1), (key1256, 1), (key1806, -1), (key1256, -1), (key1848, -1), (key1765, -1), (key1848, 1), (key1265, 1), (key1837, 1), (key1768, 1), (key1837, -1), (key1268, -1)]

theorem rawRowCheck5549 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1 = rawRow5549 := by decide +kernel

def row5549 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5549 : row5549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5549 := by decide +kernel

theorem rowEval5549 (x : Key → ℝ) : Integer.Sparse.eval row5549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5549, Integer.Sparse.eval_collectBalanced, rawRowCheck5549]

def rawRow5550 : Integer.Sparse Key := [(key1648, -1), (key1651, -1), (key1674, 2), (key1531, -1), (key1536, -1), (key1609, 2), (key1651, 2), (key1642, -1), (key1674, -1), (key1531, 2), (key1609, -1), (key1648, -1), (key1806, 1), (key1809, 1), (key1832, -2), (key1256, 1), (key1261, 1), (key1609, -2), (key1809, -2), (key1642, 1), (key1832, 1), (key1256, -2), (key1609, 1), (key1806, 1), (key1806, -1), (key1837, -1), (key1832, 1), (key1848, 1), (key1648, 1), (key1837, 1), (key1674, -1), (key1848, -1), (key1256, -1), (key1268, -1), (key1531, 1), (key1768, 1), (key1256, 1), (key1265, 1), (key1531, -1), (key1765, -1)]

theorem rawRowCheck5550 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5550 := by decide +kernel

def row5550 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5550 : row5550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5550 := by decide +kernel

theorem rowEval5550 (x : Key → ℝ) : Integer.Sparse.eval row5550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5550, Integer.Sparse.eval_collectBalanced, rawRowCheck5550]

def rawRow5551 : Integer.Sparse Key := [(key1651, -1), (key1648, -1), (key1674, 2), (key1536, -1), (key1531, -1), (key1651, 2), (key1609, 2), (key1674, -1), (key1642, -1), (key1531, 2), (key1648, -1), (key1609, -1), (key1809, 1), (key1806, 1), (key1832, -2), (key1261, 1), (key1256, 1), (key1809, -2), (key1609, -2), (key1832, 1), (key1642, 1), (key1256, -2), (key1806, 1), (key1609, 1), (key1837, -1), (key1806, -1), (key1848, 1), (key1832, 1), (key1837, 1), (key1648, 1), (key1848, -1), (key1674, -1), (key1268, -1), (key1256, -1), (key1768, 1), (key1531, 1), (key1265, 1), (key1256, 1), (key1765, -1), (key1531, -1)]

theorem rawRowCheck5551 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5551 := by decide +kernel

def row5551 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5551 : row5551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5551 := by decide +kernel

theorem rowEval5551 (x : Key → ℝ) : Integer.Sparse.eval row5551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5551, Integer.Sparse.eval_collectBalanced, rawRowCheck5551]

def rawRow5552 : Integer.Sparse Key := [(key1648, -1), (key1674, -1), (key1651, 2), (key1609, -1), (key1642, -1), (key1531, 2), (key1674, 2), (key1536, -1), (key1651, -1), (key1609, 2), (key1531, -1), (key1648, -1), (key1806, 1), (key1832, 1), (key1809, -2), (key1609, 1), (key1642, 1), (key1256, -2), (key1832, -2), (key1261, 1), (key1809, 1), (key1609, -2), (key1256, 1), (key1806, 1), (key1765, -1), (key1848, -1), (key1768, 1), (key1837, 1), (key1265, 1), (key1848, 1), (key1268, -1), (key1837, -1), (key1531, -1), (key1674, -1), (key1256, 1), (key1832, 1), (key1531, 1), (key1648, 1), (key1256, -1), (key1806, -1)]

theorem rawRowCheck5552 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5552 := by decide +kernel

def row5552 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5552 : row5552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5552 := by decide +kernel

theorem rowEval5552 (x : Key → ℝ) : Integer.Sparse.eval row5552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5552, Integer.Sparse.eval_collectBalanced, rawRowCheck5552]

def rawRow5553 : Integer.Sparse Key := [(key1674, -1), (key1648, -1), (key1651, 2), (key1642, -1), (key1609, -1), (key1674, 2), (key1531, 2), (key1651, -1), (key1536, -1), (key1609, 2), (key1648, -1), (key1531, -1), (key1832, 1), (key1806, 1), (key1809, -2), (key1642, 1), (key1609, 1), (key1832, -2), (key1256, -2), (key1809, 1), (key1261, 1), (key1609, -2), (key1806, 1), (key1256, 1), (key1848, -1), (key1765, -1), (key1837, 1), (key1768, 1), (key1848, 1), (key1265, 1), (key1837, -1), (key1268, -1), (key1674, -1), (key1531, -1), (key1832, 1), (key1256, 1), (key1648, 1), (key1531, 1), (key1806, -1), (key1256, -1)]

theorem rawRowCheck5553 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5553 := by decide +kernel

def row5553 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5553 : row5553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5553 := by decide +kernel

theorem rowEval5553 (x : Key → ℝ) : Integer.Sparse.eval row5553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5553, Integer.Sparse.eval_collectBalanced, rawRowCheck5553]

def rawRow5554 : Integer.Sparse Key := [(key1651, -1), (key1674, -1), (key1648, 2), (key1651, -1), (key1674, -1), (key1536, 2), (key1642, 2), (key1531, -1), (key1609, -1), (key1648, 2), (key1531, -1), (key1609, -1), (key1809, 1), (key1832, 1), (key1806, -2), (key1809, 1), (key1832, 1), (key1261, -2), (key1642, -2), (key1256, 1), (key1609, 1), (key1806, -2), (key1256, 1), (key1609, 1), (key1768, -1), (key1832, -1), (key1765, 1), (key1806, 1), (key1268, 1), (key1674, 1), (key1265, -1), (key1648, -1), (key1768, -1), (key1832, -1), (key1268, 1), (key1674, 1), (key1765, 1), (key1806, 1), (key1265, -1), (key1648, -1)]

theorem rawRowCheck5554 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5554 := by decide +kernel

def row5554 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5554 : row5554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5554 := by decide +kernel

theorem rowEval5554 (x : Key → ℝ) : Integer.Sparse.eval row5554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5554, Integer.Sparse.eval_collectBalanced, rawRowCheck5554]

def rawRow5555 : Integer.Sparse Key := [(key1674, -1), (key1651, -1), (key1648, 2), (key1674, -1), (key1651, -1), (key1642, 2), (key1536, 2), (key1609, -1), (key1531, -1), (key1648, 2), (key1609, -1), (key1531, -1), (key1832, 1), (key1809, 1), (key1806, -2), (key1832, 1), (key1809, 1), (key1642, -2), (key1261, -2), (key1609, 1), (key1256, 1), (key1806, -2), (key1609, 1), (key1256, 1), (key1832, -1), (key1768, -1), (key1806, 1), (key1765, 1), (key1674, 1), (key1268, 1), (key1648, -1), (key1265, -1), (key1832, -1), (key1768, -1), (key1674, 1), (key1268, 1), (key1806, 1), (key1765, 1), (key1648, -1), (key1265, -1)]

theorem rawRowCheck5555 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5555 := by decide +kernel

def row5555 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5555 : row5555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5555 := by decide +kernel

theorem rowEval5555 (x : Key → ℝ) : Integer.Sparse.eval row5555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5555, Integer.Sparse.eval_collectBalanced, rawRowCheck5555]

def rawRow5556 : Integer.Sparse Key := [(key1765, -1), (key1768, -1), (key1768, 2), (key1806, -1), (key1809, -1), (key1806, 2), (key1837, 2), (key1809, -1), (key1837, -1), (key1832, 2), (key1832, -1), (key1848, -1), (key1265, 1), (key1268, 1), (key1268, -2), (key1648, 1), (key1651, 1), (key1648, -2), (key1837, -2), (key1651, 1), (key1837, 1), (key1674, -2), (key1674, 1), (key1848, 1), (key1256, -1), (key1268, -1), (key1261, 1), (key1268, 1), (key1531, 1), (key1768, 1), (key1536, -1), (key1768, -1), (key1609, -1), (key1651, -1), (key1609, 1), (key1809, 1), (key1642, 1), (key1674, 1), (key1642, -1), (key1832, -1)]

theorem rawRowCheck5556 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5556 := by decide +kernel

def row5556 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5556 : row5556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5556 := by decide +kernel

theorem rowEval5556 (x : Key → ℝ) : Integer.Sparse.eval row5556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5556, Integer.Sparse.eval_collectBalanced, rawRowCheck5556]

def rawRow5557 : Integer.Sparse Key := [(key1768, -1), (key1765, -1), (key1768, 2), (key1809, -1), (key1806, -1), (key1837, 2), (key1806, 2), (key1837, -1), (key1809, -1), (key1832, 2), (key1848, -1), (key1832, -1), (key1268, 1), (key1265, 1), (key1268, -2), (key1651, 1), (key1648, 1), (key1837, -2), (key1648, -2), (key1837, 1), (key1651, 1), (key1674, -2), (key1848, 1), (key1674, 1), (key1268, -1), (key1256, -1), (key1268, 1), (key1261, 1), (key1768, 1), (key1531, 1), (key1768, -1), (key1536, -1), (key1651, -1), (key1609, -1), (key1809, 1), (key1609, 1), (key1674, 1), (key1642, 1), (key1832, -1), (key1642, -1)]

theorem rawRowCheck5557 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5557 := by decide +kernel

def row5557 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5557 : row5557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5557 := by decide +kernel

theorem rowEval5557 (x : Key → ℝ) : Integer.Sparse.eval row5557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5557, Integer.Sparse.eval_collectBalanced, rawRowCheck5557]

def rawRow5558 : Integer.Sparse Key := [(key1768, -1), (key1768, -1), (key1765, 2), (key1837, -1), (key1837, -1), (key1809, 2), (key1809, 2), (key1806, -1), (key1806, -1), (key1848, 2), (key1832, -1), (key1832, -1), (key1268, 1), (key1268, 1), (key1265, -2), (key1837, 1), (key1837, 1), (key1651, -2), (key1651, -2), (key1648, 1), (key1648, 1), (key1848, -2), (key1674, 1), (key1674, 1), (key1261, -1), (key1261, -1), (key1256, 1), (key1256, 1), (key1536, 1), (key1536, 1), (key1531, -1), (key1531, -1), (key1809, -1), (key1809, -1), (key1651, 1), (key1651, 1), (key1832, 1), (key1832, 1), (key1674, -1), (key1674, -1)]

theorem rawRowCheck5558 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5558 := by decide +kernel

def row5558 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5558 : row5558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5558 := by decide +kernel

theorem rowEval5558 (x : Key → ℝ) : Integer.Sparse.eval row5558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5558, Integer.Sparse.eval_collectBalanced, rawRowCheck5558]

def rawRow5559 : Integer.Sparse Key := [(key1806, -1), (key1809, -1), (key1832, 2), (key1765, -1), (key1768, -1), (key1806, 2), (key1837, 2), (key1832, -1), (key1848, -1), (key1768, 2), (key1809, -1), (key1837, -1), (key1648, 1), (key1651, 1), (key1674, -2), (key1265, 1), (key1268, 1), (key1648, -2), (key1837, -2), (key1674, 1), (key1848, 1), (key1268, -2), (key1651, 1), (key1837, 1), (key1609, -1), (key1651, -1), (key1642, 1), (key1674, 1), (key1609, 1), (key1809, 1), (key1642, -1), (key1832, -1), (key1256, -1), (key1268, -1), (key1531, 1), (key1768, 1), (key1261, 1), (key1268, 1), (key1536, -1), (key1768, -1)]

theorem rawRowCheck5559 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5559 := by decide +kernel

def row5559 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5559 : row5559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5559 := by decide +kernel

theorem rowEval5559 (x : Key → ℝ) : Integer.Sparse.eval row5559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5559, Integer.Sparse.eval_collectBalanced, rawRowCheck5559]

def rawRow5560 : Integer.Sparse Key := [(key1809, -1), (key1806, -1), (key1832, 2), (key1768, -1), (key1765, -1), (key1837, 2), (key1806, 2), (key1848, -1), (key1832, -1), (key1768, 2), (key1837, -1), (key1809, -1), (key1651, 1), (key1648, 1), (key1674, -2), (key1268, 1), (key1265, 1), (key1837, -2), (key1648, -2), (key1848, 1), (key1674, 1), (key1268, -2), (key1837, 1), (key1651, 1), (key1651, -1), (key1609, -1), (key1674, 1), (key1642, 1), (key1809, 1), (key1609, 1), (key1832, -1), (key1642, -1), (key1268, -1), (key1256, -1), (key1768, 1), (key1531, 1), (key1268, 1), (key1261, 1), (key1768, -1), (key1536, -1)]

theorem rawRowCheck5560 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5560 := by decide +kernel

def row5560 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5560 : row5560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5560 := by decide +kernel

theorem rowEval5560 (x : Key → ℝ) : Integer.Sparse.eval row5560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5560, Integer.Sparse.eval_collectBalanced, rawRowCheck5560]

def rawRow5561 : Integer.Sparse Key := [(key1806, -1), (key1832, -1), (key1809, 2), (key1806, -1), (key1832, -1), (key1765, 2), (key1848, 2), (key1768, -1), (key1837, -1), (key1809, 2), (key1768, -1), (key1837, -1), (key1648, 1), (key1674, 1), (key1651, -2), (key1648, 1), (key1674, 1), (key1265, -2), (key1848, -2), (key1268, 1), (key1837, 1), (key1651, -2), (key1268, 1), (key1837, 1), (key1531, -1), (key1674, -1), (key1536, 1), (key1651, 1), (key1256, 1), (key1832, 1), (key1261, -1), (key1809, -1), (key1531, -1), (key1674, -1), (key1256, 1), (key1832, 1), (key1536, 1), (key1651, 1), (key1261, -1), (key1809, -1)]

theorem rawRowCheck5561 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5561 := by decide +kernel

def row5561 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5561 : row5561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5561 := by decide +kernel

theorem rowEval5561 (x : Key → ℝ) : Integer.Sparse.eval row5561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5561, Integer.Sparse.eval_collectBalanced, rawRowCheck5561]

def rawRow5562 : Integer.Sparse Key := [(key1832, -1), (key1806, -1), (key1809, 2), (key1832, -1), (key1806, -1), (key1848, 2), (key1765, 2), (key1837, -1), (key1768, -1), (key1809, 2), (key1837, -1), (key1768, -1), (key1674, 1), (key1648, 1), (key1651, -2), (key1674, 1), (key1648, 1), (key1848, -2), (key1265, -2), (key1837, 1), (key1268, 1), (key1651, -2), (key1837, 1), (key1268, 1), (key1674, -1), (key1531, -1), (key1651, 1), (key1536, 1), (key1832, 1), (key1256, 1), (key1809, -1), (key1261, -1), (key1674, -1), (key1531, -1), (key1832, 1), (key1256, 1), (key1651, 1), (key1536, 1), (key1809, -1), (key1261, -1)]

theorem rawRowCheck5562 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5562 := by decide +kernel

def row5562 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5562 : row5562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5562 := by decide +kernel

theorem rowEval5562 (x : Key → ℝ) : Integer.Sparse.eval row5562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5562, Integer.Sparse.eval_collectBalanced, rawRowCheck5562]

def rawRow5563 : Integer.Sparse Key := [(key1809, -1), (key1832, -1), (key1806, 2), (key1837, -1), (key1848, -1), (key1768, 2), (key1832, 2), (key1765, -1), (key1806, -1), (key1837, 2), (key1768, -1), (key1809, -1), (key1651, 1), (key1674, 1), (key1648, -2), (key1837, 1), (key1848, 1), (key1268, -2), (key1674, -2), (key1265, 1), (key1648, 1), (key1837, -2), (key1268, 1), (key1651, 1), (key1536, -1), (key1642, -1), (key1531, 1), (key1609, 1), (key1261, 1), (key1642, 1), (key1256, -1), (key1609, -1), (key1768, -1), (key1832, -1), (key1268, 1), (key1674, 1), (key1768, 1), (key1809, 1), (key1268, -1), (key1651, -1)]

theorem rawRowCheck5563 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5563 := by decide +kernel

def row5563 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5563 : row5563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5563 := by decide +kernel

theorem rowEval5563 (x : Key → ℝ) : Integer.Sparse.eval row5563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5563, Integer.Sparse.eval_collectBalanced, rawRowCheck5563]

def rawRow5564 : Integer.Sparse Key := [(key1832, -1), (key1809, -1), (key1806, 2), (key1848, -1), (key1837, -1), (key1832, 2), (key1768, 2), (key1806, -1), (key1765, -1), (key1837, 2), (key1809, -1), (key1768, -1), (key1674, 1), (key1651, 1), (key1648, -2), (key1848, 1), (key1837, 1), (key1674, -2), (key1268, -2), (key1648, 1), (key1265, 1), (key1837, -2), (key1651, 1), (key1268, 1), (key1642, -1), (key1536, -1), (key1609, 1), (key1531, 1), (key1642, 1), (key1261, 1), (key1609, -1), (key1256, -1), (key1832, -1), (key1768, -1), (key1674, 1), (key1268, 1), (key1809, 1), (key1768, 1), (key1651, -1), (key1268, -1)]

theorem rawRowCheck5564 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5564 := by decide +kernel

def row5564 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5564 : row5564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5564 := by decide +kernel

theorem rowEval5564 (x : Key → ℝ) : Integer.Sparse.eval row5564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5564, Integer.Sparse.eval_collectBalanced, rawRowCheck5564]

def rawRow5565 : Integer.Sparse Key := [(key1837, -1), (key1837, -1), (key1848, 2), (key1768, -1), (key1768, -1), (key1809, 2), (key1809, 2), (key1832, -1), (key1832, -1), (key1765, 2), (key1806, -1), (key1806, -1), (key1837, 1), (key1837, 1), (key1848, -2), (key1268, 1), (key1268, 1), (key1651, -2), (key1651, -2), (key1674, 1), (key1674, 1), (key1265, -2), (key1648, 1), (key1648, 1), (key1809, -1), (key1809, -1), (key1832, 1), (key1832, 1), (key1651, 1), (key1651, 1), (key1674, -1), (key1674, -1), (key1261, -1), (key1261, -1), (key1536, 1), (key1536, 1), (key1256, 1), (key1256, 1), (key1531, -1), (key1531, -1)]

theorem rawRowCheck5565 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1 = rawRow5565 := by decide +kernel

def row5565 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

theorem rowCheck5565 : row5565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5565 := by decide +kernel

theorem rowEval5565 (x : Key → ℝ) : Integer.Sparse.eval row5565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5565, Integer.Sparse.eval_collectBalanced, rawRowCheck5565]

def rawRow5566 : Integer.Sparse Key := [(key1837, -1), (key1848, -1), (key1837, 2), (key1809, -1), (key1832, -1), (key1768, 2), (key1832, 2), (key1768, -1), (key1809, -1), (key1806, 2), (key1765, -1), (key1806, -1), (key1837, 1), (key1848, 1), (key1837, -2), (key1651, 1), (key1674, 1), (key1268, -2), (key1674, -2), (key1268, 1), (key1651, 1), (key1648, -2), (key1265, 1), (key1648, 1), (key1768, -1), (key1832, -1), (key1768, 1), (key1809, 1), (key1268, 1), (key1674, 1), (key1268, -1), (key1651, -1), (key1536, -1), (key1642, -1), (key1261, 1), (key1642, 1), (key1531, 1), (key1609, 1), (key1256, -1), (key1609, -1)]

theorem rawRowCheck5566 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1 = rawRow5566 := by decide +kernel

def row5566 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5566 : row5566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5566 := by decide +kernel

theorem rowEval5566 (x : Key → ℝ) : Integer.Sparse.eval row5566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5566, Integer.Sparse.eval_collectBalanced, rawRowCheck5566]

def rawRow5567 : Integer.Sparse Key := [(key1848, -1), (key1837, -1), (key1837, 2), (key1832, -1), (key1809, -1), (key1832, 2), (key1768, 2), (key1809, -1), (key1768, -1), (key1806, 2), (key1806, -1), (key1765, -1), (key1848, 1), (key1837, 1), (key1837, -2), (key1674, 1), (key1651, 1), (key1674, -2), (key1268, -2), (key1651, 1), (key1268, 1), (key1648, -2), (key1648, 1), (key1265, 1), (key1832, -1), (key1768, -1), (key1809, 1), (key1768, 1), (key1674, 1), (key1268, 1), (key1651, -1), (key1268, -1), (key1642, -1), (key1536, -1), (key1642, 1), (key1261, 1), (key1609, 1), (key1531, 1), (key1609, -1), (key1256, -1)]

theorem rawRowCheck5567 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1 = rawRow5567 := by decide +kernel

def row5567 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

theorem rowCheck5567 : row5567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5567 := by decide +kernel

theorem rowEval5567 (x : Key → ℝ) : Integer.Sparse.eval row5567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5567, Integer.Sparse.eval_collectBalanced, rawRowCheck5567]

def rawRow5568 : Integer.Sparse Key := [(key2378, -1), (key2378, -1), (key2381, 2), (key2378, -1), (key2378, -1), (key2390, 2), (key2390, 2), (key2392, -1), (key2392, -1), (key2381, 2), (key2392, -1), (key2392, -1), (key2406, 1), (key2406, 1), (key2409, -2), (key2406, 1), (key2406, 1), (key2437, -2), (key2437, -2), (key2440, 1), (key2440, 1), (key2409, -2), (key2440, 1), (key2440, 1), (key2480, -1), (key2480, -1), (key2482, 1), (key2482, 1), (key2503, 1), (key2503, 1), (key2506, -1), (key2506, -1), (key2480, -1), (key2480, -1), (key2503, 1), (key2503, 1), (key2482, 1), (key2482, 1), (key2506, -1), (key2506, -1)]

theorem rawRowCheck5568 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form2 = rawRow5568 := by decide +kernel

def row5568 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, 4), (key2409, -4), (key2437, -4), (key2440, 4), (key2480, -4), (key2482, 4), (key2503, 4), (key2506, -4)]

theorem rowCheck5568 : row5568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5568 := by decide +kernel

theorem rowEval5568 (x : Key → ℝ) : Integer.Sparse.eval row5568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5568, Integer.Sparse.eval_collectBalanced, rawRowCheck5568]

def rawRow5569 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2378, 2), (key2390, -1), (key2392, -1), (key2378, 2), (key2392, 2), (key2378, -1), (key2390, -1), (key2392, 2), (key2381, -1), (key2392, -1), (key2406, 1), (key2409, 1), (key2406, -2), (key2437, 1), (key2440, 1), (key2406, -2), (key2440, -2), (key2406, 1), (key2437, 1), (key2440, -2), (key2409, 1), (key2440, 1), (key2472, -1), (key2482, -1), (key2472, 1), (key2480, 1), (key2472, 1), (key2506, 1), (key2472, -1), (key2503, -1), (key2503, -1), (key2522, -1), (key2480, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2482, -1), (key2522, -1)]

theorem rawRowCheck5569 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form2 = rawRow5569 := by decide +kernel

def row5569 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5569 : row5569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5569 := by decide +kernel

theorem rowEval5569 (x : Key → ℝ) : Integer.Sparse.eval row5569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5569, Integer.Sparse.eval_collectBalanced, rawRowCheck5569]

def rawRow5570 : Integer.Sparse Key := [(key2381, -1), (key2378, -1), (key2378, 2), (key2392, -1), (key2390, -1), (key2392, 2), (key2378, 2), (key2390, -1), (key2378, -1), (key2392, 2), (key2392, -1), (key2381, -1), (key2409, 1), (key2406, 1), (key2406, -2), (key2440, 1), (key2437, 1), (key2440, -2), (key2406, -2), (key2437, 1), (key2406, 1), (key2440, -2), (key2440, 1), (key2409, 1), (key2482, -1), (key2472, -1), (key2480, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, -1), (key2472, -1), (key2522, -1), (key2503, -1), (key2522, 1), (key2480, 1), (key2522, 1), (key2506, 1), (key2522, -1), (key2482, -1)]

theorem rawRowCheck5570 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form2 = rawRow5570 := by decide +kernel

def row5570 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5570 : row5570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5570 := by decide +kernel

theorem rowEval5570 (x : Key → ℝ) : Integer.Sparse.eval row5570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5570, Integer.Sparse.eval_collectBalanced, rawRowCheck5570]

def rawRow5571 : Integer.Sparse Key := [(key2390, -1), (key2392, -1), (key2392, 2), (key2378, -1), (key2381, -1), (key2378, 2), (key2392, 2), (key2381, -1), (key2392, -1), (key2378, 2), (key2378, -1), (key2390, -1), (key2437, 1), (key2440, 1), (key2440, -2), (key2406, 1), (key2409, 1), (key2406, -2), (key2440, -2), (key2409, 1), (key2440, 1), (key2406, -2), (key2406, 1), (key2437, 1), (key2503, -1), (key2522, -1), (key2506, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, -1), (key2522, -1), (key2472, -1), (key2482, -1), (key2472, 1), (key2506, 1), (key2472, 1), (key2480, 1), (key2472, -1), (key2503, -1)]

theorem rawRowCheck5571 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form2 = rawRow5571 := by decide +kernel

def row5571 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5571 : row5571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5571 := by decide +kernel

theorem rowEval5571 (x : Key → ℝ) : Integer.Sparse.eval row5571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5571, Integer.Sparse.eval_collectBalanced, rawRowCheck5571]

def rawRow5572 : Integer.Sparse Key := [(key2392, -1), (key2390, -1), (key2392, 2), (key2381, -1), (key2378, -1), (key2392, 2), (key2378, 2), (key2392, -1), (key2381, -1), (key2378, 2), (key2390, -1), (key2378, -1), (key2440, 1), (key2437, 1), (key2440, -2), (key2409, 1), (key2406, 1), (key2440, -2), (key2406, -2), (key2440, 1), (key2409, 1), (key2406, -2), (key2437, 1), (key2406, 1), (key2522, -1), (key2503, -1), (key2522, 1), (key2506, 1), (key2522, 1), (key2480, 1), (key2522, -1), (key2482, -1), (key2482, -1), (key2472, -1), (key2506, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, -1), (key2472, -1)]

theorem rawRowCheck5572 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form2 = rawRow5572 := by decide +kernel

def row5572 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5572 : row5572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5572 := by decide +kernel

theorem rowEval5572 (x : Key → ℝ) : Integer.Sparse.eval row5572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5572, Integer.Sparse.eval_collectBalanced, rawRowCheck5572]

def rawRow5573 : Integer.Sparse Key := [(key2392, -1), (key2392, -1), (key2390, 2), (key2392, -1), (key2392, -1), (key2381, 2), (key2381, 2), (key2378, -1), (key2378, -1), (key2390, 2), (key2378, -1), (key2378, -1), (key2440, 1), (key2440, 1), (key2437, -2), (key2440, 1), (key2440, 1), (key2409, -2), (key2409, -2), (key2406, 1), (key2406, 1), (key2437, -2), (key2406, 1), (key2406, 1), (key2506, -1), (key2506, -1), (key2503, 1), (key2503, 1), (key2482, 1), (key2482, 1), (key2480, -1), (key2480, -1), (key2506, -1), (key2506, -1), (key2482, 1), (key2482, 1), (key2503, 1), (key2503, 1), (key2480, -1), (key2480, -1)]

theorem rawRowCheck5573 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form2 = rawRow5573 := by decide +kernel

def row5573 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, 4), (key2409, -4), (key2437, -4), (key2440, 4), (key2480, -4), (key2482, 4), (key2503, 4), (key2506, -4)]

theorem rowCheck5573 : row5573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5573 := by decide +kernel

theorem rowEval5573 (x : Key → ℝ) : Integer.Sparse.eval row5573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5573, Integer.Sparse.eval_collectBalanced, rawRowCheck5573]

def rawRow5574 : Integer.Sparse Key := [(key2406, -1), (key2406, -1), (key2409, 2), (key2472, -1), (key2472, -1), (key2480, 2), (key2480, 2), (key2482, -1), (key2482, -1), (key2538, 2), (key2543, -1), (key2543, -1), (key2378, 1), (key2378, 1), (key2381, -2), (key2472, 1), (key2472, 1), (key2503, -2), (key2503, -2), (key2506, 1), (key2506, 1), (key2538, -2), (key2554, 1), (key2554, 1), (key2390, -1), (key2390, -1), (key2392, 1), (key2392, 1), (key2437, 1), (key2437, 1), (key2440, -1), (key2440, -1), (key2480, -1), (key2480, -1), (key2503, 1), (key2503, 1), (key2543, 1), (key2543, 1), (key2554, -1), (key2554, -1)]

theorem rawRowCheck5574 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form2 = rawRow5574 := by decide +kernel

def row5574 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5574 : row5574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5574 := by decide +kernel

theorem rowEval5574 (x : Key → ℝ) : Integer.Sparse.eval row5574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5574, Integer.Sparse.eval_collectBalanced, rawRowCheck5574]

def rawRow5575 : Integer.Sparse Key := [(key2406, -1), (key2409, -1), (key2406, 2), (key2480, -1), (key2482, -1), (key2472, 2), (key2482, 2), (key2472, -1), (key2480, -1), (key2543, 2), (key2538, -1), (key2543, -1), (key2378, 1), (key2381, 1), (key2378, -2), (key2503, 1), (key2506, 1), (key2472, -2), (key2506, -2), (key2472, 1), (key2503, 1), (key2554, -2), (key2538, 1), (key2554, 1), (key2378, -1), (key2392, -1), (key2378, 1), (key2390, 1), (key2406, 1), (key2440, 1), (key2406, -1), (key2437, -1), (key2503, -1), (key2522, -1), (key2480, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2543, -1), (key2563, -1)]

theorem rawRowCheck5575 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form2 = rawRow5575 := by decide +kernel

def row5575 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5575 : row5575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5575 := by decide +kernel

theorem rowEval5575 (x : Key → ℝ) : Integer.Sparse.eval row5575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5575, Integer.Sparse.eval_collectBalanced, rawRowCheck5575]

def rawRow5576 : Integer.Sparse Key := [(key2409, -1), (key2406, -1), (key2406, 2), (key2482, -1), (key2480, -1), (key2482, 2), (key2472, 2), (key2480, -1), (key2472, -1), (key2543, 2), (key2543, -1), (key2538, -1), (key2381, 1), (key2378, 1), (key2378, -2), (key2506, 1), (key2503, 1), (key2506, -2), (key2472, -2), (key2503, 1), (key2472, 1), (key2554, -2), (key2554, 1), (key2538, 1), (key2392, -1), (key2378, -1), (key2390, 1), (key2378, 1), (key2440, 1), (key2406, 1), (key2437, -1), (key2406, -1), (key2522, -1), (key2503, -1), (key2522, 1), (key2480, 1), (key2563, 1), (key2554, 1), (key2563, -1), (key2543, -1)]

theorem rawRowCheck5576 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form2 = rawRow5576 := by decide +kernel

def row5576 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5576 : row5576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5576 := by decide +kernel

theorem rowEval5576 (x : Key → ℝ) : Integer.Sparse.eval row5576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5576, Integer.Sparse.eval_collectBalanced, rawRowCheck5576]

def rawRow5577 : Integer.Sparse Key := [(key2472, -1), (key2472, -1), (key2538, 2), (key2406, -1), (key2406, -1), (key2480, 2), (key2480, 2), (key2543, -1), (key2543, -1), (key2409, 2), (key2482, -1), (key2482, -1), (key2472, 1), (key2472, 1), (key2538, -2), (key2378, 1), (key2378, 1), (key2503, -2), (key2503, -2), (key2554, 1), (key2554, 1), (key2381, -2), (key2506, 1), (key2506, 1), (key2480, -1), (key2480, -1), (key2543, 1), (key2543, 1), (key2503, 1), (key2503, 1), (key2554, -1), (key2554, -1), (key2390, -1), (key2390, -1), (key2437, 1), (key2437, 1), (key2392, 1), (key2392, 1), (key2440, -1), (key2440, -1)]

theorem rawRowCheck5577 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form2 = rawRow5577 := by decide +kernel

def row5577 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5577 : row5577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5577 := by decide +kernel

theorem rowEval5577 (x : Key → ℝ) : Integer.Sparse.eval row5577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5577, Integer.Sparse.eval_collectBalanced, rawRowCheck5577]

def rawRow5578 : Integer.Sparse Key := [(key2472, -1), (key2538, -1), (key2472, 2), (key2480, -1), (key2543, -1), (key2406, 2), (key2543, 2), (key2406, -1), (key2480, -1), (key2482, 2), (key2409, -1), (key2482, -1), (key2472, 1), (key2538, 1), (key2472, -2), (key2503, 1), (key2554, 1), (key2378, -2), (key2554, -2), (key2378, 1), (key2503, 1), (key2506, -2), (key2381, 1), (key2506, 1), (key2406, -1), (key2543, -1), (key2406, 1), (key2480, 1), (key2378, 1), (key2554, 1), (key2378, -1), (key2503, -1), (key2437, -1), (key2563, -1), (key2390, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2392, -1), (key2522, -1)]

theorem rawRowCheck5578 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form2 = rawRow5578 := by decide +kernel

def row5578 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5578 : row5578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5578 := by decide +kernel

theorem rowEval5578 (x : Key → ℝ) : Integer.Sparse.eval row5578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5578, Integer.Sparse.eval_collectBalanced, rawRowCheck5578]

def rawRow5579 : Integer.Sparse Key := [(key2538, -1), (key2472, -1), (key2472, 2), (key2543, -1), (key2480, -1), (key2543, 2), (key2406, 2), (key2480, -1), (key2406, -1), (key2482, 2), (key2482, -1), (key2409, -1), (key2538, 1), (key2472, 1), (key2472, -2), (key2554, 1), (key2503, 1), (key2554, -2), (key2378, -2), (key2503, 1), (key2378, 1), (key2506, -2), (key2506, 1), (key2381, 1), (key2543, -1), (key2406, -1), (key2480, 1), (key2406, 1), (key2554, 1), (key2378, 1), (key2503, -1), (key2378, -1), (key2563, -1), (key2437, -1), (key2563, 1), (key2390, 1), (key2522, 1), (key2440, 1), (key2522, -1), (key2392, -1)]

theorem rawRowCheck5579 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form2 = rawRow5579 := by decide +kernel

def row5579 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5579 : row5579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5579 := by decide +kernel

theorem rowEval5579 (x : Key → ℝ) : Integer.Sparse.eval row5579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5579, Integer.Sparse.eval_collectBalanced, rawRowCheck5579]

def rawRow5580 : Integer.Sparse Key := [(key2480, -1), (key2482, -1), (key2543, 2), (key2406, -1), (key2409, -1), (key2472, 2), (key2482, 2), (key2538, -1), (key2543, -1), (key2406, 2), (key2472, -1), (key2480, -1), (key2503, 1), (key2506, 1), (key2554, -2), (key2378, 1), (key2381, 1), (key2472, -2), (key2506, -2), (key2538, 1), (key2554, 1), (key2378, -2), (key2472, 1), (key2503, 1), (key2503, -1), (key2522, -1), (key2554, 1), (key2563, 1), (key2480, 1), (key2522, 1), (key2543, -1), (key2563, -1), (key2378, -1), (key2392, -1), (key2406, 1), (key2440, 1), (key2378, 1), (key2390, 1), (key2406, -1), (key2437, -1)]

theorem rawRowCheck5580 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form2 = rawRow5580 := by decide +kernel

def row5580 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5580 : row5580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5580 := by decide +kernel

theorem rowEval5580 (x : Key → ℝ) : Integer.Sparse.eval row5580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5580, Integer.Sparse.eval_collectBalanced, rawRowCheck5580]

def rawRow5581 : Integer.Sparse Key := [(key2482, -1), (key2480, -1), (key2543, 2), (key2409, -1), (key2406, -1), (key2482, 2), (key2472, 2), (key2543, -1), (key2538, -1), (key2406, 2), (key2480, -1), (key2472, -1), (key2506, 1), (key2503, 1), (key2554, -2), (key2381, 1), (key2378, 1), (key2506, -2), (key2472, -2), (key2554, 1), (key2538, 1), (key2378, -2), (key2503, 1), (key2472, 1), (key2522, -1), (key2503, -1), (key2563, 1), (key2554, 1), (key2522, 1), (key2480, 1), (key2563, -1), (key2543, -1), (key2392, -1), (key2378, -1), (key2440, 1), (key2406, 1), (key2390, 1), (key2378, 1), (key2437, -1), (key2406, -1)]

theorem rawRowCheck5581 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form2 = rawRow5581 := by decide +kernel

def row5581 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5581 : row5581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5581 := by decide +kernel

theorem rowEval5581 (x : Key → ℝ) : Integer.Sparse.eval row5581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5581, Integer.Sparse.eval_collectBalanced, rawRowCheck5581]

def rawRow5582 : Integer.Sparse Key := [(key2480, -1), (key2543, -1), (key2482, 2), (key2472, -1), (key2538, -1), (key2406, 2), (key2543, 2), (key2409, -1), (key2482, -1), (key2472, 2), (key2406, -1), (key2480, -1), (key2503, 1), (key2554, 1), (key2506, -2), (key2472, 1), (key2538, 1), (key2378, -2), (key2554, -2), (key2381, 1), (key2506, 1), (key2472, -2), (key2378, 1), (key2503, 1), (key2437, -1), (key2563, -1), (key2440, 1), (key2522, 1), (key2390, 1), (key2563, 1), (key2392, -1), (key2522, -1), (key2406, -1), (key2543, -1), (key2378, 1), (key2554, 1), (key2406, 1), (key2480, 1), (key2378, -1), (key2503, -1)]

theorem rawRowCheck5582 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form2 = rawRow5582 := by decide +kernel

def row5582 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5582 : row5582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5582 := by decide +kernel

theorem rowEval5582 (x : Key → ℝ) : Integer.Sparse.eval row5582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5582, Integer.Sparse.eval_collectBalanced, rawRowCheck5582]

def rawRow5583 : Integer.Sparse Key := [(key2543, -1), (key2480, -1), (key2482, 2), (key2538, -1), (key2472, -1), (key2543, 2), (key2406, 2), (key2482, -1), (key2409, -1), (key2472, 2), (key2480, -1), (key2406, -1), (key2554, 1), (key2503, 1), (key2506, -2), (key2538, 1), (key2472, 1), (key2554, -2), (key2378, -2), (key2506, 1), (key2381, 1), (key2472, -2), (key2503, 1), (key2378, 1), (key2563, -1), (key2437, -1), (key2522, 1), (key2440, 1), (key2563, 1), (key2390, 1), (key2522, -1), (key2392, -1), (key2543, -1), (key2406, -1), (key2554, 1), (key2378, 1), (key2480, 1), (key2406, 1), (key2503, -1), (key2378, -1)]

theorem rawRowCheck5583 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form2 = rawRow5583 := by decide +kernel

def row5583 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5583 : row5583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5583 := by decide +kernel

theorem rowEval5583 (x : Key → ℝ) : Integer.Sparse.eval row5583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5583, Integer.Sparse.eval_collectBalanced, rawRowCheck5583]

def rawRow5584 : Integer.Sparse Key := [(key2482, -1), (key2543, -1), (key2480, 2), (key2482, -1), (key2543, -1), (key2409, 2), (key2538, 2), (key2406, -1), (key2472, -1), (key2480, 2), (key2406, -1), (key2472, -1), (key2506, 1), (key2554, 1), (key2503, -2), (key2506, 1), (key2554, 1), (key2381, -2), (key2538, -2), (key2378, 1), (key2472, 1), (key2503, -2), (key2378, 1), (key2472, 1), (key2440, -1), (key2554, -1), (key2437, 1), (key2503, 1), (key2392, 1), (key2543, 1), (key2390, -1), (key2480, -1), (key2440, -1), (key2554, -1), (key2392, 1), (key2543, 1), (key2437, 1), (key2503, 1), (key2390, -1), (key2480, -1)]

theorem rawRowCheck5584 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form2 = rawRow5584 := by decide +kernel

def row5584 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5584 : row5584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5584 := by decide +kernel

theorem rowEval5584 (x : Key → ℝ) : Integer.Sparse.eval row5584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5584, Integer.Sparse.eval_collectBalanced, rawRowCheck5584]

def rawRow5585 : Integer.Sparse Key := [(key2543, -1), (key2482, -1), (key2480, 2), (key2543, -1), (key2482, -1), (key2538, 2), (key2409, 2), (key2472, -1), (key2406, -1), (key2480, 2), (key2472, -1), (key2406, -1), (key2554, 1), (key2506, 1), (key2503, -2), (key2554, 1), (key2506, 1), (key2538, -2), (key2381, -2), (key2472, 1), (key2378, 1), (key2503, -2), (key2472, 1), (key2378, 1), (key2554, -1), (key2440, -1), (key2503, 1), (key2437, 1), (key2543, 1), (key2392, 1), (key2480, -1), (key2390, -1), (key2554, -1), (key2440, -1), (key2543, 1), (key2392, 1), (key2503, 1), (key2437, 1), (key2480, -1), (key2390, -1)]

theorem rawRowCheck5585 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form2 = rawRow5585 := by decide +kernel

def row5585 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5585 : row5585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5585 := by decide +kernel

theorem rowEval5585 (x : Key → ℝ) : Integer.Sparse.eval row5585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5585, Integer.Sparse.eval_collectBalanced, rawRowCheck5585]

def rawRow5586 : Integer.Sparse Key := [(key2437, -1), (key2440, -1), (key2440, 2), (key2503, -1), (key2506, -1), (key2503, 2), (key2522, 2), (key2506, -1), (key2522, -1), (key2554, 2), (key2554, -1), (key2563, -1), (key2390, 1), (key2392, 1), (key2392, -2), (key2480, 1), (key2482, 1), (key2480, -2), (key2522, -2), (key2482, 1), (key2522, 1), (key2543, -2), (key2543, 1), (key2563, 1), (key2378, -1), (key2392, -1), (key2381, 1), (key2392, 1), (key2406, 1), (key2440, 1), (key2409, -1), (key2440, -1), (key2472, -1), (key2482, -1), (key2472, 1), (key2506, 1), (key2538, 1), (key2543, 1), (key2538, -1), (key2554, -1)]

theorem rawRowCheck5586 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form2 = rawRow5586 := by decide +kernel

def row5586 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5586 : row5586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5586 := by decide +kernel

theorem rowEval5586 (x : Key → ℝ) : Integer.Sparse.eval row5586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5586, Integer.Sparse.eval_collectBalanced, rawRowCheck5586]

def rawRow5587 : Integer.Sparse Key := [(key2440, -1), (key2437, -1), (key2440, 2), (key2506, -1), (key2503, -1), (key2522, 2), (key2503, 2), (key2522, -1), (key2506, -1), (key2554, 2), (key2563, -1), (key2554, -1), (key2392, 1), (key2390, 1), (key2392, -2), (key2482, 1), (key2480, 1), (key2522, -2), (key2480, -2), (key2522, 1), (key2482, 1), (key2543, -2), (key2563, 1), (key2543, 1), (key2392, -1), (key2378, -1), (key2392, 1), (key2381, 1), (key2440, 1), (key2406, 1), (key2440, -1), (key2409, -1), (key2482, -1), (key2472, -1), (key2506, 1), (key2472, 1), (key2543, 1), (key2538, 1), (key2554, -1), (key2538, -1)]

theorem rawRowCheck5587 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form2 = rawRow5587 := by decide +kernel

def row5587 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5587 : row5587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5587 := by decide +kernel

theorem rowEval5587 (x : Key → ℝ) : Integer.Sparse.eval row5587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5587, Integer.Sparse.eval_collectBalanced, rawRowCheck5587]

def rawRow5588 : Integer.Sparse Key := [(key2440, -1), (key2440, -1), (key2437, 2), (key2522, -1), (key2522, -1), (key2506, 2), (key2506, 2), (key2503, -1), (key2503, -1), (key2563, 2), (key2554, -1), (key2554, -1), (key2392, 1), (key2392, 1), (key2390, -2), (key2522, 1), (key2522, 1), (key2482, -2), (key2482, -2), (key2480, 1), (key2480, 1), (key2563, -2), (key2543, 1), (key2543, 1), (key2381, -1), (key2381, -1), (key2378, 1), (key2378, 1), (key2409, 1), (key2409, 1), (key2406, -1), (key2406, -1), (key2506, -1), (key2506, -1), (key2482, 1), (key2482, 1), (key2554, 1), (key2554, 1), (key2543, -1), (key2543, -1)]

theorem rawRowCheck5588 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form2 = rawRow5588 := by decide +kernel

def row5588 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5588 : row5588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5588 := by decide +kernel

theorem rowEval5588 (x : Key → ℝ) : Integer.Sparse.eval row5588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5588, Integer.Sparse.eval_collectBalanced, rawRowCheck5588]

def rawRow5589 : Integer.Sparse Key := [(key2503, -1), (key2506, -1), (key2554, 2), (key2437, -1), (key2440, -1), (key2503, 2), (key2522, 2), (key2554, -1), (key2563, -1), (key2440, 2), (key2506, -1), (key2522, -1), (key2480, 1), (key2482, 1), (key2543, -2), (key2390, 1), (key2392, 1), (key2480, -2), (key2522, -2), (key2543, 1), (key2563, 1), (key2392, -2), (key2482, 1), (key2522, 1), (key2472, -1), (key2482, -1), (key2538, 1), (key2543, 1), (key2472, 1), (key2506, 1), (key2538, -1), (key2554, -1), (key2378, -1), (key2392, -1), (key2406, 1), (key2440, 1), (key2381, 1), (key2392, 1), (key2409, -1), (key2440, -1)]

theorem rawRowCheck5589 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form2 = rawRow5589 := by decide +kernel

def row5589 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5589 : row5589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5589 := by decide +kernel

theorem rowEval5589 (x : Key → ℝ) : Integer.Sparse.eval row5589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5589, Integer.Sparse.eval_collectBalanced, rawRowCheck5589]

def rawRow5590 : Integer.Sparse Key := [(key2506, -1), (key2503, -1), (key2554, 2), (key2440, -1), (key2437, -1), (key2522, 2), (key2503, 2), (key2563, -1), (key2554, -1), (key2440, 2), (key2522, -1), (key2506, -1), (key2482, 1), (key2480, 1), (key2543, -2), (key2392, 1), (key2390, 1), (key2522, -2), (key2480, -2), (key2563, 1), (key2543, 1), (key2392, -2), (key2522, 1), (key2482, 1), (key2482, -1), (key2472, -1), (key2543, 1), (key2538, 1), (key2506, 1), (key2472, 1), (key2554, -1), (key2538, -1), (key2392, -1), (key2378, -1), (key2440, 1), (key2406, 1), (key2392, 1), (key2381, 1), (key2440, -1), (key2409, -1)]

theorem rawRowCheck5590 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form2 = rawRow5590 := by decide +kernel

def row5590 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5590 : row5590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5590 := by decide +kernel

theorem rowEval5590 (x : Key → ℝ) : Integer.Sparse.eval row5590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5590, Integer.Sparse.eval_collectBalanced, rawRowCheck5590]

def rawRow5591 : Integer.Sparse Key := [(key2503, -1), (key2554, -1), (key2506, 2), (key2503, -1), (key2554, -1), (key2437, 2), (key2563, 2), (key2440, -1), (key2522, -1), (key2506, 2), (key2440, -1), (key2522, -1), (key2480, 1), (key2543, 1), (key2482, -2), (key2480, 1), (key2543, 1), (key2390, -2), (key2563, -2), (key2392, 1), (key2522, 1), (key2482, -2), (key2392, 1), (key2522, 1), (key2406, -1), (key2543, -1), (key2409, 1), (key2482, 1), (key2378, 1), (key2554, 1), (key2381, -1), (key2506, -1), (key2406, -1), (key2543, -1), (key2378, 1), (key2554, 1), (key2409, 1), (key2482, 1), (key2381, -1), (key2506, -1)]

theorem rawRowCheck5591 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form2 = rawRow5591 := by decide +kernel

def row5591 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5591 : row5591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5591 := by decide +kernel

theorem rowEval5591 (x : Key → ℝ) : Integer.Sparse.eval row5591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5591, Integer.Sparse.eval_collectBalanced, rawRowCheck5591]

def rawRow5592 : Integer.Sparse Key := [(key2554, -1), (key2503, -1), (key2506, 2), (key2554, -1), (key2503, -1), (key2563, 2), (key2437, 2), (key2522, -1), (key2440, -1), (key2506, 2), (key2522, -1), (key2440, -1), (key2543, 1), (key2480, 1), (key2482, -2), (key2543, 1), (key2480, 1), (key2563, -2), (key2390, -2), (key2522, 1), (key2392, 1), (key2482, -2), (key2522, 1), (key2392, 1), (key2543, -1), (key2406, -1), (key2482, 1), (key2409, 1), (key2554, 1), (key2378, 1), (key2506, -1), (key2381, -1), (key2543, -1), (key2406, -1), (key2554, 1), (key2378, 1), (key2482, 1), (key2409, 1), (key2506, -1), (key2381, -1)]

theorem rawRowCheck5592 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form2 = rawRow5592 := by decide +kernel

def row5592 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5592 : row5592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5592 := by decide +kernel

theorem rowEval5592 (x : Key → ℝ) : Integer.Sparse.eval row5592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5592, Integer.Sparse.eval_collectBalanced, rawRowCheck5592]

def rawRow5593 : Integer.Sparse Key := [(key2506, -1), (key2554, -1), (key2503, 2), (key2522, -1), (key2563, -1), (key2440, 2), (key2554, 2), (key2437, -1), (key2503, -1), (key2522, 2), (key2440, -1), (key2506, -1), (key2482, 1), (key2543, 1), (key2480, -2), (key2522, 1), (key2563, 1), (key2392, -2), (key2543, -2), (key2390, 1), (key2480, 1), (key2522, -2), (key2392, 1), (key2482, 1), (key2409, -1), (key2538, -1), (key2406, 1), (key2472, 1), (key2381, 1), (key2538, 1), (key2378, -1), (key2472, -1), (key2440, -1), (key2554, -1), (key2392, 1), (key2543, 1), (key2440, 1), (key2506, 1), (key2392, -1), (key2482, -1)]

theorem rawRowCheck5593 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form2 = rawRow5593 := by decide +kernel

def row5593 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5593 : row5593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5593 := by decide +kernel

theorem rowEval5593 (x : Key → ℝ) : Integer.Sparse.eval row5593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5593, Integer.Sparse.eval_collectBalanced, rawRowCheck5593]

def rawRow5594 : Integer.Sparse Key := [(key2554, -1), (key2506, -1), (key2503, 2), (key2563, -1), (key2522, -1), (key2554, 2), (key2440, 2), (key2503, -1), (key2437, -1), (key2522, 2), (key2506, -1), (key2440, -1), (key2543, 1), (key2482, 1), (key2480, -2), (key2563, 1), (key2522, 1), (key2543, -2), (key2392, -2), (key2480, 1), (key2390, 1), (key2522, -2), (key2482, 1), (key2392, 1), (key2538, -1), (key2409, -1), (key2472, 1), (key2406, 1), (key2538, 1), (key2381, 1), (key2472, -1), (key2378, -1), (key2554, -1), (key2440, -1), (key2543, 1), (key2392, 1), (key2506, 1), (key2440, 1), (key2482, -1), (key2392, -1)]

theorem rawRowCheck5594 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form2 = rawRow5594 := by decide +kernel

def row5594 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5594 : row5594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5594 := by decide +kernel

theorem rowEval5594 (x : Key → ℝ) : Integer.Sparse.eval row5594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5594, Integer.Sparse.eval_collectBalanced, rawRowCheck5594]

def rawRow5595 : Integer.Sparse Key := [(key2522, -1), (key2522, -1), (key2563, 2), (key2440, -1), (key2440, -1), (key2506, 2), (key2506, 2), (key2554, -1), (key2554, -1), (key2437, 2), (key2503, -1), (key2503, -1), (key2522, 1), (key2522, 1), (key2563, -2), (key2392, 1), (key2392, 1), (key2482, -2), (key2482, -2), (key2543, 1), (key2543, 1), (key2390, -2), (key2480, 1), (key2480, 1), (key2506, -1), (key2506, -1), (key2554, 1), (key2554, 1), (key2482, 1), (key2482, 1), (key2543, -1), (key2543, -1), (key2381, -1), (key2381, -1), (key2409, 1), (key2409, 1), (key2378, 1), (key2378, 1), (key2406, -1), (key2406, -1)]

theorem rawRowCheck5595 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form2 = rawRow5595 := by decide +kernel

def row5595 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

theorem rowCheck5595 : row5595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5595 := by decide +kernel

theorem rowEval5595 (x : Key → ℝ) : Integer.Sparse.eval row5595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5595, Integer.Sparse.eval_collectBalanced, rawRowCheck5595]

def rawRow5596 : Integer.Sparse Key := [(key2522, -1), (key2563, -1), (key2522, 2), (key2506, -1), (key2554, -1), (key2440, 2), (key2554, 2), (key2440, -1), (key2506, -1), (key2503, 2), (key2437, -1), (key2503, -1), (key2522, 1), (key2563, 1), (key2522, -2), (key2482, 1), (key2543, 1), (key2392, -2), (key2543, -2), (key2392, 1), (key2482, 1), (key2480, -2), (key2390, 1), (key2480, 1), (key2440, -1), (key2554, -1), (key2440, 1), (key2506, 1), (key2392, 1), (key2543, 1), (key2392, -1), (key2482, -1), (key2409, -1), (key2538, -1), (key2381, 1), (key2538, 1), (key2406, 1), (key2472, 1), (key2378, -1), (key2472, -1)]

theorem rawRowCheck5596 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form2 = rawRow5596 := by decide +kernel

def row5596 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5596 : row5596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5596 := by decide +kernel

theorem rowEval5596 (x : Key → ℝ) : Integer.Sparse.eval row5596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5596, Integer.Sparse.eval_collectBalanced, rawRowCheck5596]

def rawRow5597 : Integer.Sparse Key := [(key2563, -1), (key2522, -1), (key2522, 2), (key2554, -1), (key2506, -1), (key2554, 2), (key2440, 2), (key2506, -1), (key2440, -1), (key2503, 2), (key2503, -1), (key2437, -1), (key2563, 1), (key2522, 1), (key2522, -2), (key2543, 1), (key2482, 1), (key2543, -2), (key2392, -2), (key2482, 1), (key2392, 1), (key2480, -2), (key2480, 1), (key2390, 1), (key2554, -1), (key2440, -1), (key2506, 1), (key2440, 1), (key2543, 1), (key2392, 1), (key2482, -1), (key2392, -1), (key2538, -1), (key2409, -1), (key2538, 1), (key2381, 1), (key2472, 1), (key2406, 1), (key2472, -1), (key2378, -1)]

theorem rawRowCheck5597 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form2 = rawRow5597 := by decide +kernel

def row5597 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

theorem rowCheck5597 : row5597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5597 := by decide +kernel

theorem rowEval5597 (x : Key → ℝ) : Integer.Sparse.eval row5597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5597, Integer.Sparse.eval_collectBalanced, rawRowCheck5597]

def rawRow5598 : Integer.Sparse Key := [(key982, -4), (key986, 2), (key986, 2), (key986, 2), (key986, 2), (key988, -4), (key1096, 2), (key1100, -1), (key1100, -1), (key1096, 2), (key1185, -1), (key1185, -1), (key1100, -1), (key1100, -1), (key1185, -1), (key1185, -1), (key1186, 2), (key1186, 2), (key1171, -1), (key1171, -1), (key1175, 2), (key1171, -1), (key1171, -1), (key1222, 2), (key1222, 2), (key1224, -1), (key1224, -1), (key1175, 2), (key1224, -1), (key1224, -1)]

theorem rawRowCheck5598 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5598 := by decide +kernel

def row5598 : Integer.Sparse Key := [(key982, -4), (key986, 8), (key988, -4), (key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

theorem rowCheck5598 : row5598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5598 := by decide +kernel

theorem rowEval5598 (x : Key → ℝ) : Integer.Sparse.eval row5598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5598, Integer.Sparse.eval_collectBalanced, rawRowCheck5598]

def rawRow5599 : Integer.Sparse Key := [(key986, -4), (key982, 2), (key986, 2), (key986, 2), (key988, 2), (key986, -4), (key1100, 2), (key1096, -1), (key1100, -1), (key1185, 2), (key1096, -1), (key1185, -1), (key1185, -1), (key1186, -1), (key1100, -1), (key1186, -1), (key1100, 2), (key1185, 2), (key1171, -1), (key1175, -1), (key1171, 2), (key1222, -1), (key1224, -1), (key1171, 2), (key1224, 2), (key1171, -1), (key1222, -1), (key1224, 2), (key1175, -1), (key1224, -1)]

theorem rawRowCheck5599 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5599 := by decide +kernel

def row5599 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5599 : row5599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5599 := by decide +kernel

theorem rowEval5599 (x : Key → ℝ) : Integer.Sparse.eval row5599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5599, Integer.Sparse.eval_collectBalanced, rawRowCheck5599]

def rawRow5600 : Integer.Sparse Key := [(key986, -4), (key986, 2), (key982, 2), (key988, 2), (key986, 2), (key986, -4), (key1100, 2), (key1100, -1), (key1096, -1), (key1185, 2), (key1185, -1), (key1096, -1), (key1186, -1), (key1185, -1), (key1186, -1), (key1100, -1), (key1185, 2), (key1100, 2), (key1175, -1), (key1171, -1), (key1171, 2), (key1224, -1), (key1222, -1), (key1224, 2), (key1171, 2), (key1222, -1), (key1171, -1), (key1224, 2), (key1224, -1), (key1175, -1)]

theorem rawRowCheck5600 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5600 := by decide +kernel

def row5600 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5600 : row5600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5600 := by decide +kernel

theorem rowEval5600 (x : Key → ℝ) : Integer.Sparse.eval row5600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5600, Integer.Sparse.eval_collectBalanced, rawRowCheck5600]

def rawRow5601 : Integer.Sparse Key := [(key986, -4), (key986, 2), (key988, 2), (key982, 2), (key986, 2), (key986, -4), (key1185, 2), (key1185, -1), (key1186, -1), (key1100, 2), (key1100, -1), (key1186, -1), (key1096, -1), (key1100, -1), (key1096, -1), (key1185, -1), (key1100, 2), (key1185, 2), (key1222, -1), (key1224, -1), (key1224, 2), (key1171, -1), (key1175, -1), (key1171, 2), (key1224, 2), (key1175, -1), (key1224, -1), (key1171, 2), (key1171, -1), (key1222, -1)]

theorem rawRowCheck5601 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5601 := by decide +kernel

def row5601 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5601 : row5601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5601 := by decide +kernel

theorem rowEval5601 (x : Key → ℝ) : Integer.Sparse.eval row5601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5601, Integer.Sparse.eval_collectBalanced, rawRowCheck5601]

def rawRow5602 : Integer.Sparse Key := [(key986, -4), (key988, 2), (key986, 2), (key986, 2), (key982, 2), (key986, -4), (key1185, 2), (key1186, -1), (key1185, -1), (key1100, 2), (key1186, -1), (key1100, -1), (key1100, -1), (key1096, -1), (key1185, -1), (key1096, -1), (key1185, 2), (key1100, 2), (key1224, -1), (key1222, -1), (key1224, 2), (key1175, -1), (key1171, -1), (key1224, 2), (key1171, 2), (key1224, -1), (key1175, -1), (key1171, 2), (key1222, -1), (key1171, -1)]

theorem rawRowCheck5602 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5602 := by decide +kernel

def row5602 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5602 : row5602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5602 := by decide +kernel

theorem rowEval5602 (x : Key → ℝ) : Integer.Sparse.eval row5602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5602, Integer.Sparse.eval_collectBalanced, rawRowCheck5602]

def rawRow5603 : Integer.Sparse Key := [(key988, -4), (key986, 2), (key986, 2), (key986, 2), (key986, 2), (key982, -4), (key1186, 2), (key1185, -1), (key1185, -1), (key1186, 2), (key1100, -1), (key1100, -1), (key1185, -1), (key1185, -1), (key1100, -1), (key1100, -1), (key1096, 2), (key1096, 2), (key1224, -1), (key1224, -1), (key1222, 2), (key1224, -1), (key1224, -1), (key1175, 2), (key1175, 2), (key1171, -1), (key1171, -1), (key1222, 2), (key1171, -1), (key1171, -1)]

theorem rawRowCheck5603 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5603 := by decide +kernel

def row5603 : Integer.Sparse Key := [(key982, -4), (key986, 8), (key988, -4), (key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

theorem rowCheck5603 : row5603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5603 := by decide +kernel

theorem rowEval5603 (x : Key → ℝ) : Integer.Sparse.eval row5603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5603, Integer.Sparse.eval_collectBalanced, rawRowCheck5603]

def rawRow5604 : Integer.Sparse Key := [(key1096, -4), (key1100, 2), (key1100, 2), (key1171, 2), (key1171, 2), (key1175, -4), (key982, 2), (key986, -1), (key986, -1), (key1096, 2), (key1185, -1), (key1185, -1), (key1171, -1), (key1171, -1), (key1222, -1), (key1222, -1), (key1224, 2), (key1224, 2), (key986, -1), (key986, -1), (key988, 2), (key1100, -1), (key1100, -1), (key1185, 2), (key1185, 2), (key1186, -1), (key1186, -1), (key1175, 2), (key1224, -1), (key1224, -1)]

theorem rawRowCheck5604 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5604 := by decide +kernel

def row5604 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5604 : row5604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5604 := by decide +kernel

theorem rowEval5604 (x : Key → ℝ) : Integer.Sparse.eval row5604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5604, Integer.Sparse.eval_collectBalanced, rawRowCheck5604]

def rawRow5605 : Integer.Sparse Key := [(key1100, -4), (key1096, 2), (key1100, 2), (key1171, 2), (key1175, 2), (key1171, -4), (key986, 2), (key982, -1), (key986, -1), (key1185, 2), (key1096, -1), (key1185, -1), (key1222, -1), (key1224, -1), (key1171, -1), (key1224, -1), (key1171, 2), (key1222, 2), (key986, -1), (key988, -1), (key986, 2), (key1185, -1), (key1186, -1), (key1100, 2), (key1186, 2), (key1100, -1), (key1185, -1), (key1224, 2), (key1175, -1), (key1224, -1)]

theorem rawRowCheck5605 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5605 := by decide +kernel

def row5605 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5605 : row5605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5605 := by decide +kernel

theorem rowEval5605 (x : Key → ℝ) : Integer.Sparse.eval row5605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5605, Integer.Sparse.eval_collectBalanced, rawRowCheck5605]

def rawRow5606 : Integer.Sparse Key := [(key1100, -4), (key1100, 2), (key1096, 2), (key1175, 2), (key1171, 2), (key1171, -4), (key986, 2), (key986, -1), (key982, -1), (key1185, 2), (key1185, -1), (key1096, -1), (key1224, -1), (key1222, -1), (key1224, -1), (key1171, -1), (key1222, 2), (key1171, 2), (key988, -1), (key986, -1), (key986, 2), (key1186, -1), (key1185, -1), (key1186, 2), (key1100, 2), (key1185, -1), (key1100, -1), (key1224, 2), (key1224, -1), (key1175, -1)]

theorem rawRowCheck5606 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5606 := by decide +kernel

def row5606 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5606 : row5606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5606 := by decide +kernel

theorem rowEval5606 (x : Key → ℝ) : Integer.Sparse.eval row5606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5606, Integer.Sparse.eval_collectBalanced, rawRowCheck5606]

def rawRow5607 : Integer.Sparse Key := [(key1096, -4), (key1171, 2), (key1171, 2), (key1100, 2), (key1100, 2), (key1175, -4), (key1096, 2), (key1171, -1), (key1171, -1), (key982, 2), (key1222, -1), (key1222, -1), (key986, -1), (key986, -1), (key1185, -1), (key1185, -1), (key1224, 2), (key1224, 2), (key1100, -1), (key1100, -1), (key1175, 2), (key986, -1), (key986, -1), (key1185, 2), (key1185, 2), (key1224, -1), (key1224, -1), (key988, 2), (key1186, -1), (key1186, -1)]

theorem rawRowCheck5607 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3 = rawRow5607 := by decide +kernel

def row5607 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5607 : row5607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5607 := by decide +kernel

theorem rowEval5607 (x : Key → ℝ) : Integer.Sparse.eval row5607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5607, Integer.Sparse.eval_collectBalanced, rawRowCheck5607]

def rawRow5608 : Integer.Sparse Key := [(key1171, -4), (key1096, 2), (key1171, 2), (key1100, 2), (key1175, 2), (key1100, -4), (key1171, 2), (key1096, -1), (key1171, -1), (key1222, 2), (key982, -1), (key1222, -1), (key1185, -1), (key1224, -1), (key986, -1), (key1224, -1), (key986, 2), (key1185, 2), (key1100, -1), (key1175, -1), (key1100, 2), (key1185, -1), (key1224, -1), (key986, 2), (key1224, 2), (key986, -1), (key1185, -1), (key1186, 2), (key988, -1), (key1186, -1)]

theorem rawRowCheck5608 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3 = rawRow5608 := by decide +kernel

def row5608 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5608 : row5608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5608 := by decide +kernel

theorem rowEval5608 (x : Key → ℝ) : Integer.Sparse.eval row5608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5608, Integer.Sparse.eval_collectBalanced, rawRowCheck5608]

def rawRow5609 : Integer.Sparse Key := [(key1171, -4), (key1171, 2), (key1096, 2), (key1175, 2), (key1100, 2), (key1100, -4), (key1171, 2), (key1171, -1), (key1096, -1), (key1222, 2), (key1222, -1), (key982, -1), (key1224, -1), (key1185, -1), (key1224, -1), (key986, -1), (key1185, 2), (key986, 2), (key1175, -1), (key1100, -1), (key1100, 2), (key1224, -1), (key1185, -1), (key1224, 2), (key986, 2), (key1185, -1), (key986, -1), (key1186, 2), (key1186, -1), (key988, -1)]

theorem rawRowCheck5609 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3 = rawRow5609 := by decide +kernel

def row5609 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5609 : row5609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5609 := by decide +kernel

theorem rowEval5609 (x : Key → ℝ) : Integer.Sparse.eval row5609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5609, Integer.Sparse.eval_collectBalanced, rawRowCheck5609]

def rawRow5610 : Integer.Sparse Key := [(key1100, -4), (key1171, 2), (key1175, 2), (key1096, 2), (key1100, 2), (key1171, -4), (key1185, 2), (key1222, -1), (key1224, -1), (key986, 2), (key1171, -1), (key1224, -1), (key982, -1), (key986, -1), (key1096, -1), (key1185, -1), (key1171, 2), (key1222, 2), (key1185, -1), (key1186, -1), (key1224, 2), (key986, -1), (key988, -1), (key1100, 2), (key1186, 2), (key1175, -1), (key1224, -1), (key986, 2), (key1100, -1), (key1185, -1)]

theorem rawRowCheck5610 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5610 := by decide +kernel

def row5610 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5610 : row5610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5610 := by decide +kernel

theorem rowEval5610 (x : Key → ℝ) : Integer.Sparse.eval row5610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5610, Integer.Sparse.eval_collectBalanced, rawRowCheck5610]

def rawRow5611 : Integer.Sparse Key := [(key1100, -4), (key1175, 2), (key1171, 2), (key1100, 2), (key1096, 2), (key1171, -4), (key1185, 2), (key1224, -1), (key1222, -1), (key986, 2), (key1224, -1), (key1171, -1), (key986, -1), (key982, -1), (key1185, -1), (key1096, -1), (key1222, 2), (key1171, 2), (key1186, -1), (key1185, -1), (key1224, 2), (key988, -1), (key986, -1), (key1186, 2), (key1100, 2), (key1224, -1), (key1175, -1), (key986, 2), (key1185, -1), (key1100, -1)]

theorem rawRowCheck5611 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5611 := by decide +kernel

def row5611 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5611 : row5611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5611 := by decide +kernel

theorem rowEval5611 (x : Key → ℝ) : Integer.Sparse.eval row5611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5611, Integer.Sparse.eval_collectBalanced, rawRowCheck5611]

def rawRow5612 : Integer.Sparse Key := [(key1171, -4), (key1100, 2), (key1175, 2), (key1096, 2), (key1171, 2), (key1100, -4), (key1222, 2), (key1185, -1), (key1224, -1), (key1171, 2), (key986, -1), (key1224, -1), (key1096, -1), (key1171, -1), (key982, -1), (key1222, -1), (key986, 2), (key1185, 2), (key1185, -1), (key1224, -1), (key1186, 2), (key1100, -1), (key1175, -1), (key986, 2), (key1224, 2), (key988, -1), (key1186, -1), (key1100, 2), (key986, -1), (key1185, -1)]

theorem rawRowCheck5612 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5612 := by decide +kernel

def row5612 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5612 : row5612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5612 := by decide +kernel

theorem rowEval5612 (x : Key → ℝ) : Integer.Sparse.eval row5612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5612, Integer.Sparse.eval_collectBalanced, rawRowCheck5612]

def rawRow5613 : Integer.Sparse Key := [(key1171, -4), (key1175, 2), (key1100, 2), (key1171, 2), (key1096, 2), (key1100, -4), (key1222, 2), (key1224, -1), (key1185, -1), (key1171, 2), (key1224, -1), (key986, -1), (key1171, -1), (key1096, -1), (key1222, -1), (key982, -1), (key1185, 2), (key986, 2), (key1224, -1), (key1185, -1), (key1186, 2), (key1175, -1), (key1100, -1), (key1224, 2), (key986, 2), (key1186, -1), (key988, -1), (key1100, 2), (key1185, -1), (key986, -1)]

theorem rawRowCheck5613 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5613 := by decide +kernel

def row5613 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5613 : row5613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5613 := by decide +kernel

theorem rowEval5613 (x : Key → ℝ) : Integer.Sparse.eval row5613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5613, Integer.Sparse.eval_collectBalanced, rawRowCheck5613]

def rawRow5614 : Integer.Sparse Key := [(key1175, -4), (key1100, 2), (key1171, 2), (key1100, 2), (key1171, 2), (key1096, -4), (key1224, 2), (key1185, -1), (key1222, -1), (key1224, 2), (key986, -1), (key1171, -1), (key1185, -1), (key1222, -1), (key986, -1), (key1171, -1), (key982, 2), (key1096, 2), (key1186, -1), (key1224, -1), (key1185, 2), (key1186, -1), (key1224, -1), (key988, 2), (key1175, 2), (key986, -1), (key1100, -1), (key1185, 2), (key986, -1), (key1100, -1)]

theorem rawRowCheck5614 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5614 := by decide +kernel

def row5614 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5614 : row5614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5614 := by decide +kernel

theorem rowEval5614 (x : Key → ℝ) : Integer.Sparse.eval row5614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5614, Integer.Sparse.eval_collectBalanced, rawRowCheck5614]

def rawRow5615 : Integer.Sparse Key := [(key1175, -4), (key1171, 2), (key1100, 2), (key1171, 2), (key1100, 2), (key1096, -4), (key1224, 2), (key1222, -1), (key1185, -1), (key1224, 2), (key1171, -1), (key986, -1), (key1222, -1), (key1185, -1), (key1171, -1), (key986, -1), (key1096, 2), (key982, 2), (key1224, -1), (key1186, -1), (key1185, 2), (key1224, -1), (key1186, -1), (key1175, 2), (key988, 2), (key1100, -1), (key986, -1), (key1185, 2), (key1100, -1), (key986, -1)]

theorem rawRowCheck5615 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5615 := by decide +kernel

def row5615 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5615 : row5615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5615 := by decide +kernel

theorem rowEval5615 (x : Key → ℝ) : Integer.Sparse.eval row5615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5615, Integer.Sparse.eval_collectBalanced, rawRowCheck5615]

def rawRow5616 : Integer.Sparse Key := [(key1185, -4), (key1185, 2), (key1186, 2), (key1222, 2), (key1224, 2), (key1224, -4), (key986, 2), (key986, -1), (key988, -1), (key1100, 2), (key1100, -1), (key1186, -1), (key1171, -1), (key1175, -1), (key1171, -1), (key1224, -1), (key1175, 2), (key1224, 2), (key982, -1), (key986, -1), (key986, 2), (key1096, -1), (key1100, -1), (key1096, 2), (key1185, 2), (key1100, -1), (key1185, -1), (key1171, 2), (key1171, -1), (key1222, -1)]

theorem rawRowCheck5616 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5616 := by decide +kernel

def row5616 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5616 : row5616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5616 := by decide +kernel

theorem rowEval5616 (x : Key → ℝ) : Integer.Sparse.eval row5616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5616, Integer.Sparse.eval_collectBalanced, rawRowCheck5616]

def rawRow5617 : Integer.Sparse Key := [(key1185, -4), (key1186, 2), (key1185, 2), (key1224, 2), (key1222, 2), (key1224, -4), (key986, 2), (key988, -1), (key986, -1), (key1100, 2), (key1186, -1), (key1100, -1), (key1175, -1), (key1171, -1), (key1224, -1), (key1171, -1), (key1224, 2), (key1175, 2), (key986, -1), (key982, -1), (key986, 2), (key1100, -1), (key1096, -1), (key1185, 2), (key1096, 2), (key1185, -1), (key1100, -1), (key1171, 2), (key1222, -1), (key1171, -1)]

theorem rawRowCheck5617 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5617 := by decide +kernel

def row5617 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5617 : row5617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5617 := by decide +kernel

theorem rowEval5617 (x : Key → ℝ) : Integer.Sparse.eval row5617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5617, Integer.Sparse.eval_collectBalanced, rawRowCheck5617]

def rawRow5618 : Integer.Sparse Key := [(key1186, -4), (key1185, 2), (key1185, 2), (key1224, 2), (key1224, 2), (key1222, -4), (key988, 2), (key986, -1), (key986, -1), (key1186, 2), (key1100, -1), (key1100, -1), (key1224, -1), (key1224, -1), (key1175, -1), (key1175, -1), (key1171, 2), (key1171, 2), (key986, -1), (key986, -1), (key982, 2), (key1185, -1), (key1185, -1), (key1100, 2), (key1100, 2), (key1096, -1), (key1096, -1), (key1222, 2), (key1171, -1), (key1171, -1)]

theorem rawRowCheck5618 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5618 := by decide +kernel

def row5618 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5618 : row5618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5618 := by decide +kernel

theorem rowEval5618 (x : Key → ℝ) : Integer.Sparse.eval row5618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5618, Integer.Sparse.eval_collectBalanced, rawRowCheck5618]

def rawRow5619 : Integer.Sparse Key := [(key1185, -4), (key1222, 2), (key1224, 2), (key1185, 2), (key1186, 2), (key1224, -4), (key1100, 2), (key1171, -1), (key1175, -1), (key986, 2), (key1171, -1), (key1224, -1), (key986, -1), (key988, -1), (key1100, -1), (key1186, -1), (key1175, 2), (key1224, 2), (key1096, -1), (key1100, -1), (key1171, 2), (key982, -1), (key986, -1), (key1096, 2), (key1185, 2), (key1171, -1), (key1222, -1), (key986, 2), (key1100, -1), (key1185, -1)]

theorem rawRowCheck5619 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5619 := by decide +kernel

def row5619 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5619 : row5619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5619 := by decide +kernel

theorem rowEval5619 (x : Key → ℝ) : Integer.Sparse.eval row5619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5619, Integer.Sparse.eval_collectBalanced, rawRowCheck5619]

def rawRow5620 : Integer.Sparse Key := [(key1185, -4), (key1224, 2), (key1222, 2), (key1186, 2), (key1185, 2), (key1224, -4), (key1100, 2), (key1175, -1), (key1171, -1), (key986, 2), (key1224, -1), (key1171, -1), (key988, -1), (key986, -1), (key1186, -1), (key1100, -1), (key1224, 2), (key1175, 2), (key1100, -1), (key1096, -1), (key1171, 2), (key986, -1), (key982, -1), (key1185, 2), (key1096, 2), (key1222, -1), (key1171, -1), (key986, 2), (key1185, -1), (key1100, -1)]

theorem rawRowCheck5620 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5620 := by decide +kernel

def row5620 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5620 : row5620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5620 := by decide +kernel

theorem rowEval5620 (x : Key → ℝ) : Integer.Sparse.eval row5620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5620, Integer.Sparse.eval_collectBalanced, rawRowCheck5620]

def rawRow5621 : Integer.Sparse Key := [(key1222, -4), (key1185, 2), (key1224, 2), (key1185, 2), (key1224, 2), (key1186, -4), (key1171, 2), (key1100, -1), (key1175, -1), (key1171, 2), (key986, -1), (key1224, -1), (key1100, -1), (key1175, -1), (key986, -1), (key1224, -1), (key988, 2), (key1186, 2), (key1096, -1), (key1171, -1), (key1100, 2), (key1096, -1), (key1171, -1), (key982, 2), (key1222, 2), (key986, -1), (key1185, -1), (key1100, 2), (key986, -1), (key1185, -1)]

theorem rawRowCheck5621 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5621 := by decide +kernel

def row5621 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5621 : row5621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5621 := by decide +kernel

theorem rowEval5621 (x : Key → ℝ) : Integer.Sparse.eval row5621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5621, Integer.Sparse.eval_collectBalanced, rawRowCheck5621]

def rawRow5622 : Integer.Sparse Key := [(key1222, -4), (key1224, 2), (key1185, 2), (key1224, 2), (key1185, 2), (key1186, -4), (key1171, 2), (key1175, -1), (key1100, -1), (key1171, 2), (key1224, -1), (key986, -1), (key1175, -1), (key1100, -1), (key1224, -1), (key986, -1), (key1186, 2), (key988, 2), (key1171, -1), (key1096, -1), (key1100, 2), (key1171, -1), (key1096, -1), (key1222, 2), (key982, 2), (key1185, -1), (key986, -1), (key1100, 2), (key1185, -1), (key986, -1)]

theorem rawRowCheck5622 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5622 := by decide +kernel

def row5622 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5622 : row5622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5622 := by decide +kernel

theorem rowEval5622 (x : Key → ℝ) : Integer.Sparse.eval row5622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5622, Integer.Sparse.eval_collectBalanced, rawRowCheck5622]

def rawRow5623 : Integer.Sparse Key := [(key1224, -4), (key1185, 2), (key1222, 2), (key1186, 2), (key1224, 2), (key1185, -4), (key1175, 2), (key1100, -1), (key1171, -1), (key1224, 2), (key986, -1), (key1171, -1), (key1186, -1), (key1224, -1), (key988, -1), (key1175, -1), (key986, 2), (key1100, 2), (key1100, -1), (key1171, -1), (key1096, 2), (key1185, -1), (key1222, -1), (key986, 2), (key1171, 2), (key982, -1), (key1096, -1), (key1185, 2), (key986, -1), (key1100, -1)]

theorem rawRowCheck5623 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5623 := by decide +kernel

def row5623 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5623 : row5623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5623 := by decide +kernel

theorem rowEval5623 (x : Key → ℝ) : Integer.Sparse.eval row5623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5623, Integer.Sparse.eval_collectBalanced, rawRowCheck5623]

def rawRow5624 : Integer.Sparse Key := [(key1224, -4), (key1222, 2), (key1185, 2), (key1224, 2), (key1186, 2), (key1185, -4), (key1175, 2), (key1171, -1), (key1100, -1), (key1224, 2), (key1171, -1), (key986, -1), (key1224, -1), (key1186, -1), (key1175, -1), (key988, -1), (key1100, 2), (key986, 2), (key1171, -1), (key1100, -1), (key1096, 2), (key1222, -1), (key1185, -1), (key1171, 2), (key986, 2), (key1096, -1), (key982, -1), (key1185, 2), (key1100, -1), (key986, -1)]

theorem rawRowCheck5624 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5624 := by decide +kernel

def row5624 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5624 : row5624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5624 := by decide +kernel

theorem rowEval5624 (x : Key → ℝ) : Integer.Sparse.eval row5624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5624, Integer.Sparse.eval_collectBalanced, rawRowCheck5624]

def rawRow5625 : Integer.Sparse Key := [(key1186, -4), (key1224, 2), (key1224, 2), (key1185, 2), (key1185, 2), (key1222, -4), (key1186, 2), (key1224, -1), (key1224, -1), (key988, 2), (key1175, -1), (key1175, -1), (key986, -1), (key986, -1), (key1100, -1), (key1100, -1), (key1171, 2), (key1171, 2), (key1185, -1), (key1185, -1), (key1222, 2), (key986, -1), (key986, -1), (key1100, 2), (key1100, 2), (key1171, -1), (key1171, -1), (key982, 2), (key1096, -1), (key1096, -1)]

theorem rawRowCheck5625 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3 = rawRow5625 := by decide +kernel

def row5625 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck5625 : row5625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5625 := by decide +kernel

theorem rowEval5625 (x : Key → ℝ) : Integer.Sparse.eval row5625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5625, Integer.Sparse.eval_collectBalanced, rawRowCheck5625]

def rawRow5626 : Integer.Sparse Key := [(key1224, -4), (key1186, 2), (key1224, 2), (key1185, 2), (key1222, 2), (key1185, -4), (key1224, 2), (key1186, -1), (key1224, -1), (key1175, 2), (key988, -1), (key1175, -1), (key1100, -1), (key1171, -1), (key986, -1), (key1171, -1), (key986, 2), (key1100, 2), (key1185, -1), (key1222, -1), (key1185, 2), (key1100, -1), (key1171, -1), (key986, 2), (key1171, 2), (key986, -1), (key1100, -1), (key1096, 2), (key982, -1), (key1096, -1)]

theorem rawRowCheck5626 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3 = rawRow5626 := by decide +kernel

def row5626 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5626 : row5626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5626 := by decide +kernel

theorem rowEval5626 (x : Key → ℝ) : Integer.Sparse.eval row5626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5626, Integer.Sparse.eval_collectBalanced, rawRowCheck5626]

def rawRow5627 : Integer.Sparse Key := [(key1224, -4), (key1224, 2), (key1186, 2), (key1222, 2), (key1185, 2), (key1185, -4), (key1224, 2), (key1224, -1), (key1186, -1), (key1175, 2), (key1175, -1), (key988, -1), (key1171, -1), (key1100, -1), (key1171, -1), (key986, -1), (key1100, 2), (key986, 2), (key1222, -1), (key1185, -1), (key1185, 2), (key1171, -1), (key1100, -1), (key1171, 2), (key986, 2), (key1100, -1), (key986, -1), (key1096, 2), (key1096, -1), (key982, -1)]

theorem rawRowCheck5627 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3 = rawRow5627 := by decide +kernel

def row5627 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

theorem rowCheck5627 : row5627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5627 := by decide +kernel

theorem rowEval5627 (x : Key → ℝ) : Integer.Sparse.eval row5627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5627, Integer.Sparse.eval_collectBalanced, rawRowCheck5627]

def rawRow5628 : Integer.Sparse Key := [(key2362, -4), (key2365, 2), (key2365, 2), (key2365, 2), (key2365, 2), (key2367, -4), (key2457, 2), (key2460, -1), (key2460, -1), (key2457, 2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, 2), (key2525, 2), (key2532, -1), (key2532, -1), (key2533, 2), (key2532, -1), (key2532, -1), (key2562, 2), (key2562, 2), (key2564, -1), (key2564, -1), (key2533, 2), (key2564, -1), (key2564, -1)]

theorem rawRowCheck5628 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form4 = rawRow5628 := by decide +kernel

def row5628 : Integer.Sparse Key := [(key2362, -4), (key2365, 8), (key2367, -4), (key2457, 4), (key2460, -4), (key2521, -4), (key2525, 4), (key2532, -4), (key2533, 4), (key2562, 4), (key2564, -4)]

theorem rowCheck5628 : row5628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5628 := by decide +kernel

theorem rowEval5628 (x : Key → ℝ) : Integer.Sparse.eval row5628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5628, Integer.Sparse.eval_collectBalanced, rawRowCheck5628]

def rawRow5629 : Integer.Sparse Key := [(key2365, -4), (key2362, 2), (key2365, 2), (key2365, 2), (key2367, 2), (key2365, -4), (key2460, 2), (key2457, -1), (key2460, -1), (key2521, 2), (key2457, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, 2), (key2521, 2), (key2532, -1), (key2533, -1), (key2532, 2), (key2562, -1), (key2564, -1), (key2532, 2), (key2564, 2), (key2532, -1), (key2562, -1), (key2564, 2), (key2533, -1), (key2564, -1)]

theorem rawRowCheck5629 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form4 = rawRow5629 := by decide +kernel

def row5629 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck5629 : row5629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5629 := by decide +kernel

theorem rowEval5629 (x : Key → ℝ) : Integer.Sparse.eval row5629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5629, Integer.Sparse.eval_collectBalanced, rawRowCheck5629]

def rawRow5630 : Integer.Sparse Key := [(key2365, -4), (key2365, 2), (key2362, 2), (key2367, 2), (key2365, 2), (key2365, -4), (key2460, 2), (key2460, -1), (key2457, -1), (key2521, 2), (key2521, -1), (key2457, -1), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, 2), (key2460, 2), (key2533, -1), (key2532, -1), (key2532, 2), (key2564, -1), (key2562, -1), (key2564, 2), (key2532, 2), (key2562, -1), (key2532, -1), (key2564, 2), (key2564, -1), (key2533, -1)]

theorem rawRowCheck5630 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form4 = rawRow5630 := by decide +kernel

def row5630 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck5630 : row5630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5630 := by decide +kernel

theorem rowEval5630 (x : Key → ℝ) : Integer.Sparse.eval row5630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5630, Integer.Sparse.eval_collectBalanced, rawRowCheck5630]

def rawRow5631 : Integer.Sparse Key := [(key2365, -4), (key2365, 2), (key2367, 2), (key2362, 2), (key2365, 2), (key2365, -4), (key2521, 2), (key2521, -1), (key2525, -1), (key2460, 2), (key2460, -1), (key2525, -1), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, 2), (key2521, 2), (key2562, -1), (key2564, -1), (key2564, 2), (key2532, -1), (key2533, -1), (key2532, 2), (key2564, 2), (key2533, -1), (key2564, -1), (key2532, 2), (key2532, -1), (key2562, -1)]

theorem rawRowCheck5631 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow5631 := by decide +kernel

def row5631 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck5631 : row5631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5631 := by decide +kernel

theorem rowEval5631 (x : Key → ℝ) : Integer.Sparse.eval row5631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5631, Integer.Sparse.eval_collectBalanced, rawRowCheck5631]

end MUB6.Certificate.GramRows

end OAI

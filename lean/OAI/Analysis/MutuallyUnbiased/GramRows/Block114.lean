import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
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

def rawRow11520 : Integer.Sparse Key := [(key1034, -6), (key1069, -6), (key1034, -6), (key1029, -6), (key1191, 2), (key1210, 2), (key1191, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1107, 2), (key994, 2), (key1107, 2)]

theorem rawRowCheck11520 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow11520 := by decide +kernel

def row11520 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11520 : row11520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11520 := by decide +kernel

theorem rowEval11520 (x : Key → ℝ) : Integer.Sparse.eval row11520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck11520, Integer.Sparse.eval_collectBalanced, rawRowCheck11520]

def rawRow11521 : Integer.Sparse Key := [(key1069, -6), (key1034, -6), (key1034, -6), (key1029, -6), (key1210, 2), (key1191, 2), (key1191, 2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1107, 2), (key1107, 2), (key994, 2)]

theorem rawRowCheck11521 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow11521 := by decide +kernel

def row11521 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

theorem rowCheck11521 : row11521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11521 := by decide +kernel

theorem rowEval11521 (x : Key → ℝ) : Integer.Sparse.eval row11521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck11521, Integer.Sparse.eval_collectBalanced, rawRowCheck11521]

def rawRow11522 : Integer.Sparse Key := [(key2607, -6), (key2800, -6), (key2800, -6), (key2823, -6), (key2623, 2), (key2623, 2), (key2634, 2), (key2697, 2), (key2697, 2), (key2720, 2), (key2850, 2), (key2854, 2), (key2850, 2), (key2864, 2), (key2854, 2), (key2864, 2)]

theorem rawRowCheck11522 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form3 = rawRow11522 := by decide +kernel

def row11522 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11522 : row11522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11522 := by decide +kernel

theorem rowEval11522 (x : Key → ℝ) : Integer.Sparse.eval row11522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11522, Integer.Sparse.eval_collectBalanced, rawRowCheck11522]

def rawRow11523 : Integer.Sparse Key := [(key2607, -6), (key2800, -6), (key2823, -6), (key2800, -6), (key2623, 2), (key2634, 2), (key2623, 2), (key2697, 2), (key2720, 2), (key2697, 2), (key2854, 2), (key2850, 2), (key2864, 2), (key2850, 2), (key2864, 2), (key2854, 2)]

theorem rawRowCheck11523 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form3 = rawRow11523 := by decide +kernel

def row11523 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11523 : row11523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11523 := by decide +kernel

theorem rowEval11523 (x : Key → ℝ) : Integer.Sparse.eval row11523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11523, Integer.Sparse.eval_collectBalanced, rawRowCheck11523]

def rawRow11524 : Integer.Sparse Key := [(key2607, -6), (key2823, -6), (key2800, -6), (key2800, -6), (key2634, 2), (key2623, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2697, 2), (key2864, 2), (key2864, 2), (key2854, 2), (key2854, 2), (key2850, 2), (key2850, 2)]

theorem rawRowCheck11524 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form3 = rawRow11524 := by decide +kernel

def row11524 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11524 : row11524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11524 := by decide +kernel

theorem rowEval11524 (x : Key → ℝ) : Integer.Sparse.eval row11524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11524, Integer.Sparse.eval_collectBalanced, rawRowCheck11524]

def rawRow11525 : Integer.Sparse Key := [(key2800, -6), (key2607, -6), (key2800, -6), (key2823, -6), (key2697, 2), (key2850, 2), (key2854, 2), (key2623, 2), (key2850, 2), (key2864, 2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

theorem rawRowCheck11525 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form3 = rawRow11525 := by decide +kernel

def row11525 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11525 : row11525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11525 := by decide +kernel

theorem rowEval11525 (x : Key → ℝ) : Integer.Sparse.eval row11525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11525, Integer.Sparse.eval_collectBalanced, rawRowCheck11525]

def rawRow11526 : Integer.Sparse Key := [(key2800, -6), (key2607, -6), (key2823, -6), (key2800, -6), (key2697, 2), (key2854, 2), (key2850, 2), (key2623, 2), (key2864, 2), (key2850, 2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

theorem rawRowCheck11526 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form3 = rawRow11526 := by decide +kernel

def row11526 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11526 : row11526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11526 := by decide +kernel

theorem rowEval11526 (x : Key → ℝ) : Integer.Sparse.eval row11526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11526, Integer.Sparse.eval_collectBalanced, rawRowCheck11526]

def rawRow11527 : Integer.Sparse Key := [(key2800, -6), (key2800, -6), (key2607, -6), (key2823, -6), (key2850, 2), (key2697, 2), (key2854, 2), (key2850, 2), (key2623, 2), (key2864, 2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

theorem rawRowCheck11527 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form3 = rawRow11527 := by decide +kernel

def row11527 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11527 : row11527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11527 := by decide +kernel

theorem rowEval11527 (x : Key → ℝ) : Integer.Sparse.eval row11527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck11527, Integer.Sparse.eval_collectBalanced, rawRowCheck11527]

def rawRow11528 : Integer.Sparse Key := [(key2800, -6), (key2800, -6), (key2823, -6), (key2607, -6), (key2850, 2), (key2854, 2), (key2697, 2), (key2850, 2), (key2864, 2), (key2623, 2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

theorem rawRowCheck11528 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form3 = rawRow11528 := by decide +kernel

def row11528 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11528 : row11528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11528 := by decide +kernel

theorem rowEval11528 (x : Key → ℝ) : Integer.Sparse.eval row11528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck11528, Integer.Sparse.eval_collectBalanced, rawRowCheck11528]

def rawRow11529 : Integer.Sparse Key := [(key2800, -6), (key2823, -6), (key2607, -6), (key2800, -6), (key2854, 2), (key2697, 2), (key2850, 2), (key2864, 2), (key2623, 2), (key2850, 2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck11529 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form3 = rawRow11529 := by decide +kernel

def row11529 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11529 : row11529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11529 := by decide +kernel

theorem rowEval11529 (x : Key → ℝ) : Integer.Sparse.eval row11529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11529, Integer.Sparse.eval_collectBalanced, rawRowCheck11529]

def rawRow11530 : Integer.Sparse Key := [(key2800, -6), (key2823, -6), (key2800, -6), (key2607, -6), (key2854, 2), (key2850, 2), (key2697, 2), (key2864, 2), (key2850, 2), (key2623, 2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck11530 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form3 = rawRow11530 := by decide +kernel

def row11530 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11530 : row11530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11530 := by decide +kernel

theorem rowEval11530 (x : Key → ℝ) : Integer.Sparse.eval row11530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck11530, Integer.Sparse.eval_collectBalanced, rawRowCheck11530]

def rawRow11531 : Integer.Sparse Key := [(key2823, -6), (key2607, -6), (key2800, -6), (key2800, -6), (key2720, 2), (key2864, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2854, 2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

theorem rawRowCheck11531 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow11531 := by decide +kernel

def row11531 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11531 : row11531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11531 := by decide +kernel

theorem rowEval11531 (x : Key → ℝ) : Integer.Sparse.eval row11531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11531, Integer.Sparse.eval_collectBalanced, rawRowCheck11531]

def rawRow11532 : Integer.Sparse Key := [(key2823, -6), (key2800, -6), (key2607, -6), (key2800, -6), (key2864, 2), (key2720, 2), (key2864, 2), (key2854, 2), (key2634, 2), (key2854, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

theorem rawRowCheck11532 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow11532 := by decide +kernel

def row11532 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11532 : row11532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11532 := by decide +kernel

theorem rowEval11532 (x : Key → ℝ) : Integer.Sparse.eval row11532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck11532, Integer.Sparse.eval_collectBalanced, rawRowCheck11532]

def rawRow11533 : Integer.Sparse Key := [(key2823, -6), (key2800, -6), (key2800, -6), (key2607, -6), (key2864, 2), (key2864, 2), (key2720, 2), (key2854, 2), (key2854, 2), (key2634, 2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

theorem rawRowCheck11533 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow11533 := by decide +kernel

def row11533 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

theorem rowCheck11533 : row11533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11533 := by decide +kernel

theorem rowEval11533 (x : Key → ℝ) : Integer.Sparse.eval row11533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck11533, Integer.Sparse.eval_collectBalanced, rawRowCheck11533]

def rawRow11534 : Integer.Sparse Key := [(key2399, -6), (key2403, -6), (key2403, -6), (key2434, -6), (key2371, 2), (key2375, 2), (key2375, 2), (key2465, 2), (key2469, 2), (key2465, 2), (key2536, 2), (key2469, 2), (key2536, 2), (key2500, 2), (key2500, 2), (key2552, 2)]

theorem rawRowCheck11534 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form4 = rawRow11534 := by decide +kernel

def row11534 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11534 : row11534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11534 := by decide +kernel

theorem rowEval11534 (x : Key → ℝ) : Integer.Sparse.eval row11534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11534, Integer.Sparse.eval_collectBalanced, rawRowCheck11534]

def rawRow11535 : Integer.Sparse Key := [(key2403, -6), (key2399, -6), (key2403, -6), (key2434, -6), (key2375, 2), (key2371, 2), (key2375, 2), (key2469, 2), (key2465, 2), (key2536, 2), (key2465, 2), (key2536, 2), (key2469, 2), (key2500, 2), (key2552, 2), (key2500, 2)]

theorem rawRowCheck11535 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form4 = rawRow11535 := by decide +kernel

def row11535 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11535 : row11535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11535 := by decide +kernel

theorem rowEval11535 (x : Key → ℝ) : Integer.Sparse.eval row11535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11535, Integer.Sparse.eval_collectBalanced, rawRowCheck11535]

def rawRow11536 : Integer.Sparse Key := [(key2403, -6), (key2403, -6), (key2399, -6), (key2434, -6), (key2375, 2), (key2375, 2), (key2371, 2), (key2536, 2), (key2536, 2), (key2469, 2), (key2469, 2), (key2465, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2500, 2)]

theorem rawRowCheck11536 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form4 = rawRow11536 := by decide +kernel

def row11536 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11536 : row11536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11536 := by decide +kernel

theorem rowEval11536 (x : Key → ℝ) : Integer.Sparse.eval row11536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11536, Integer.Sparse.eval_collectBalanced, rawRowCheck11536]

def rawRow11537 : Integer.Sparse Key := [(key2399, -6), (key2403, -6), (key2434, -6), (key2403, -6), (key2465, 2), (key2469, 2), (key2500, 2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2375, 2), (key2469, 2), (key2536, 2)]

theorem rawRowCheck11537 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form4 = rawRow11537 := by decide +kernel

def row11537 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11537 : row11537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11537 := by decide +kernel

theorem rowEval11537 (x : Key → ℝ) : Integer.Sparse.eval row11537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11537, Integer.Sparse.eval_collectBalanced, rawRowCheck11537]

def rawRow11538 : Integer.Sparse Key := [(key2403, -6), (key2399, -6), (key2434, -6), (key2403, -6), (key2469, 2), (key2465, 2), (key2500, 2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2375, 2), (key2536, 2), (key2469, 2)]

theorem rawRowCheck11538 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form4 = rawRow11538 := by decide +kernel

def row11538 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11538 : row11538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11538 := by decide +kernel

theorem rowEval11538 (x : Key → ℝ) : Integer.Sparse.eval row11538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11538, Integer.Sparse.eval_collectBalanced, rawRowCheck11538]

def rawRow11539 : Integer.Sparse Key := [(key2399, -6), (key2434, -6), (key2403, -6), (key2403, -6), (key2465, 2), (key2500, 2), (key2469, 2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2469, 2), (key2375, 2), (key2536, 2)]

theorem rawRowCheck11539 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form4 = rawRow11539 := by decide +kernel

def row11539 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11539 : row11539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11539 := by decide +kernel

theorem rowEval11539 (x : Key → ℝ) : Integer.Sparse.eval row11539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck11539, Integer.Sparse.eval_collectBalanced, rawRowCheck11539]

def rawRow11540 : Integer.Sparse Key := [(key2434, -6), (key2399, -6), (key2403, -6), (key2403, -6), (key2500, 2), (key2465, 2), (key2469, 2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2469, 2), (key2536, 2), (key2375, 2)]

theorem rawRowCheck11540 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form4 = rawRow11540 := by decide +kernel

def row11540 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11540 : row11540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11540 := by decide +kernel

theorem rowEval11540 (x : Key → ℝ) : Integer.Sparse.eval row11540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck11540, Integer.Sparse.eval_collectBalanced, rawRowCheck11540]

def rawRow11541 : Integer.Sparse Key := [(key2403, -6), (key2434, -6), (key2399, -6), (key2403, -6), (key2469, 2), (key2500, 2), (key2465, 2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2536, 2), (key2375, 2), (key2469, 2)]

theorem rawRowCheck11541 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form4 = rawRow11541 := by decide +kernel

def row11541 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11541 : row11541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11541 := by decide +kernel

theorem rowEval11541 (x : Key → ℝ) : Integer.Sparse.eval row11541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11541, Integer.Sparse.eval_collectBalanced, rawRowCheck11541]

def rawRow11542 : Integer.Sparse Key := [(key2434, -6), (key2403, -6), (key2399, -6), (key2403, -6), (key2500, 2), (key2469, 2), (key2465, 2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2536, 2), (key2469, 2), (key2375, 2)]

theorem rawRowCheck11542 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form4 = rawRow11542 := by decide +kernel

def row11542 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11542 : row11542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11542 := by decide +kernel

theorem rowEval11542 (x : Key → ℝ) : Integer.Sparse.eval row11542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck11542, Integer.Sparse.eval_collectBalanced, rawRowCheck11542]

def rawRow11543 : Integer.Sparse Key := [(key2403, -6), (key2403, -6), (key2434, -6), (key2399, -6), (key2536, 2), (key2536, 2), (key2552, 2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2465, 2)]

theorem rawRowCheck11543 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form4 = rawRow11543 := by decide +kernel

def row11543 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11543 : row11543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11543 := by decide +kernel

theorem rowEval11543 (x : Key → ℝ) : Integer.Sparse.eval row11543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11543, Integer.Sparse.eval_collectBalanced, rawRowCheck11543]

def rawRow11544 : Integer.Sparse Key := [(key2403, -6), (key2434, -6), (key2403, -6), (key2399, -6), (key2536, 2), (key2552, 2), (key2536, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2465, 2), (key2371, 2), (key2465, 2)]

theorem rawRowCheck11544 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form4 = rawRow11544 := by decide +kernel

def row11544 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11544 : row11544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11544 := by decide +kernel

theorem rowEval11544 (x : Key → ℝ) : Integer.Sparse.eval row11544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck11544, Integer.Sparse.eval_collectBalanced, rawRowCheck11544]

def rawRow11545 : Integer.Sparse Key := [(key2434, -6), (key2403, -6), (key2403, -6), (key2399, -6), (key2552, 2), (key2536, 2), (key2536, 2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2465, 2), (key2465, 2), (key2371, 2)]

theorem rawRowCheck11545 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form4 = rawRow11545 := by decide +kernel

def row11545 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

theorem rowCheck11545 : row11545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11545 := by decide +kernel

theorem rowEval11545 (x : Key → ℝ) : Integer.Sparse.eval row11545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck11545, Integer.Sparse.eval_collectBalanced, rawRowCheck11545]

def rawRow11546 : Integer.Sparse Key := [(key2609, -2), (key2613, -2), (key2613, -2), (key2802, -2), (key2806, -2), (key2802, -2), (key2949, -2), (key2806, -2), (key2949, -2), (key2826, -2), (key2826, -2), (key2959, -2), (key2625, 1), (key2629, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1), (key2852, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2973, 1), (key2867, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2982, 1)]

theorem rawRowCheck11546 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form5 = rawRow11546 := by decide +kernel

def row11546 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11546 : row11546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11546 := by decide +kernel

theorem rowEval11546 (x : Key → ℝ) : Integer.Sparse.eval row11546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11546, Integer.Sparse.eval_collectBalanced, rawRowCheck11546]

def rawRow11547 : Integer.Sparse Key := [(key2613, -2), (key2609, -2), (key2613, -2), (key2806, -2), (key2802, -2), (key2949, -2), (key2802, -2), (key2949, -2), (key2806, -2), (key2826, -2), (key2959, -2), (key2826, -2), (key2629, 1), (key2625, 1), (key2647, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2867, 1), (key2982, 1), (key2903, 1)]

theorem rawRowCheck11547 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form5 = rawRow11547 := by decide +kernel

def row11547 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11547 : row11547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11547 := by decide +kernel

theorem rowEval11547 (x : Key → ℝ) : Integer.Sparse.eval row11547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11547, Integer.Sparse.eval_collectBalanced, rawRowCheck11547]

def rawRow11548 : Integer.Sparse Key := [(key2613, -2), (key2613, -2), (key2609, -2), (key2949, -2), (key2949, -2), (key2806, -2), (key2806, -2), (key2802, -2), (key2802, -2), (key2959, -2), (key2826, -2), (key2826, -2), (key2647, 1), (key2647, 1), (key2629, 1), (key2629, 1), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1), (key2973, 1), (key2973, 1), (key2894, 1), (key2894, 1), (key2852, 1), (key2852, 1), (key2982, 1), (key2982, 1), (key2903, 1), (key2903, 1), (key2867, 1), (key2867, 1)]

theorem rawRowCheck11548 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form5 = rawRow11548 := by decide +kernel

def row11548 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11548 : row11548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11548 := by decide +kernel

theorem rowEval11548 (x : Key → ℝ) : Integer.Sparse.eval row11548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11548, Integer.Sparse.eval_collectBalanced, rawRowCheck11548]

def rawRow11549 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2826, -2), (key2609, -2), (key2613, -2), (key2802, -2), (key2949, -2), (key2826, -2), (key2959, -2), (key2613, -2), (key2806, -2), (key2949, -2), (key2779, 1), (key2783, 1), (key2852, 1), (key2894, 1), (key2867, 1), (key2903, 1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2629, 1), (key2647, 1), (key2783, 1), (key2937, 1), (key2894, 1), (key2973, 1)]

theorem rawRowCheck11549 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form5 = rawRow11549 := by decide +kernel

def row11549 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11549 : row11549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11549 := by decide +kernel

theorem rowEval11549 (x : Key → ℝ) : Integer.Sparse.eval row11549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11549, Integer.Sparse.eval_collectBalanced, rawRowCheck11549]

def rawRow11550 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2826, -2), (key2613, -2), (key2609, -2), (key2949, -2), (key2802, -2), (key2959, -2), (key2826, -2), (key2613, -2), (key2949, -2), (key2806, -2), (key2783, 1), (key2779, 1), (key2894, 1), (key2852, 1), (key2903, 1), (key2867, 1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2647, 1), (key2629, 1), (key2937, 1), (key2783, 1), (key2973, 1), (key2894, 1)]

theorem rawRowCheck11550 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form5 = rawRow11550 := by decide +kernel

def row11550 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11550 : row11550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11550 := by decide +kernel

theorem rowEval11550 (x : Key → ℝ) : Integer.Sparse.eval row11550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11550, Integer.Sparse.eval_collectBalanced, rawRowCheck11550]

def rawRow11551 : Integer.Sparse Key := [(key2802, -2), (key2826, -2), (key2806, -2), (key2802, -2), (key2826, -2), (key2609, -2), (key2959, -2), (key2613, -2), (key2949, -2), (key2806, -2), (key2613, -2), (key2949, -2), (key2852, 1), (key2867, 1), (key2779, 1), (key2903, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2937, 1)]

theorem rawRowCheck11551 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form5 = rawRow11551 := by decide +kernel

def row11551 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11551 : row11551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11551 := by decide +kernel

theorem rowEval11551 (x : Key → ℝ) : Integer.Sparse.eval row11551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck11551, Integer.Sparse.eval_collectBalanced, rawRowCheck11551]

def rawRow11552 : Integer.Sparse Key := [(key2826, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2802, -2), (key2959, -2), (key2609, -2), (key2949, -2), (key2613, -2), (key2806, -2), (key2949, -2), (key2613, -2), (key2867, 1), (key2852, 1), (key2903, 1), (key2779, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2937, 1), (key2647, 1)]

theorem rawRowCheck11552 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form5 = rawRow11552 := by decide +kernel

def row11552 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11552 : row11552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11552 := by decide +kernel

theorem rowEval11552 (x : Key → ℝ) : Integer.Sparse.eval row11552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck11552, Integer.Sparse.eval_collectBalanced, rawRowCheck11552]

def rawRow11553 : Integer.Sparse Key := [(key2806, -2), (key2826, -2), (key2802, -2), (key2949, -2), (key2959, -2), (key2613, -2), (key2826, -2), (key2609, -2), (key2802, -2), (key2949, -2), (key2613, -2), (key2806, -2), (key2894, 1), (key2903, 1), (key2783, 1), (key2867, 1), (key2779, 1), (key2852, 1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2937, 1), (key2973, 1), (key2647, 1), (key2894, 1), (key2629, 1), (key2783, 1)]

theorem rawRowCheck11553 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form5 = rawRow11553 := by decide +kernel

def row11553 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11553 : row11553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11553 := by decide +kernel

theorem rowEval11553 (x : Key → ℝ) : Integer.Sparse.eval row11553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11553, Integer.Sparse.eval_collectBalanced, rawRowCheck11553]

def rawRow11554 : Integer.Sparse Key := [(key2826, -2), (key2806, -2), (key2802, -2), (key2959, -2), (key2949, -2), (key2826, -2), (key2613, -2), (key2802, -2), (key2609, -2), (key2949, -2), (key2806, -2), (key2613, -2), (key2903, 1), (key2894, 1), (key2867, 1), (key2783, 1), (key2852, 1), (key2779, 1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2973, 1), (key2937, 1), (key2894, 1), (key2647, 1), (key2783, 1), (key2629, 1)]

theorem rawRowCheck11554 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form5 = rawRow11554 := by decide +kernel

def row11554 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11554 : row11554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11554 := by decide +kernel

theorem rowEval11554 (x : Key → ℝ) : Integer.Sparse.eval row11554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck11554, Integer.Sparse.eval_collectBalanced, rawRowCheck11554]

def rawRow11555 : Integer.Sparse Key := [(key2949, -2), (key2949, -2), (key2959, -2), (key2613, -2), (key2613, -2), (key2806, -2), (key2806, -2), (key2826, -2), (key2826, -2), (key2609, -2), (key2802, -2), (key2802, -2), (key2937, 1), (key2937, 1), (key2973, 1), (key2973, 1), (key2982, 1), (key2982, 1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2625, 1), (key2625, 1), (key2779, 1), (key2779, 1), (key2852, 1), (key2852, 1)]

theorem rawRowCheck11555 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form5 = rawRow11555 := by decide +kernel

def row11555 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11555 : row11555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11555 := by decide +kernel

theorem rowEval11555 (x : Key → ℝ) : Integer.Sparse.eval row11555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11555, Integer.Sparse.eval_collectBalanced, rawRowCheck11555]

def rawRow11556 : Integer.Sparse Key := [(key2949, -2), (key2959, -2), (key2949, -2), (key2806, -2), (key2826, -2), (key2613, -2), (key2826, -2), (key2613, -2), (key2806, -2), (key2802, -2), (key2609, -2), (key2802, -2), (key2973, 1), (key2982, 1), (key2937, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2852, 1), (key2625, 1), (key2779, 1)]

theorem rawRowCheck11556 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form5 = rawRow11556 := by decide +kernel

def row11556 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11556 : row11556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11556 := by decide +kernel

theorem rowEval11556 (x : Key → ℝ) : Integer.Sparse.eval row11556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck11556, Integer.Sparse.eval_collectBalanced, rawRowCheck11556]

def rawRow11557 : Integer.Sparse Key := [(key2959, -2), (key2949, -2), (key2949, -2), (key2826, -2), (key2806, -2), (key2826, -2), (key2613, -2), (key2806, -2), (key2613, -2), (key2802, -2), (key2802, -2), (key2609, -2), (key2982, 1), (key2973, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2937, 1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2852, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2625, 1)]

theorem rawRowCheck11557 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form5 = rawRow11557 := by decide +kernel

def row11557 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

theorem rowCheck11557 : row11557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11557 := by decide +kernel

theorem rowEval11557 (x : Key → ℝ) : Integer.Sparse.eval row11557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck11557, Integer.Sparse.eval_collectBalanced, rawRowCheck11557]

def rawRow11558 : Integer.Sparse Key := [(key2761, -24), (key2582, 6), (key2838, 6), (key2838, 6), (key2872, 6)]

theorem rawRowCheck11558 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form6 = rawRow11558 := by decide +kernel

def row11558 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11558 : row11558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11558 := by decide +kernel

theorem rowEval11558 (x : Key → ℝ) : Integer.Sparse.eval row11558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11558, Integer.Sparse.eval_collectBalanced, rawRowCheck11558]

def rawRow11559 : Integer.Sparse Key := [(key2761, -24), (key2582, 6), (key2838, 6), (key2872, 6), (key2838, 6)]

theorem rawRowCheck11559 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form6 = rawRow11559 := by decide +kernel

def row11559 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11559 : row11559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11559 := by decide +kernel

theorem rowEval11559 (x : Key → ℝ) : Integer.Sparse.eval row11559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11559, Integer.Sparse.eval_collectBalanced, rawRowCheck11559]

def rawRow11560 : Integer.Sparse Key := [(key2761, -24), (key2582, 6), (key2872, 6), (key2838, 6), (key2838, 6)]

theorem rawRowCheck11560 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form6 = rawRow11560 := by decide +kernel

def row11560 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11560 : row11560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11560 := by decide +kernel

theorem rowEval11560 (x : Key → ℝ) : Integer.Sparse.eval row11560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11560, Integer.Sparse.eval_collectBalanced, rawRowCheck11560]

def rawRow11561 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2582, 6), (key2838, 6), (key2872, 6)]

theorem rawRowCheck11561 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form6 = rawRow11561 := by decide +kernel

def row11561 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11561 : row11561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11561 := by decide +kernel

theorem rowEval11561 (x : Key → ℝ) : Integer.Sparse.eval row11561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11561, Integer.Sparse.eval_collectBalanced, rawRowCheck11561]

def rawRow11562 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2582, 6), (key2872, 6), (key2838, 6)]

theorem rawRowCheck11562 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form6 = rawRow11562 := by decide +kernel

def row11562 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11562 : row11562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11562 := by decide +kernel

theorem rowEval11562 (x : Key → ℝ) : Integer.Sparse.eval row11562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11562, Integer.Sparse.eval_collectBalanced, rawRowCheck11562]

def rawRow11563 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2838, 6), (key2582, 6), (key2872, 6)]

theorem rawRowCheck11563 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form6 = rawRow11563 := by decide +kernel

def row11563 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11563 : row11563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11563 := by decide +kernel

theorem rowEval11563 (x : Key → ℝ) : Integer.Sparse.eval row11563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck11563, Integer.Sparse.eval_collectBalanced, rawRowCheck11563]

def rawRow11564 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2838, 6), (key2872, 6), (key2582, 6)]

theorem rawRowCheck11564 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form6 = rawRow11564 := by decide +kernel

def row11564 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11564 : row11564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11564 := by decide +kernel

theorem rowEval11564 (x : Key → ℝ) : Integer.Sparse.eval row11564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck11564, Integer.Sparse.eval_collectBalanced, rawRowCheck11564]

def rawRow11565 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2872, 6), (key2582, 6), (key2838, 6)]

theorem rawRowCheck11565 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form6 = rawRow11565 := by decide +kernel

def row11565 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11565 : row11565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11565 := by decide +kernel

theorem rowEval11565 (x : Key → ℝ) : Integer.Sparse.eval row11565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11565, Integer.Sparse.eval_collectBalanced, rawRowCheck11565]

def rawRow11566 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2872, 6), (key2838, 6), (key2582, 6)]

theorem rawRowCheck11566 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form6 = rawRow11566 := by decide +kernel

def row11566 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11566 : row11566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11566 := by decide +kernel

theorem rowEval11566 (x : Key → ℝ) : Integer.Sparse.eval row11566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck11566, Integer.Sparse.eval_collectBalanced, rawRowCheck11566]

def rawRow11567 : Integer.Sparse Key := [(key2761, -24), (key2872, 6), (key2582, 6), (key2838, 6), (key2838, 6)]

theorem rawRowCheck11567 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form6 = rawRow11567 := by decide +kernel

def row11567 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11567 : row11567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11567 := by decide +kernel

theorem rowEval11567 (x : Key → ℝ) : Integer.Sparse.eval row11567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11567, Integer.Sparse.eval_collectBalanced, rawRowCheck11567]

def rawRow11568 : Integer.Sparse Key := [(key2761, -24), (key2872, 6), (key2838, 6), (key2582, 6), (key2838, 6)]

theorem rawRowCheck11568 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form6 = rawRow11568 := by decide +kernel

def row11568 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11568 : row11568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11568 := by decide +kernel

theorem rowEval11568 (x : Key → ℝ) : Integer.Sparse.eval row11568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck11568, Integer.Sparse.eval_collectBalanced, rawRowCheck11568]

def rawRow11569 : Integer.Sparse Key := [(key2761, -24), (key2872, 6), (key2838, 6), (key2838, 6), (key2582, 6)]

theorem rawRowCheck11569 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form6 = rawRow11569 := by decide +kernel

def row11569 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

theorem rowCheck11569 : row11569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11569 := by decide +kernel

theorem rowEval11569 (x : Key → ℝ) : Integer.Sparse.eval row11569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck11569, Integer.Sparse.eval_collectBalanced, rawRowCheck11569]

def rawRow11570 : Integer.Sparse Key := [(key2664, -2), (key2668, -2), (key2668, -2), (key2699, -2), (key2703, -2), (key2699, -2), (key2736, -2), (key2703, -2), (key2736, -2), (key2723, -2), (key2723, -2), (key2746, -2), (key2609, 2), (key2613, 2), (key2613, 2), (key2802, 2), (key2806, 2), (key2802, 2), (key2949, 2), (key2806, 2), (key2949, 2), (key2826, 2), (key2826, 2), (key2959, 2)]

theorem rawRowCheck11570 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form7 = rawRow11570 := by decide +kernel

def row11570 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11570 : row11570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11570 := by decide +kernel

theorem rowEval11570 (x : Key → ℝ) : Integer.Sparse.eval row11570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11570, Integer.Sparse.eval_collectBalanced, rawRowCheck11570]

def rawRow11571 : Integer.Sparse Key := [(key2668, -2), (key2664, -2), (key2668, -2), (key2703, -2), (key2699, -2), (key2736, -2), (key2699, -2), (key2736, -2), (key2703, -2), (key2723, -2), (key2746, -2), (key2723, -2), (key2613, 2), (key2609, 2), (key2613, 2), (key2806, 2), (key2802, 2), (key2949, 2), (key2802, 2), (key2949, 2), (key2806, 2), (key2826, 2), (key2959, 2), (key2826, 2)]

theorem rawRowCheck11571 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form7 = rawRow11571 := by decide +kernel

def row11571 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11571 : row11571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11571 := by decide +kernel

theorem rowEval11571 (x : Key → ℝ) : Integer.Sparse.eval row11571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11571, Integer.Sparse.eval_collectBalanced, rawRowCheck11571]

def rawRow11572 : Integer.Sparse Key := [(key2668, -2), (key2668, -2), (key2664, -2), (key2736, -2), (key2736, -2), (key2703, -2), (key2703, -2), (key2699, -2), (key2699, -2), (key2746, -2), (key2723, -2), (key2723, -2), (key2613, 2), (key2613, 2), (key2609, 2), (key2949, 2), (key2949, 2), (key2806, 2), (key2806, 2), (key2802, 2), (key2802, 2), (key2959, 2), (key2826, 2), (key2826, 2)]

theorem rawRowCheck11572 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form7 = rawRow11572 := by decide +kernel

def row11572 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11572 : row11572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11572 := by decide +kernel

theorem rowEval11572 (x : Key → ℝ) : Integer.Sparse.eval row11572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11572, Integer.Sparse.eval_collectBalanced, rawRowCheck11572]

def rawRow11573 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2664, -2), (key2668, -2), (key2699, -2), (key2736, -2), (key2723, -2), (key2746, -2), (key2668, -2), (key2703, -2), (key2736, -2), (key2802, 2), (key2806, 2), (key2826, 2), (key2609, 2), (key2613, 2), (key2802, 2), (key2949, 2), (key2826, 2), (key2959, 2), (key2613, 2), (key2806, 2), (key2949, 2)]

theorem rawRowCheck11573 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form7 = rawRow11573 := by decide +kernel

def row11573 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11573 : row11573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11573 := by decide +kernel

theorem rowEval11573 (x : Key → ℝ) : Integer.Sparse.eval row11573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11573, Integer.Sparse.eval_collectBalanced, rawRowCheck11573]

def rawRow11574 : Integer.Sparse Key := [(key2703, -2), (key2699, -2), (key2723, -2), (key2668, -2), (key2664, -2), (key2736, -2), (key2699, -2), (key2746, -2), (key2723, -2), (key2668, -2), (key2736, -2), (key2703, -2), (key2806, 2), (key2802, 2), (key2826, 2), (key2613, 2), (key2609, 2), (key2949, 2), (key2802, 2), (key2959, 2), (key2826, 2), (key2613, 2), (key2949, 2), (key2806, 2)]

theorem rawRowCheck11574 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form7 = rawRow11574 := by decide +kernel

def row11574 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11574 : row11574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11574 := by decide +kernel

theorem rowEval11574 (x : Key → ℝ) : Integer.Sparse.eval row11574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11574, Integer.Sparse.eval_collectBalanced, rawRowCheck11574]

def rawRow11575 : Integer.Sparse Key := [(key2699, -2), (key2723, -2), (key2703, -2), (key2699, -2), (key2723, -2), (key2664, -2), (key2746, -2), (key2668, -2), (key2736, -2), (key2703, -2), (key2668, -2), (key2736, -2), (key2802, 2), (key2826, 2), (key2806, 2), (key2802, 2), (key2826, 2), (key2609, 2), (key2959, 2), (key2613, 2), (key2949, 2), (key2806, 2), (key2613, 2), (key2949, 2)]

theorem rawRowCheck11575 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form7 = rawRow11575 := by decide +kernel

def row11575 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11575 : row11575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11575 := by decide +kernel

theorem rowEval11575 (x : Key → ℝ) : Integer.Sparse.eval row11575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck11575, Integer.Sparse.eval_collectBalanced, rawRowCheck11575]

def rawRow11576 : Integer.Sparse Key := [(key2723, -2), (key2699, -2), (key2703, -2), (key2723, -2), (key2699, -2), (key2746, -2), (key2664, -2), (key2736, -2), (key2668, -2), (key2703, -2), (key2736, -2), (key2668, -2), (key2826, 2), (key2802, 2), (key2806, 2), (key2826, 2), (key2802, 2), (key2959, 2), (key2609, 2), (key2949, 2), (key2613, 2), (key2806, 2), (key2949, 2), (key2613, 2)]

theorem rawRowCheck11576 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form7 = rawRow11576 := by decide +kernel

def row11576 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11576 : row11576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11576 := by decide +kernel

theorem rowEval11576 (x : Key → ℝ) : Integer.Sparse.eval row11576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck11576, Integer.Sparse.eval_collectBalanced, rawRowCheck11576]

def rawRow11577 : Integer.Sparse Key := [(key2703, -2), (key2723, -2), (key2699, -2), (key2736, -2), (key2746, -2), (key2668, -2), (key2723, -2), (key2664, -2), (key2699, -2), (key2736, -2), (key2668, -2), (key2703, -2), (key2806, 2), (key2826, 2), (key2802, 2), (key2949, 2), (key2959, 2), (key2613, 2), (key2826, 2), (key2609, 2), (key2802, 2), (key2949, 2), (key2613, 2), (key2806, 2)]

theorem rawRowCheck11577 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form7 = rawRow11577 := by decide +kernel

def row11577 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11577 : row11577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11577 := by decide +kernel

theorem rowEval11577 (x : Key → ℝ) : Integer.Sparse.eval row11577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11577, Integer.Sparse.eval_collectBalanced, rawRowCheck11577]

def rawRow11578 : Integer.Sparse Key := [(key2723, -2), (key2703, -2), (key2699, -2), (key2746, -2), (key2736, -2), (key2723, -2), (key2668, -2), (key2699, -2), (key2664, -2), (key2736, -2), (key2703, -2), (key2668, -2), (key2826, 2), (key2806, 2), (key2802, 2), (key2959, 2), (key2949, 2), (key2826, 2), (key2613, 2), (key2802, 2), (key2609, 2), (key2949, 2), (key2806, 2), (key2613, 2)]

theorem rawRowCheck11578 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form7 = rawRow11578 := by decide +kernel

def row11578 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11578 : row11578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11578 := by decide +kernel

theorem rowEval11578 (x : Key → ℝ) : Integer.Sparse.eval row11578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck11578, Integer.Sparse.eval_collectBalanced, rawRowCheck11578]

def rawRow11579 : Integer.Sparse Key := [(key2736, -2), (key2736, -2), (key2746, -2), (key2668, -2), (key2668, -2), (key2703, -2), (key2703, -2), (key2723, -2), (key2723, -2), (key2664, -2), (key2699, -2), (key2699, -2), (key2949, 2), (key2949, 2), (key2959, 2), (key2613, 2), (key2613, 2), (key2806, 2), (key2806, 2), (key2826, 2), (key2826, 2), (key2609, 2), (key2802, 2), (key2802, 2)]

theorem rawRowCheck11579 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form7 = rawRow11579 := by decide +kernel

def row11579 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11579 : row11579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11579 := by decide +kernel

theorem rowEval11579 (x : Key → ℝ) : Integer.Sparse.eval row11579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11579, Integer.Sparse.eval_collectBalanced, rawRowCheck11579]

def rawRow11580 : Integer.Sparse Key := [(key2736, -2), (key2746, -2), (key2736, -2), (key2703, -2), (key2723, -2), (key2668, -2), (key2723, -2), (key2668, -2), (key2703, -2), (key2699, -2), (key2664, -2), (key2699, -2), (key2949, 2), (key2959, 2), (key2949, 2), (key2806, 2), (key2826, 2), (key2613, 2), (key2826, 2), (key2613, 2), (key2806, 2), (key2802, 2), (key2609, 2), (key2802, 2)]

theorem rawRowCheck11580 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form7 = rawRow11580 := by decide +kernel

def row11580 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11580 : row11580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11580 := by decide +kernel

theorem rowEval11580 (x : Key → ℝ) : Integer.Sparse.eval row11580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck11580, Integer.Sparse.eval_collectBalanced, rawRowCheck11580]

def rawRow11581 : Integer.Sparse Key := [(key2746, -2), (key2736, -2), (key2736, -2), (key2723, -2), (key2703, -2), (key2723, -2), (key2668, -2), (key2703, -2), (key2668, -2), (key2699, -2), (key2699, -2), (key2664, -2), (key2959, 2), (key2949, 2), (key2949, 2), (key2826, 2), (key2806, 2), (key2826, 2), (key2613, 2), (key2806, 2), (key2613, 2), (key2802, 2), (key2802, 2), (key2609, 2)]

theorem rawRowCheck11581 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form7 = rawRow11581 := by decide +kernel

def row11581 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

theorem rowCheck11581 : row11581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11581 := by decide +kernel

theorem rowEval11581 (x : Key → ℝ) : Integer.Sparse.eval row11581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck11581, Integer.Sparse.eval_collectBalanced, rawRowCheck11581]

def rawRow11582 : Integer.Sparse Key := [(key1292, -2), (key1297, -2), (key1297, -2), (key1569, -2), (key1574, -2), (key1569, -2), (key1789, -2), (key1574, -2), (key1789, -2), (key1592, -2), (key1592, -2), (key1797, -2), (key1312, 1), (key1317, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1338, 1), (key1542, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1773, 1), (key1618, 1), (key1656, 1), (key1618, 1), (key1814, 1), (key1656, 1), (key1814, 1), (key1632, 1), (key1666, 1), (key1632, 1), (key1824, 1), (key1666, 1), (key1824, 1)]

theorem rawRowCheck11582 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form8 = rawRow11582 := by decide +kernel

def row11582 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11582 : row11582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11582 := by decide +kernel

theorem rowEval11582 (x : Key → ℝ) : Integer.Sparse.eval row11582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11582, Integer.Sparse.eval_collectBalanced, rawRowCheck11582]

def rawRow11583 : Integer.Sparse Key := [(key1297, -2), (key1292, -2), (key1297, -2), (key1574, -2), (key1569, -2), (key1789, -2), (key1569, -2), (key1789, -2), (key1574, -2), (key1592, -2), (key1797, -2), (key1592, -2), (key1317, 1), (key1312, 1), (key1338, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1656, 1), (key1618, 1), (key1814, 1), (key1618, 1), (key1814, 1), (key1656, 1), (key1666, 1), (key1632, 1), (key1824, 1), (key1632, 1), (key1824, 1), (key1666, 1)]

theorem rawRowCheck11583 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form8 = rawRow11583 := by decide +kernel

def row11583 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11583 : row11583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11583 := by decide +kernel

theorem rowEval11583 (x : Key → ℝ) : Integer.Sparse.eval row11583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11583, Integer.Sparse.eval_collectBalanced, rawRowCheck11583]

def rawRow11584 : Integer.Sparse Key := [(key1297, -2), (key1297, -2), (key1292, -2), (key1789, -2), (key1789, -2), (key1574, -2), (key1574, -2), (key1569, -2), (key1569, -2), (key1797, -2), (key1592, -2), (key1592, -2), (key1338, 1), (key1338, 1), (key1317, 1), (key1317, 1), (key1312, 1), (key1312, 1), (key1773, 1), (key1773, 1), (key1547, 1), (key1547, 1), (key1542, 1), (key1542, 1), (key1814, 1), (key1814, 1), (key1656, 1), (key1656, 1), (key1618, 1), (key1618, 1), (key1824, 1), (key1824, 1), (key1666, 1), (key1666, 1), (key1632, 1), (key1632, 1)]

theorem rawRowCheck11584 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form8 = rawRow11584 := by decide +kernel

def row11584 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11584 : row11584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11584 := by decide +kernel

theorem rowEval11584 (x : Key → ℝ) : Integer.Sparse.eval row11584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11584, Integer.Sparse.eval_collectBalanced, rawRowCheck11584]

def rawRow11585 : Integer.Sparse Key := [(key1569, -2), (key1574, -2), (key1592, -2), (key1292, -2), (key1297, -2), (key1569, -2), (key1789, -2), (key1592, -2), (key1797, -2), (key1297, -2), (key1574, -2), (key1789, -2), (key1542, 1), (key1547, 1), (key1618, 1), (key1656, 1), (key1632, 1), (key1666, 1), (key1312, 1), (key1317, 1), (key1618, 1), (key1814, 1), (key1632, 1), (key1824, 1), (key1312, 1), (key1338, 1), (key1542, 1), (key1773, 1), (key1666, 1), (key1824, 1), (key1317, 1), (key1338, 1), (key1547, 1), (key1773, 1), (key1656, 1), (key1814, 1)]

theorem rawRowCheck11585 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form8 = rawRow11585 := by decide +kernel

def row11585 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11585 : row11585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11585 := by decide +kernel

theorem rowEval11585 (x : Key → ℝ) : Integer.Sparse.eval row11585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11585, Integer.Sparse.eval_collectBalanced, rawRowCheck11585]

def rawRow11586 : Integer.Sparse Key := [(key1574, -2), (key1569, -2), (key1592, -2), (key1297, -2), (key1292, -2), (key1789, -2), (key1569, -2), (key1797, -2), (key1592, -2), (key1297, -2), (key1789, -2), (key1574, -2), (key1547, 1), (key1542, 1), (key1656, 1), (key1618, 1), (key1666, 1), (key1632, 1), (key1317, 1), (key1312, 1), (key1814, 1), (key1618, 1), (key1824, 1), (key1632, 1), (key1338, 1), (key1312, 1), (key1773, 1), (key1542, 1), (key1824, 1), (key1666, 1), (key1338, 1), (key1317, 1), (key1773, 1), (key1547, 1), (key1814, 1), (key1656, 1)]

theorem rawRowCheck11586 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form8 = rawRow11586 := by decide +kernel

def row11586 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11586 : row11586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11586 := by decide +kernel

theorem rowEval11586 (x : Key → ℝ) : Integer.Sparse.eval row11586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11586, Integer.Sparse.eval_collectBalanced, rawRowCheck11586]

def rawRow11587 : Integer.Sparse Key := [(key1569, -2), (key1592, -2), (key1574, -2), (key1569, -2), (key1592, -2), (key1292, -2), (key1797, -2), (key1297, -2), (key1789, -2), (key1574, -2), (key1297, -2), (key1789, -2), (key1618, 1), (key1632, 1), (key1542, 1), (key1666, 1), (key1547, 1), (key1656, 1), (key1618, 1), (key1632, 1), (key1312, 1), (key1824, 1), (key1317, 1), (key1814, 1), (key1542, 1), (key1666, 1), (key1312, 1), (key1824, 1), (key1338, 1), (key1773, 1), (key1547, 1), (key1656, 1), (key1317, 1), (key1814, 1), (key1338, 1), (key1773, 1)]

theorem rawRowCheck11587 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form8 = rawRow11587 := by decide +kernel

def row11587 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11587 : row11587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11587 := by decide +kernel

theorem rowEval11587 (x : Key → ℝ) : Integer.Sparse.eval row11587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11587, Integer.Sparse.eval_collectBalanced, rawRowCheck11587]

def rawRow11588 : Integer.Sparse Key := [(key1592, -2), (key1569, -2), (key1574, -2), (key1592, -2), (key1569, -2), (key1797, -2), (key1292, -2), (key1789, -2), (key1297, -2), (key1574, -2), (key1789, -2), (key1297, -2), (key1632, 1), (key1618, 1), (key1666, 1), (key1542, 1), (key1656, 1), (key1547, 1), (key1632, 1), (key1618, 1), (key1824, 1), (key1312, 1), (key1814, 1), (key1317, 1), (key1666, 1), (key1542, 1), (key1824, 1), (key1312, 1), (key1773, 1), (key1338, 1), (key1656, 1), (key1547, 1), (key1814, 1), (key1317, 1), (key1773, 1), (key1338, 1)]

theorem rawRowCheck11588 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form8 = rawRow11588 := by decide +kernel

def row11588 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11588 : row11588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11588 := by decide +kernel

theorem rowEval11588 (x : Key → ℝ) : Integer.Sparse.eval row11588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck11588, Integer.Sparse.eval_collectBalanced, rawRowCheck11588]

def rawRow11589 : Integer.Sparse Key := [(key1574, -2), (key1592, -2), (key1569, -2), (key1789, -2), (key1797, -2), (key1297, -2), (key1592, -2), (key1292, -2), (key1569, -2), (key1789, -2), (key1297, -2), (key1574, -2), (key1656, 1), (key1666, 1), (key1547, 1), (key1632, 1), (key1542, 1), (key1618, 1), (key1814, 1), (key1824, 1), (key1317, 1), (key1632, 1), (key1312, 1), (key1618, 1), (key1773, 1), (key1824, 1), (key1338, 1), (key1666, 1), (key1312, 1), (key1542, 1), (key1773, 1), (key1814, 1), (key1338, 1), (key1656, 1), (key1317, 1), (key1547, 1)]

theorem rawRowCheck11589 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form8 = rawRow11589 := by decide +kernel

def row11589 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11589 : row11589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11589 := by decide +kernel

theorem rowEval11589 (x : Key → ℝ) : Integer.Sparse.eval row11589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11589, Integer.Sparse.eval_collectBalanced, rawRowCheck11589]

def rawRow11590 : Integer.Sparse Key := [(key1592, -2), (key1574, -2), (key1569, -2), (key1797, -2), (key1789, -2), (key1592, -2), (key1297, -2), (key1569, -2), (key1292, -2), (key1789, -2), (key1574, -2), (key1297, -2), (key1666, 1), (key1656, 1), (key1632, 1), (key1547, 1), (key1618, 1), (key1542, 1), (key1824, 1), (key1814, 1), (key1632, 1), (key1317, 1), (key1618, 1), (key1312, 1), (key1824, 1), (key1773, 1), (key1666, 1), (key1338, 1), (key1542, 1), (key1312, 1), (key1814, 1), (key1773, 1), (key1656, 1), (key1338, 1), (key1547, 1), (key1317, 1)]

theorem rawRowCheck11590 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form8 = rawRow11590 := by decide +kernel

def row11590 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11590 : row11590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11590 := by decide +kernel

theorem rowEval11590 (x : Key → ℝ) : Integer.Sparse.eval row11590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck11590, Integer.Sparse.eval_collectBalanced, rawRowCheck11590]

def rawRow11591 : Integer.Sparse Key := [(key1789, -2), (key1789, -2), (key1797, -2), (key1297, -2), (key1297, -2), (key1574, -2), (key1574, -2), (key1592, -2), (key1592, -2), (key1292, -2), (key1569, -2), (key1569, -2), (key1773, 1), (key1773, 1), (key1814, 1), (key1814, 1), (key1824, 1), (key1824, 1), (key1338, 1), (key1338, 1), (key1656, 1), (key1656, 1), (key1666, 1), (key1666, 1), (key1317, 1), (key1317, 1), (key1547, 1), (key1547, 1), (key1632, 1), (key1632, 1), (key1312, 1), (key1312, 1), (key1542, 1), (key1542, 1), (key1618, 1), (key1618, 1)]

theorem rawRowCheck11591 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form8 = rawRow11591 := by decide +kernel

def row11591 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11591 : row11591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11591 := by decide +kernel

theorem rowEval11591 (x : Key → ℝ) : Integer.Sparse.eval row11591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11591, Integer.Sparse.eval_collectBalanced, rawRowCheck11591]

def rawRow11592 : Integer.Sparse Key := [(key1789, -2), (key1797, -2), (key1789, -2), (key1574, -2), (key1592, -2), (key1297, -2), (key1592, -2), (key1297, -2), (key1574, -2), (key1569, -2), (key1292, -2), (key1569, -2), (key1814, 1), (key1824, 1), (key1773, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1542, 1), (key1618, 1), (key1312, 1), (key1618, 1), (key1312, 1), (key1542, 1)]

theorem rawRowCheck11592 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form8 = rawRow11592 := by decide +kernel

def row11592 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11592 : row11592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11592 := by decide +kernel

theorem rowEval11592 (x : Key → ℝ) : Integer.Sparse.eval row11592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11592, Integer.Sparse.eval_collectBalanced, rawRowCheck11592]

def rawRow11593 : Integer.Sparse Key := [(key1797, -2), (key1789, -2), (key1789, -2), (key1592, -2), (key1574, -2), (key1592, -2), (key1297, -2), (key1574, -2), (key1297, -2), (key1569, -2), (key1569, -2), (key1292, -2), (key1824, 1), (key1814, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1773, 1), (key1666, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1338, 1), (key1632, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1317, 1), (key1618, 1), (key1542, 1), (key1618, 1), (key1312, 1), (key1542, 1), (key1312, 1)]

theorem rawRowCheck11593 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form8 = rawRow11593 := by decide +kernel

def row11593 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

theorem rowCheck11593 : row11593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11593 := by decide +kernel

theorem rowEval11593 (x : Key → ℝ) : Integer.Sparse.eval row11593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck11593, Integer.Sparse.eval_collectBalanced, rawRowCheck11593]

def rawRow11594 : Integer.Sparse Key := [(key2625, 1), (key2629, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1), (key2852, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2973, 1), (key2867, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2982, 1), (key2637, -2), (key2637, -2), (key2652, -2), (key2791, -2), (key2791, -2), (key2942, -2), (key2857, -2), (key2896, -2), (key2857, -2), (key2975, -2), (key2896, -2), (key2975, -2)]

theorem rawRowCheck11594 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form9 = rawRow11594 := by decide +kernel

def row11594 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11594 : row11594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11594 := by decide +kernel

theorem rowEval11594 (x : Key → ℝ) : Integer.Sparse.eval row11594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11594, Integer.Sparse.eval_collectBalanced, rawRowCheck11594]

def rawRow11595 : Integer.Sparse Key := [(key2629, 1), (key2625, 1), (key2647, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2637, -2), (key2652, -2), (key2637, -2), (key2791, -2), (key2942, -2), (key2791, -2), (key2896, -2), (key2857, -2), (key2975, -2), (key2857, -2), (key2975, -2), (key2896, -2)]

theorem rawRowCheck11595 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form9 = rawRow11595 := by decide +kernel

def row11595 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11595 : row11595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11595 := by decide +kernel

theorem rowEval11595 (x : Key → ℝ) : Integer.Sparse.eval row11595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11595, Integer.Sparse.eval_collectBalanced, rawRowCheck11595]

def rawRow11596 : Integer.Sparse Key := [(key2647, 1), (key2647, 1), (key2629, 1), (key2629, 1), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1), (key2973, 1), (key2973, 1), (key2894, 1), (key2894, 1), (key2852, 1), (key2852, 1), (key2982, 1), (key2982, 1), (key2903, 1), (key2903, 1), (key2867, 1), (key2867, 1), (key2652, -2), (key2637, -2), (key2637, -2), (key2942, -2), (key2791, -2), (key2791, -2), (key2975, -2), (key2975, -2), (key2896, -2), (key2896, -2), (key2857, -2), (key2857, -2)]

theorem rawRowCheck11596 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form9 = rawRow11596 := by decide +kernel

def row11596 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11596 : row11596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11596 := by decide +kernel

theorem rowEval11596 (x : Key → ℝ) : Integer.Sparse.eval row11596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11596, Integer.Sparse.eval_collectBalanced, rawRowCheck11596]

def rawRow11597 : Integer.Sparse Key := [(key2779, 1), (key2783, 1), (key2852, 1), (key2894, 1), (key2867, 1), (key2903, 1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2629, 1), (key2647, 1), (key2783, 1), (key2937, 1), (key2894, 1), (key2973, 1), (key2791, -2), (key2857, -2), (key2896, -2), (key2637, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2652, -2), (key2791, -2), (key2942, -2), (key2896, -2), (key2975, -2)]

theorem rawRowCheck11597 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form9 = rawRow11597 := by decide +kernel

def row11597 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11597 : row11597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11597 := by decide +kernel

theorem rowEval11597 (x : Key → ℝ) : Integer.Sparse.eval row11597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11597, Integer.Sparse.eval_collectBalanced, rawRowCheck11597]

def rawRow11598 : Integer.Sparse Key := [(key2783, 1), (key2779, 1), (key2894, 1), (key2852, 1), (key2903, 1), (key2867, 1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2647, 1), (key2629, 1), (key2937, 1), (key2783, 1), (key2973, 1), (key2894, 1), (key2791, -2), (key2896, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2857, -2), (key2652, -2), (key2637, -2), (key2942, -2), (key2791, -2), (key2975, -2), (key2896, -2)]

theorem rawRowCheck11598 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form9 = rawRow11598 := by decide +kernel

def row11598 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11598 : row11598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11598 := by decide +kernel

theorem rowEval11598 (x : Key → ℝ) : Integer.Sparse.eval row11598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11598, Integer.Sparse.eval_collectBalanced, rawRowCheck11598]

def rawRow11599 : Integer.Sparse Key := [(key2852, 1), (key2867, 1), (key2779, 1), (key2903, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2937, 1), (key2857, -2), (key2791, -2), (key2896, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2791, -2), (key2896, -2), (key2637, -2), (key2975, -2), (key2652, -2), (key2942, -2)]

theorem rawRowCheck11599 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form9 = rawRow11599 := by decide +kernel

def row11599 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11599 : row11599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11599 := by decide +kernel

theorem rowEval11599 (x : Key → ℝ) : Integer.Sparse.eval row11599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11599, Integer.Sparse.eval_collectBalanced, rawRowCheck11599]

def rawRow11600 : Integer.Sparse Key := [(key2867, 1), (key2852, 1), (key2903, 1), (key2779, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2937, 1), (key2647, 1), (key2857, -2), (key2896, -2), (key2791, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2896, -2), (key2791, -2), (key2975, -2), (key2637, -2), (key2942, -2), (key2652, -2)]

theorem rawRowCheck11600 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form9 = rawRow11600 := by decide +kernel

def row11600 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11600 : row11600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11600 := by decide +kernel

theorem rowEval11600 (x : Key → ℝ) : Integer.Sparse.eval row11600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11600, Integer.Sparse.eval_collectBalanced, rawRowCheck11600]

def rawRow11601 : Integer.Sparse Key := [(key2894, 1), (key2903, 1), (key2783, 1), (key2867, 1), (key2779, 1), (key2852, 1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2937, 1), (key2973, 1), (key2647, 1), (key2894, 1), (key2629, 1), (key2783, 1), (key2896, -2), (key2791, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2857, -2), (key2942, -2), (key2975, -2), (key2652, -2), (key2896, -2), (key2637, -2), (key2791, -2)]

theorem rawRowCheck11601 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form9 = rawRow11601 := by decide +kernel

def row11601 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11601 : row11601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11601 := by decide +kernel

theorem rowEval11601 (x : Key → ℝ) : Integer.Sparse.eval row11601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11601, Integer.Sparse.eval_collectBalanced, rawRowCheck11601]

def rawRow11602 : Integer.Sparse Key := [(key2903, 1), (key2894, 1), (key2867, 1), (key2783, 1), (key2852, 1), (key2779, 1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2973, 1), (key2937, 1), (key2894, 1), (key2647, 1), (key2783, 1), (key2629, 1), (key2896, -2), (key2857, -2), (key2791, -2), (key2975, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2942, -2), (key2896, -2), (key2652, -2), (key2791, -2), (key2637, -2)]

theorem rawRowCheck11602 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form9 = rawRow11602 := by decide +kernel

def row11602 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11602 : row11602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11602 := by decide +kernel

theorem rowEval11602 (x : Key → ℝ) : Integer.Sparse.eval row11602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11602, Integer.Sparse.eval_collectBalanced, rawRowCheck11602]

def rawRow11603 : Integer.Sparse Key := [(key2937, 1), (key2937, 1), (key2973, 1), (key2973, 1), (key2982, 1), (key2982, 1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2625, 1), (key2625, 1), (key2779, 1), (key2779, 1), (key2852, 1), (key2852, 1), (key2942, -2), (key2975, -2), (key2975, -2), (key2652, -2), (key2896, -2), (key2896, -2), (key2637, -2), (key2637, -2), (key2791, -2), (key2791, -2), (key2857, -2), (key2857, -2)]

theorem rawRowCheck11603 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form9 = rawRow11603 := by decide +kernel

def row11603 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11603 : row11603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11603 := by decide +kernel

theorem rowEval11603 (x : Key → ℝ) : Integer.Sparse.eval row11603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11603, Integer.Sparse.eval_collectBalanced, rawRowCheck11603]

def rawRow11604 : Integer.Sparse Key := [(key2973, 1), (key2982, 1), (key2937, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2975, -2), (key2942, -2), (key2975, -2), (key2896, -2), (key2652, -2), (key2896, -2), (key2791, -2), (key2857, -2), (key2637, -2), (key2857, -2), (key2637, -2), (key2791, -2)]

theorem rawRowCheck11604 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form9 = rawRow11604 := by decide +kernel

def row11604 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11604 : row11604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11604 := by decide +kernel

theorem rowEval11604 (x : Key → ℝ) : Integer.Sparse.eval row11604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11604, Integer.Sparse.eval_collectBalanced, rawRowCheck11604]

def rawRow11605 : Integer.Sparse Key := [(key2982, 1), (key2973, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2937, 1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2852, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2625, 1), (key2975, -2), (key2975, -2), (key2942, -2), (key2896, -2), (key2896, -2), (key2652, -2), (key2857, -2), (key2791, -2), (key2857, -2), (key2637, -2), (key2791, -2), (key2637, -2)]

theorem rawRowCheck11605 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form9 = rawRow11605 := by decide +kernel

def row11605 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

theorem rowCheck11605 : row11605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11605 := by decide +kernel

theorem rowEval11605 (x : Key → ℝ) : Integer.Sparse.eval row11605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11605, Integer.Sparse.eval_collectBalanced, rawRowCheck11605]

def rawRow11606 : Integer.Sparse Key := [(key1288, -6), (key1565, -6), (key1565, -6), (key1785, -6), (key1308, 2), (key1308, 2), (key1334, 2), (key1538, 2), (key1538, 2), (key1769, 2), (key1614, 2), (key1652, 2), (key1614, 2), (key1810, 2), (key1652, 2), (key1810, 2)]

theorem rawRowCheck11606 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form10 = rawRow11606 := by decide +kernel

def row11606 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11606 : row11606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11606 := by decide +kernel

theorem rowEval11606 (x : Key → ℝ) : Integer.Sparse.eval row11606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11606, Integer.Sparse.eval_collectBalanced, rawRowCheck11606]

def rawRow11607 : Integer.Sparse Key := [(key1288, -6), (key1565, -6), (key1785, -6), (key1565, -6), (key1308, 2), (key1334, 2), (key1308, 2), (key1538, 2), (key1769, 2), (key1538, 2), (key1652, 2), (key1614, 2), (key1810, 2), (key1614, 2), (key1810, 2), (key1652, 2)]

theorem rawRowCheck11607 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form10 = rawRow11607 := by decide +kernel

def row11607 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11607 : row11607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11607 := by decide +kernel

theorem rowEval11607 (x : Key → ℝ) : Integer.Sparse.eval row11607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11607, Integer.Sparse.eval_collectBalanced, rawRowCheck11607]

def rawRow11608 : Integer.Sparse Key := [(key1288, -6), (key1785, -6), (key1565, -6), (key1565, -6), (key1334, 2), (key1308, 2), (key1308, 2), (key1769, 2), (key1538, 2), (key1538, 2), (key1810, 2), (key1810, 2), (key1652, 2), (key1652, 2), (key1614, 2), (key1614, 2)]

theorem rawRowCheck11608 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form10 = rawRow11608 := by decide +kernel

def row11608 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11608 : row11608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11608 := by decide +kernel

theorem rowEval11608 (x : Key → ℝ) : Integer.Sparse.eval row11608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11608, Integer.Sparse.eval_collectBalanced, rawRowCheck11608]

def rawRow11609 : Integer.Sparse Key := [(key1565, -6), (key1288, -6), (key1565, -6), (key1785, -6), (key1538, 2), (key1614, 2), (key1652, 2), (key1308, 2), (key1614, 2), (key1810, 2), (key1308, 2), (key1334, 2), (key1538, 2), (key1769, 2), (key1652, 2), (key1810, 2)]

theorem rawRowCheck11609 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form10 = rawRow11609 := by decide +kernel

def row11609 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11609 : row11609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11609 := by decide +kernel

theorem rowEval11609 (x : Key → ℝ) : Integer.Sparse.eval row11609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11609, Integer.Sparse.eval_collectBalanced, rawRowCheck11609]

def rawRow11610 : Integer.Sparse Key := [(key1565, -6), (key1288, -6), (key1785, -6), (key1565, -6), (key1538, 2), (key1652, 2), (key1614, 2), (key1308, 2), (key1810, 2), (key1614, 2), (key1334, 2), (key1308, 2), (key1769, 2), (key1538, 2), (key1810, 2), (key1652, 2)]

theorem rawRowCheck11610 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form10 = rawRow11610 := by decide +kernel

def row11610 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11610 : row11610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11610 := by decide +kernel

theorem rowEval11610 (x : Key → ℝ) : Integer.Sparse.eval row11610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11610, Integer.Sparse.eval_collectBalanced, rawRowCheck11610]

def rawRow11611 : Integer.Sparse Key := [(key1565, -6), (key1565, -6), (key1288, -6), (key1785, -6), (key1614, 2), (key1538, 2), (key1652, 2), (key1614, 2), (key1308, 2), (key1810, 2), (key1538, 2), (key1652, 2), (key1308, 2), (key1810, 2), (key1334, 2), (key1769, 2)]

theorem rawRowCheck11611 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form10 = rawRow11611 := by decide +kernel

def row11611 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11611 : row11611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11611 := by decide +kernel

theorem rowEval11611 (x : Key → ℝ) : Integer.Sparse.eval row11611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11611, Integer.Sparse.eval_collectBalanced, rawRowCheck11611]

def rawRow11612 : Integer.Sparse Key := [(key1565, -6), (key1565, -6), (key1785, -6), (key1288, -6), (key1614, 2), (key1652, 2), (key1538, 2), (key1614, 2), (key1810, 2), (key1308, 2), (key1652, 2), (key1538, 2), (key1810, 2), (key1308, 2), (key1769, 2), (key1334, 2)]

theorem rawRowCheck11612 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form10 = rawRow11612 := by decide +kernel

def row11612 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11612 : row11612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11612 := by decide +kernel

theorem rowEval11612 (x : Key → ℝ) : Integer.Sparse.eval row11612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11612, Integer.Sparse.eval_collectBalanced, rawRowCheck11612]

def rawRow11613 : Integer.Sparse Key := [(key1565, -6), (key1785, -6), (key1288, -6), (key1565, -6), (key1652, 2), (key1538, 2), (key1614, 2), (key1810, 2), (key1308, 2), (key1614, 2), (key1769, 2), (key1810, 2), (key1334, 2), (key1652, 2), (key1308, 2), (key1538, 2)]

theorem rawRowCheck11613 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form10 = rawRow11613 := by decide +kernel

def row11613 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11613 : row11613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11613 := by decide +kernel

theorem rowEval11613 (x : Key → ℝ) : Integer.Sparse.eval row11613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11613, Integer.Sparse.eval_collectBalanced, rawRowCheck11613]

def rawRow11614 : Integer.Sparse Key := [(key1565, -6), (key1785, -6), (key1565, -6), (key1288, -6), (key1652, 2), (key1614, 2), (key1538, 2), (key1810, 2), (key1614, 2), (key1308, 2), (key1810, 2), (key1769, 2), (key1652, 2), (key1334, 2), (key1538, 2), (key1308, 2)]

theorem rawRowCheck11614 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form10 = rawRow11614 := by decide +kernel

def row11614 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11614 : row11614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11614 := by decide +kernel

theorem rowEval11614 (x : Key → ℝ) : Integer.Sparse.eval row11614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11614, Integer.Sparse.eval_collectBalanced, rawRowCheck11614]

def rawRow11615 : Integer.Sparse Key := [(key1785, -6), (key1288, -6), (key1565, -6), (key1565, -6), (key1769, 2), (key1810, 2), (key1810, 2), (key1334, 2), (key1652, 2), (key1652, 2), (key1308, 2), (key1308, 2), (key1538, 2), (key1538, 2), (key1614, 2), (key1614, 2)]

theorem rawRowCheck11615 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form10 = rawRow11615 := by decide +kernel

def row11615 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11615 : row11615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11615 := by decide +kernel

theorem rowEval11615 (x : Key → ℝ) : Integer.Sparse.eval row11615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11615, Integer.Sparse.eval_collectBalanced, rawRowCheck11615]

def rawRow11616 : Integer.Sparse Key := [(key1785, -6), (key1565, -6), (key1288, -6), (key1565, -6), (key1810, 2), (key1769, 2), (key1810, 2), (key1652, 2), (key1334, 2), (key1652, 2), (key1538, 2), (key1614, 2), (key1308, 2), (key1614, 2), (key1308, 2), (key1538, 2)]

theorem rawRowCheck11616 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form10 = rawRow11616 := by decide +kernel

def row11616 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11616 : row11616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11616 := by decide +kernel

theorem rowEval11616 (x : Key → ℝ) : Integer.Sparse.eval row11616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11616, Integer.Sparse.eval_collectBalanced, rawRowCheck11616]

def rawRow11617 : Integer.Sparse Key := [(key1785, -6), (key1565, -6), (key1565, -6), (key1288, -6), (key1810, 2), (key1810, 2), (key1769, 2), (key1652, 2), (key1652, 2), (key1334, 2), (key1614, 2), (key1538, 2), (key1614, 2), (key1308, 2), (key1538, 2), (key1308, 2)]

theorem rawRowCheck11617 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form10 = rawRow11617 := by decide +kernel

def row11617 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

theorem rowCheck11617 : row11617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11617 := by decide +kernel

theorem rowEval11617 (x : Key → ℝ) : Integer.Sparse.eval row11617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11617, Integer.Sparse.eval_collectBalanced, rawRowCheck11617]

def rawRow11618 : Integer.Sparse Key := [(key2398, 6), (key2401, 6), (key2401, 6), (key2433, 6), (key2597, -6), (key2886, -6), (key2886, -6), (key2908, -6)]

theorem rawRowCheck11618 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form11 = rawRow11618 := by decide +kernel

def row11618 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11618 : row11618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11618 := by decide +kernel

theorem rowEval11618 (x : Key → ℝ) : Integer.Sparse.eval row11618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11618, Integer.Sparse.eval_collectBalanced, rawRowCheck11618]

def rawRow11619 : Integer.Sparse Key := [(key2401, 6), (key2398, 6), (key2401, 6), (key2433, 6), (key2597, -6), (key2886, -6), (key2908, -6), (key2886, -6)]

theorem rawRowCheck11619 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form11 = rawRow11619 := by decide +kernel

def row11619 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11619 : row11619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11619 := by decide +kernel

theorem rowEval11619 (x : Key → ℝ) : Integer.Sparse.eval row11619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11619, Integer.Sparse.eval_collectBalanced, rawRowCheck11619]

def rawRow11620 : Integer.Sparse Key := [(key2401, 6), (key2401, 6), (key2398, 6), (key2433, 6), (key2597, -6), (key2908, -6), (key2886, -6), (key2886, -6)]

theorem rawRowCheck11620 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form11 = rawRow11620 := by decide +kernel

def row11620 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11620 : row11620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11620 := by decide +kernel

theorem rowEval11620 (x : Key → ℝ) : Integer.Sparse.eval row11620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11620, Integer.Sparse.eval_collectBalanced, rawRowCheck11620]

def rawRow11621 : Integer.Sparse Key := [(key2398, 6), (key2401, 6), (key2433, 6), (key2401, 6), (key2886, -6), (key2597, -6), (key2886, -6), (key2908, -6)]

theorem rawRowCheck11621 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form11 = rawRow11621 := by decide +kernel

def row11621 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11621 : row11621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11621 := by decide +kernel

theorem rowEval11621 (x : Key → ℝ) : Integer.Sparse.eval row11621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11621, Integer.Sparse.eval_collectBalanced, rawRowCheck11621]

def rawRow11622 : Integer.Sparse Key := [(key2401, 6), (key2398, 6), (key2433, 6), (key2401, 6), (key2886, -6), (key2597, -6), (key2908, -6), (key2886, -6)]

theorem rawRowCheck11622 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form11 = rawRow11622 := by decide +kernel

def row11622 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11622 : row11622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11622 := by decide +kernel

theorem rowEval11622 (x : Key → ℝ) : Integer.Sparse.eval row11622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11622, Integer.Sparse.eval_collectBalanced, rawRowCheck11622]

def rawRow11623 : Integer.Sparse Key := [(key2398, 6), (key2433, 6), (key2401, 6), (key2401, 6), (key2886, -6), (key2886, -6), (key2597, -6), (key2908, -6)]

theorem rawRowCheck11623 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form11 = rawRow11623 := by decide +kernel

def row11623 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11623 : row11623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11623 := by decide +kernel

theorem rowEval11623 (x : Key → ℝ) : Integer.Sparse.eval row11623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11623, Integer.Sparse.eval_collectBalanced, rawRowCheck11623]

def rawRow11624 : Integer.Sparse Key := [(key2433, 6), (key2398, 6), (key2401, 6), (key2401, 6), (key2886, -6), (key2886, -6), (key2908, -6), (key2597, -6)]

theorem rawRowCheck11624 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form11 = rawRow11624 := by decide +kernel

def row11624 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11624 : row11624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11624 := by decide +kernel

theorem rowEval11624 (x : Key → ℝ) : Integer.Sparse.eval row11624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11624, Integer.Sparse.eval_collectBalanced, rawRowCheck11624]

def rawRow11625 : Integer.Sparse Key := [(key2401, 6), (key2433, 6), (key2398, 6), (key2401, 6), (key2886, -6), (key2908, -6), (key2597, -6), (key2886, -6)]

theorem rawRowCheck11625 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form11 = rawRow11625 := by decide +kernel

def row11625 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11625 : row11625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11625 := by decide +kernel

theorem rowEval11625 (x : Key → ℝ) : Integer.Sparse.eval row11625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11625, Integer.Sparse.eval_collectBalanced, rawRowCheck11625]

def rawRow11626 : Integer.Sparse Key := [(key2433, 6), (key2401, 6), (key2398, 6), (key2401, 6), (key2886, -6), (key2908, -6), (key2886, -6), (key2597, -6)]

theorem rawRowCheck11626 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form11 = rawRow11626 := by decide +kernel

def row11626 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11626 : row11626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11626 := by decide +kernel

theorem rowEval11626 (x : Key → ℝ) : Integer.Sparse.eval row11626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11626, Integer.Sparse.eval_collectBalanced, rawRowCheck11626]

def rawRow11627 : Integer.Sparse Key := [(key2401, 6), (key2401, 6), (key2433, 6), (key2398, 6), (key2908, -6), (key2597, -6), (key2886, -6), (key2886, -6)]

theorem rawRowCheck11627 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form11 = rawRow11627 := by decide +kernel

def row11627 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11627 : row11627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11627 := by decide +kernel

theorem rowEval11627 (x : Key → ℝ) : Integer.Sparse.eval row11627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11627, Integer.Sparse.eval_collectBalanced, rawRowCheck11627]

def rawRow11628 : Integer.Sparse Key := [(key2401, 6), (key2433, 6), (key2401, 6), (key2398, 6), (key2908, -6), (key2886, -6), (key2597, -6), (key2886, -6)]

theorem rawRowCheck11628 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form11 = rawRow11628 := by decide +kernel

def row11628 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11628 : row11628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11628 := by decide +kernel

theorem rowEval11628 (x : Key → ℝ) : Integer.Sparse.eval row11628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11628, Integer.Sparse.eval_collectBalanced, rawRowCheck11628]

def rawRow11629 : Integer.Sparse Key := [(key2433, 6), (key2401, 6), (key2401, 6), (key2398, 6), (key2908, -6), (key2886, -6), (key2886, -6), (key2597, -6)]

theorem rawRowCheck11629 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form11 = rawRow11629 := by decide +kernel

def row11629 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

theorem rowCheck11629 : row11629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11629 := by decide +kernel

theorem rowEval11629 (x : Key → ℝ) : Integer.Sparse.eval row11629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11629, Integer.Sparse.eval_collectBalanced, rawRowCheck11629]

def rawRow11630 : Integer.Sparse Key := [(key2399, 6), (key2403, 6), (key2403, 6), (key2434, 6), (key2387, -6), (key2477, -6), (key2477, -6), (key2541, -6)]

theorem rawRowCheck11630 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form12 = rawRow11630 := by decide +kernel

def row11630 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11630 : row11630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11630 := by decide +kernel

theorem rowEval11630 (x : Key → ℝ) : Integer.Sparse.eval row11630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11630, Integer.Sparse.eval_collectBalanced, rawRowCheck11630]

def rawRow11631 : Integer.Sparse Key := [(key2403, 6), (key2399, 6), (key2403, 6), (key2434, 6), (key2387, -6), (key2477, -6), (key2541, -6), (key2477, -6)]

theorem rawRowCheck11631 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form12 = rawRow11631 := by decide +kernel

def row11631 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11631 : row11631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11631 := by decide +kernel

theorem rowEval11631 (x : Key → ℝ) : Integer.Sparse.eval row11631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11631, Integer.Sparse.eval_collectBalanced, rawRowCheck11631]

def rawRow11632 : Integer.Sparse Key := [(key2403, 6), (key2403, 6), (key2399, 6), (key2434, 6), (key2387, -6), (key2541, -6), (key2477, -6), (key2477, -6)]

theorem rawRowCheck11632 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form12 = rawRow11632 := by decide +kernel

def row11632 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11632 : row11632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11632 := by decide +kernel

theorem rowEval11632 (x : Key → ℝ) : Integer.Sparse.eval row11632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11632, Integer.Sparse.eval_collectBalanced, rawRowCheck11632]

def rawRow11633 : Integer.Sparse Key := [(key2399, 6), (key2403, 6), (key2434, 6), (key2403, 6), (key2477, -6), (key2387, -6), (key2477, -6), (key2541, -6)]

theorem rawRowCheck11633 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form12 = rawRow11633 := by decide +kernel

def row11633 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11633 : row11633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11633 := by decide +kernel

theorem rowEval11633 (x : Key → ℝ) : Integer.Sparse.eval row11633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11633, Integer.Sparse.eval_collectBalanced, rawRowCheck11633]

def rawRow11634 : Integer.Sparse Key := [(key2403, 6), (key2399, 6), (key2434, 6), (key2403, 6), (key2477, -6), (key2387, -6), (key2541, -6), (key2477, -6)]

theorem rawRowCheck11634 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form12 = rawRow11634 := by decide +kernel

def row11634 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11634 : row11634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11634 := by decide +kernel

theorem rowEval11634 (x : Key → ℝ) : Integer.Sparse.eval row11634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11634, Integer.Sparse.eval_collectBalanced, rawRowCheck11634]

def rawRow11635 : Integer.Sparse Key := [(key2399, 6), (key2434, 6), (key2403, 6), (key2403, 6), (key2477, -6), (key2477, -6), (key2387, -6), (key2541, -6)]

theorem rawRowCheck11635 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form12 = rawRow11635 := by decide +kernel

def row11635 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11635 : row11635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11635 := by decide +kernel

theorem rowEval11635 (x : Key → ℝ) : Integer.Sparse.eval row11635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11635, Integer.Sparse.eval_collectBalanced, rawRowCheck11635]

def rawRow11636 : Integer.Sparse Key := [(key2434, 6), (key2399, 6), (key2403, 6), (key2403, 6), (key2477, -6), (key2477, -6), (key2541, -6), (key2387, -6)]

theorem rawRowCheck11636 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form12 = rawRow11636 := by decide +kernel

def row11636 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11636 : row11636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11636 := by decide +kernel

theorem rowEval11636 (x : Key → ℝ) : Integer.Sparse.eval row11636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11636, Integer.Sparse.eval_collectBalanced, rawRowCheck11636]

def rawRow11637 : Integer.Sparse Key := [(key2403, 6), (key2434, 6), (key2399, 6), (key2403, 6), (key2477, -6), (key2541, -6), (key2387, -6), (key2477, -6)]

theorem rawRowCheck11637 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form12 = rawRow11637 := by decide +kernel

def row11637 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11637 : row11637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11637 := by decide +kernel

theorem rowEval11637 (x : Key → ℝ) : Integer.Sparse.eval row11637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11637, Integer.Sparse.eval_collectBalanced, rawRowCheck11637]

def rawRow11638 : Integer.Sparse Key := [(key2434, 6), (key2403, 6), (key2399, 6), (key2403, 6), (key2477, -6), (key2541, -6), (key2477, -6), (key2387, -6)]

theorem rawRowCheck11638 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form12 = rawRow11638 := by decide +kernel

def row11638 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11638 : row11638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11638 := by decide +kernel

theorem rowEval11638 (x : Key → ℝ) : Integer.Sparse.eval row11638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11638, Integer.Sparse.eval_collectBalanced, rawRowCheck11638]

def rawRow11639 : Integer.Sparse Key := [(key2403, 6), (key2403, 6), (key2434, 6), (key2399, 6), (key2541, -6), (key2387, -6), (key2477, -6), (key2477, -6)]

theorem rawRowCheck11639 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form12 = rawRow11639 := by decide +kernel

def row11639 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11639 : row11639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11639 := by decide +kernel

theorem rowEval11639 (x : Key → ℝ) : Integer.Sparse.eval row11639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11639, Integer.Sparse.eval_collectBalanced, rawRowCheck11639]

def rawRow11640 : Integer.Sparse Key := [(key2403, 6), (key2434, 6), (key2403, 6), (key2399, 6), (key2541, -6), (key2477, -6), (key2387, -6), (key2477, -6)]

theorem rawRowCheck11640 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form12 = rawRow11640 := by decide +kernel

def row11640 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11640 : row11640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11640 := by decide +kernel

theorem rowEval11640 (x : Key → ℝ) : Integer.Sparse.eval row11640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11640, Integer.Sparse.eval_collectBalanced, rawRowCheck11640]

def rawRow11641 : Integer.Sparse Key := [(key2434, 6), (key2403, 6), (key2403, 6), (key2399, 6), (key2541, -6), (key2477, -6), (key2477, -6), (key2387, -6)]

theorem rawRowCheck11641 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form12 = rawRow11641 := by decide +kernel

def row11641 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

theorem rowCheck11641 : row11641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11641 := by decide +kernel

theorem rowEval11641 (x : Key → ℝ) : Integer.Sparse.eval row11641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11641, Integer.Sparse.eval_collectBalanced, rawRowCheck11641]

def rawRow11642 : Integer.Sparse Key := [(key2193, -6), (key2194, -6), (key2194, -6), (key2200, -6), (key2091, 2), (key2092, 2), (key2092, 2), (key2302, 2), (key2303, 2), (key2302, 2), (key2341, 2), (key2303, 2), (key2341, 2), (key2310, 2), (key2310, 2), (key2347, 2)]

theorem rawRowCheck11642 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form13 = rawRow11642 := by decide +kernel

def row11642 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11642 : row11642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11642 := by decide +kernel

theorem rowEval11642 (x : Key → ℝ) : Integer.Sparse.eval row11642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11642, Integer.Sparse.eval_collectBalanced, rawRowCheck11642]

def rawRow11643 : Integer.Sparse Key := [(key2194, -6), (key2193, -6), (key2194, -6), (key2200, -6), (key2092, 2), (key2091, 2), (key2092, 2), (key2303, 2), (key2302, 2), (key2341, 2), (key2302, 2), (key2341, 2), (key2303, 2), (key2310, 2), (key2347, 2), (key2310, 2)]

theorem rawRowCheck11643 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form13 = rawRow11643 := by decide +kernel

def row11643 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11643 : row11643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11643 := by decide +kernel

theorem rowEval11643 (x : Key → ℝ) : Integer.Sparse.eval row11643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11643, Integer.Sparse.eval_collectBalanced, rawRowCheck11643]

def rawRow11644 : Integer.Sparse Key := [(key2194, -6), (key2194, -6), (key2193, -6), (key2200, -6), (key2092, 2), (key2092, 2), (key2091, 2), (key2341, 2), (key2341, 2), (key2303, 2), (key2303, 2), (key2302, 2), (key2302, 2), (key2347, 2), (key2310, 2), (key2310, 2)]

theorem rawRowCheck11644 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form13 = rawRow11644 := by decide +kernel

def row11644 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11644 : row11644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11644 := by decide +kernel

theorem rowEval11644 (x : Key → ℝ) : Integer.Sparse.eval row11644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11644, Integer.Sparse.eval_collectBalanced, rawRowCheck11644]

def rawRow11645 : Integer.Sparse Key := [(key2193, -6), (key2194, -6), (key2200, -6), (key2194, -6), (key2302, 2), (key2303, 2), (key2310, 2), (key2091, 2), (key2092, 2), (key2302, 2), (key2341, 2), (key2310, 2), (key2347, 2), (key2092, 2), (key2303, 2), (key2341, 2)]

theorem rawRowCheck11645 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form13 = rawRow11645 := by decide +kernel

def row11645 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11645 : row11645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11645 := by decide +kernel

theorem rowEval11645 (x : Key → ℝ) : Integer.Sparse.eval row11645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11645, Integer.Sparse.eval_collectBalanced, rawRowCheck11645]

def rawRow11646 : Integer.Sparse Key := [(key2194, -6), (key2193, -6), (key2200, -6), (key2194, -6), (key2303, 2), (key2302, 2), (key2310, 2), (key2092, 2), (key2091, 2), (key2341, 2), (key2302, 2), (key2347, 2), (key2310, 2), (key2092, 2), (key2341, 2), (key2303, 2)]

theorem rawRowCheck11646 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form13 = rawRow11646 := by decide +kernel

def row11646 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11646 : row11646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11646 := by decide +kernel

theorem rowEval11646 (x : Key → ℝ) : Integer.Sparse.eval row11646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck11646, Integer.Sparse.eval_collectBalanced, rawRowCheck11646]

def rawRow11647 : Integer.Sparse Key := [(key2193, -6), (key2200, -6), (key2194, -6), (key2194, -6), (key2302, 2), (key2310, 2), (key2303, 2), (key2302, 2), (key2310, 2), (key2091, 2), (key2347, 2), (key2092, 2), (key2341, 2), (key2303, 2), (key2092, 2), (key2341, 2)]

theorem rawRowCheck11647 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form13 = rawRow11647 := by decide +kernel

def row11647 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

theorem rowCheck11647 : row11647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11647 := by decide +kernel

theorem rowEval11647 (x : Key → ℝ) : Integer.Sparse.eval row11647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck11647, Integer.Sparse.eval_collectBalanced, rawRowCheck11647]

end MUB6.Certificate.GramRows

end OAI

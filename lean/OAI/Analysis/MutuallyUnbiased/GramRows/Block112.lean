import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
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

def rawRow11264 : Integer.Sparse Key := [(key2534, -6), (key2540, -6), (key2551, -6), (key2534, -6), (key2467, 2), (key2476, 2), (key2499, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2373, 2), (key2401, 2), (key2467, 2)]

theorem rawRowCheck11264 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form15 = rawRow11264 := by decide +kernel

def row11264 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11264 : row11264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11264 := by decide +kernel

theorem rowEval11264 (x : Key → ℝ) : Integer.Sparse.eval row11264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11264, Integer.Sparse.eval_collectBalanced, rawRowCheck11264]

def rawRow11265 : Integer.Sparse Key := [(key2540, -6), (key2534, -6), (key2551, -6), (key2534, -6), (key2476, 2), (key2467, 2), (key2499, 2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2373, 2), (key2467, 2), (key2401, 2)]

theorem rawRowCheck11265 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form15 = rawRow11265 := by decide +kernel

def row11265 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11265 : row11265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11265 := by decide +kernel

theorem rowEval11265 (x : Key → ℝ) : Integer.Sparse.eval row11265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11265, Integer.Sparse.eval_collectBalanced, rawRowCheck11265]

def rawRow11266 : Integer.Sparse Key := [(key2534, -6), (key2551, -6), (key2540, -6), (key2534, -6), (key2467, 2), (key2499, 2), (key2476, 2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2401, 2), (key2373, 2), (key2467, 2)]

theorem rawRowCheck11266 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form15 = rawRow11266 := by decide +kernel

def row11266 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11266 : row11266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11266 := by decide +kernel

theorem rowEval11266 (x : Key → ℝ) : Integer.Sparse.eval row11266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck11266, Integer.Sparse.eval_collectBalanced, rawRowCheck11266]

def rawRow11267 : Integer.Sparse Key := [(key2551, -6), (key2534, -6), (key2540, -6), (key2534, -6), (key2499, 2), (key2467, 2), (key2476, 2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2401, 2), (key2467, 2), (key2373, 2)]

theorem rawRowCheck11267 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form15 = rawRow11267 := by decide +kernel

def row11267 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11267 : row11267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11267 := by decide +kernel

theorem rowEval11267 (x : Key → ℝ) : Integer.Sparse.eval row11267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11267, Integer.Sparse.eval_collectBalanced, rawRowCheck11267]

def rawRow11268 : Integer.Sparse Key := [(key2540, -6), (key2551, -6), (key2534, -6), (key2534, -6), (key2476, 2), (key2499, 2), (key2467, 2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2467, 2), (key2373, 2), (key2401, 2)]

theorem rawRowCheck11268 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form15 = rawRow11268 := by decide +kernel

def row11268 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11268 : row11268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11268 := by decide +kernel

theorem rowEval11268 (x : Key → ℝ) : Integer.Sparse.eval row11268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck11268, Integer.Sparse.eval_collectBalanced, rawRowCheck11268]

def rawRow11269 : Integer.Sparse Key := [(key2551, -6), (key2540, -6), (key2534, -6), (key2534, -6), (key2499, 2), (key2476, 2), (key2467, 2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2467, 2), (key2401, 2), (key2373, 2)]

theorem rawRowCheck11269 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form15 = rawRow11269 := by decide +kernel

def row11269 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

theorem rowCheck11269 : row11269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11269 := by decide +kernel

theorem rowEval11269 (x : Key → ℝ) : Integer.Sparse.eval row11269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck11269, Integer.Sparse.eval_collectBalanced, rawRowCheck11269]

def rawRow11270 : Integer.Sparse Key := [(key2697, -6), (key2800, -6), (key2850, -6), (key2854, -6), (key2623, 6), (key2777, 6), (key2850, 6), (key2864, 6)]

theorem rawRowCheck11270 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form16 = rawRow11270 := by decide +kernel

def row11270 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11270 : row11270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11270 := by decide +kernel

theorem rowEval11270 (x : Key → ℝ) : Integer.Sparse.eval row11270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11270, Integer.Sparse.eval_collectBalanced, rawRowCheck11270]

def rawRow11271 : Integer.Sparse Key := [(key2697, -6), (key2800, -6), (key2854, -6), (key2850, -6), (key2623, 6), (key2777, 6), (key2864, 6), (key2850, 6)]

theorem rawRowCheck11271 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form16 = rawRow11271 := by decide +kernel

def row11271 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11271 : row11271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11271 := by decide +kernel

theorem rowEval11271 (x : Key → ℝ) : Integer.Sparse.eval row11271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11271, Integer.Sparse.eval_collectBalanced, rawRowCheck11271]

def rawRow11272 : Integer.Sparse Key := [(key2697, -6), (key2850, -6), (key2800, -6), (key2854, -6), (key2623, 6), (key2850, 6), (key2777, 6), (key2864, 6)]

theorem rawRowCheck11272 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form16 = rawRow11272 := by decide +kernel

def row11272 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11272 : row11272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11272 := by decide +kernel

theorem rowEval11272 (x : Key → ℝ) : Integer.Sparse.eval row11272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11272, Integer.Sparse.eval_collectBalanced, rawRowCheck11272]

def rawRow11273 : Integer.Sparse Key := [(key2697, -6), (key2850, -6), (key2854, -6), (key2800, -6), (key2623, 6), (key2850, 6), (key2864, 6), (key2777, 6)]

theorem rawRowCheck11273 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form16 = rawRow11273 := by decide +kernel

def row11273 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11273 : row11273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11273 := by decide +kernel

theorem rowEval11273 (x : Key → ℝ) : Integer.Sparse.eval row11273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11273, Integer.Sparse.eval_collectBalanced, rawRowCheck11273]

def rawRow11274 : Integer.Sparse Key := [(key2697, -6), (key2854, -6), (key2800, -6), (key2850, -6), (key2623, 6), (key2864, 6), (key2777, 6), (key2850, 6)]

theorem rawRowCheck11274 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form16 = rawRow11274 := by decide +kernel

def row11274 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11274 : row11274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11274 := by decide +kernel

theorem rowEval11274 (x : Key → ℝ) : Integer.Sparse.eval row11274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11274, Integer.Sparse.eval_collectBalanced, rawRowCheck11274]

def rawRow11275 : Integer.Sparse Key := [(key2697, -6), (key2854, -6), (key2850, -6), (key2800, -6), (key2623, 6), (key2864, 6), (key2850, 6), (key2777, 6)]

theorem rawRowCheck11275 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form16 = rawRow11275 := by decide +kernel

def row11275 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11275 : row11275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11275 := by decide +kernel

theorem rowEval11275 (x : Key → ℝ) : Integer.Sparse.eval row11275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11275, Integer.Sparse.eval_collectBalanced, rawRowCheck11275]

def rawRow11276 : Integer.Sparse Key := [(key2800, -6), (key2697, -6), (key2850, -6), (key2854, -6), (key2777, 6), (key2623, 6), (key2850, 6), (key2864, 6)]

theorem rawRowCheck11276 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form16 = rawRow11276 := by decide +kernel

def row11276 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11276 : row11276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11276 := by decide +kernel

theorem rowEval11276 (x : Key → ℝ) : Integer.Sparse.eval row11276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11276, Integer.Sparse.eval_collectBalanced, rawRowCheck11276]

def rawRow11277 : Integer.Sparse Key := [(key2800, -6), (key2697, -6), (key2854, -6), (key2850, -6), (key2777, 6), (key2623, 6), (key2864, 6), (key2850, 6)]

theorem rawRowCheck11277 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form16 = rawRow11277 := by decide +kernel

def row11277 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11277 : row11277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11277 := by decide +kernel

theorem rowEval11277 (x : Key → ℝ) : Integer.Sparse.eval row11277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11277, Integer.Sparse.eval_collectBalanced, rawRowCheck11277]

def rawRow11278 : Integer.Sparse Key := [(key2800, -6), (key2850, -6), (key2697, -6), (key2854, -6), (key2777, 6), (key2850, 6), (key2623, 6), (key2864, 6)]

theorem rawRowCheck11278 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form16 = rawRow11278 := by decide +kernel

def row11278 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11278 : row11278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11278 := by decide +kernel

theorem rowEval11278 (x : Key → ℝ) : Integer.Sparse.eval row11278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11278, Integer.Sparse.eval_collectBalanced, rawRowCheck11278]

def rawRow11279 : Integer.Sparse Key := [(key2800, -6), (key2850, -6), (key2854, -6), (key2697, -6), (key2777, 6), (key2850, 6), (key2864, 6), (key2623, 6)]

theorem rawRowCheck11279 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form16 = rawRow11279 := by decide +kernel

def row11279 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11279 : row11279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11279 := by decide +kernel

theorem rowEval11279 (x : Key → ℝ) : Integer.Sparse.eval row11279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11279, Integer.Sparse.eval_collectBalanced, rawRowCheck11279]

def rawRow11280 : Integer.Sparse Key := [(key2800, -6), (key2854, -6), (key2697, -6), (key2850, -6), (key2777, 6), (key2864, 6), (key2623, 6), (key2850, 6)]

theorem rawRowCheck11280 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form16 = rawRow11280 := by decide +kernel

def row11280 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11280 : row11280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11280 := by decide +kernel

theorem rowEval11280 (x : Key → ℝ) : Integer.Sparse.eval row11280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11280, Integer.Sparse.eval_collectBalanced, rawRowCheck11280]

def rawRow11281 : Integer.Sparse Key := [(key2800, -6), (key2854, -6), (key2850, -6), (key2697, -6), (key2777, 6), (key2864, 6), (key2850, 6), (key2623, 6)]

theorem rawRowCheck11281 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form16 = rawRow11281 := by decide +kernel

def row11281 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11281 : row11281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11281 := by decide +kernel

theorem rowEval11281 (x : Key → ℝ) : Integer.Sparse.eval row11281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11281, Integer.Sparse.eval_collectBalanced, rawRowCheck11281]

def rawRow11282 : Integer.Sparse Key := [(key2850, -6), (key2697, -6), (key2800, -6), (key2854, -6), (key2850, 6), (key2623, 6), (key2777, 6), (key2864, 6)]

theorem rawRowCheck11282 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form16 = rawRow11282 := by decide +kernel

def row11282 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11282 : row11282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11282 := by decide +kernel

theorem rowEval11282 (x : Key → ℝ) : Integer.Sparse.eval row11282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11282, Integer.Sparse.eval_collectBalanced, rawRowCheck11282]

def rawRow11283 : Integer.Sparse Key := [(key2850, -6), (key2697, -6), (key2854, -6), (key2800, -6), (key2850, 6), (key2623, 6), (key2864, 6), (key2777, 6)]

theorem rawRowCheck11283 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form16 = rawRow11283 := by decide +kernel

def row11283 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11283 : row11283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11283 := by decide +kernel

theorem rowEval11283 (x : Key → ℝ) : Integer.Sparse.eval row11283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11283, Integer.Sparse.eval_collectBalanced, rawRowCheck11283]

def rawRow11284 : Integer.Sparse Key := [(key2850, -6), (key2800, -6), (key2697, -6), (key2854, -6), (key2850, 6), (key2777, 6), (key2623, 6), (key2864, 6)]

theorem rawRowCheck11284 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form16 = rawRow11284 := by decide +kernel

def row11284 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11284 : row11284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11284 := by decide +kernel

theorem rowEval11284 (x : Key → ℝ) : Integer.Sparse.eval row11284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11284, Integer.Sparse.eval_collectBalanced, rawRowCheck11284]

def rawRow11285 : Integer.Sparse Key := [(key2850, -6), (key2800, -6), (key2854, -6), (key2697, -6), (key2850, 6), (key2777, 6), (key2864, 6), (key2623, 6)]

theorem rawRowCheck11285 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form16 = rawRow11285 := by decide +kernel

def row11285 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11285 : row11285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11285 := by decide +kernel

theorem rowEval11285 (x : Key → ℝ) : Integer.Sparse.eval row11285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11285, Integer.Sparse.eval_collectBalanced, rawRowCheck11285]

def rawRow11286 : Integer.Sparse Key := [(key2850, -6), (key2854, -6), (key2697, -6), (key2800, -6), (key2850, 6), (key2864, 6), (key2623, 6), (key2777, 6)]

theorem rawRowCheck11286 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form16 = rawRow11286 := by decide +kernel

def row11286 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11286 : row11286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11286 := by decide +kernel

theorem rowEval11286 (x : Key → ℝ) : Integer.Sparse.eval row11286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11286, Integer.Sparse.eval_collectBalanced, rawRowCheck11286]

def rawRow11287 : Integer.Sparse Key := [(key2850, -6), (key2854, -6), (key2800, -6), (key2697, -6), (key2850, 6), (key2864, 6), (key2777, 6), (key2623, 6)]

theorem rawRowCheck11287 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form16 = rawRow11287 := by decide +kernel

def row11287 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11287 : row11287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11287 := by decide +kernel

theorem rowEval11287 (x : Key → ℝ) : Integer.Sparse.eval row11287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11287, Integer.Sparse.eval_collectBalanced, rawRowCheck11287]

def rawRow11288 : Integer.Sparse Key := [(key2854, -6), (key2697, -6), (key2800, -6), (key2850, -6), (key2864, 6), (key2623, 6), (key2777, 6), (key2850, 6)]

theorem rawRowCheck11288 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form16 = rawRow11288 := by decide +kernel

def row11288 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11288 : row11288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11288 := by decide +kernel

theorem rowEval11288 (x : Key → ℝ) : Integer.Sparse.eval row11288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11288, Integer.Sparse.eval_collectBalanced, rawRowCheck11288]

def rawRow11289 : Integer.Sparse Key := [(key2854, -6), (key2697, -6), (key2850, -6), (key2800, -6), (key2864, 6), (key2623, 6), (key2850, 6), (key2777, 6)]

theorem rawRowCheck11289 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form16 = rawRow11289 := by decide +kernel

def row11289 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11289 : row11289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11289 := by decide +kernel

theorem rowEval11289 (x : Key → ℝ) : Integer.Sparse.eval row11289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11289, Integer.Sparse.eval_collectBalanced, rawRowCheck11289]

def rawRow11290 : Integer.Sparse Key := [(key2854, -6), (key2800, -6), (key2697, -6), (key2850, -6), (key2864, 6), (key2777, 6), (key2623, 6), (key2850, 6)]

theorem rawRowCheck11290 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form16 = rawRow11290 := by decide +kernel

def row11290 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11290 : row11290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11290 := by decide +kernel

theorem rowEval11290 (x : Key → ℝ) : Integer.Sparse.eval row11290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11290, Integer.Sparse.eval_collectBalanced, rawRowCheck11290]

def rawRow11291 : Integer.Sparse Key := [(key2854, -6), (key2800, -6), (key2850, -6), (key2697, -6), (key2864, 6), (key2777, 6), (key2850, 6), (key2623, 6)]

theorem rawRowCheck11291 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form16 = rawRow11291 := by decide +kernel

def row11291 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11291 : row11291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11291 := by decide +kernel

theorem rowEval11291 (x : Key → ℝ) : Integer.Sparse.eval row11291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11291, Integer.Sparse.eval_collectBalanced, rawRowCheck11291]

def rawRow11292 : Integer.Sparse Key := [(key2854, -6), (key2850, -6), (key2697, -6), (key2800, -6), (key2864, 6), (key2850, 6), (key2623, 6), (key2777, 6)]

theorem rawRowCheck11292 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form16 = rawRow11292 := by decide +kernel

def row11292 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11292 : row11292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11292 := by decide +kernel

theorem rowEval11292 (x : Key → ℝ) : Integer.Sparse.eval row11292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11292, Integer.Sparse.eval_collectBalanced, rawRowCheck11292]

def rawRow11293 : Integer.Sparse Key := [(key2854, -6), (key2850, -6), (key2800, -6), (key2697, -6), (key2864, 6), (key2850, 6), (key2777, 6), (key2623, 6)]

theorem rawRowCheck11293 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form16 = rawRow11293 := by decide +kernel

def row11293 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

theorem rowCheck11293 : row11293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11293 := by decide +kernel

theorem rowEval11293 (x : Key → ℝ) : Integer.Sparse.eval row11293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11293, Integer.Sparse.eval_collectBalanced, rawRowCheck11293]

def rawRow11294 : Integer.Sparse Key := [(key2720, -6), (key2823, -6), (key2864, -6), (key2864, -6), (key2634, 6), (key2788, 6), (key2854, 6), (key2854, 6)]

theorem rawRowCheck11294 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form16 = rawRow11294 := by decide +kernel

def row11294 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11294 : row11294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11294 := by decide +kernel

theorem rowEval11294 (x : Key → ℝ) : Integer.Sparse.eval row11294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11294, Integer.Sparse.eval_collectBalanced, rawRowCheck11294]

def rawRow11295 : Integer.Sparse Key := [(key2720, -6), (key2864, -6), (key2823, -6), (key2864, -6), (key2634, 6), (key2854, 6), (key2788, 6), (key2854, 6)]

theorem rawRowCheck11295 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form16 = rawRow11295 := by decide +kernel

def row11295 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11295 : row11295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11295 := by decide +kernel

theorem rowEval11295 (x : Key → ℝ) : Integer.Sparse.eval row11295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11295, Integer.Sparse.eval_collectBalanced, rawRowCheck11295]

def rawRow11296 : Integer.Sparse Key := [(key2720, -6), (key2864, -6), (key2864, -6), (key2823, -6), (key2634, 6), (key2854, 6), (key2854, 6), (key2788, 6)]

theorem rawRowCheck11296 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form16 = rawRow11296 := by decide +kernel

def row11296 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11296 : row11296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11296 := by decide +kernel

theorem rowEval11296 (x : Key → ℝ) : Integer.Sparse.eval row11296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11296, Integer.Sparse.eval_collectBalanced, rawRowCheck11296]

def rawRow11297 : Integer.Sparse Key := [(key2823, -6), (key2720, -6), (key2864, -6), (key2864, -6), (key2788, 6), (key2634, 6), (key2854, 6), (key2854, 6)]

theorem rawRowCheck11297 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form16 = rawRow11297 := by decide +kernel

def row11297 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11297 : row11297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11297 := by decide +kernel

theorem rowEval11297 (x : Key → ℝ) : Integer.Sparse.eval row11297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11297, Integer.Sparse.eval_collectBalanced, rawRowCheck11297]

def rawRow11298 : Integer.Sparse Key := [(key2823, -6), (key2864, -6), (key2720, -6), (key2864, -6), (key2788, 6), (key2854, 6), (key2634, 6), (key2854, 6)]

theorem rawRowCheck11298 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form16 = rawRow11298 := by decide +kernel

def row11298 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11298 : row11298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11298 := by decide +kernel

theorem rowEval11298 (x : Key → ℝ) : Integer.Sparse.eval row11298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11298, Integer.Sparse.eval_collectBalanced, rawRowCheck11298]

def rawRow11299 : Integer.Sparse Key := [(key2823, -6), (key2864, -6), (key2864, -6), (key2720, -6), (key2788, 6), (key2854, 6), (key2854, 6), (key2634, 6)]

theorem rawRowCheck11299 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form16 = rawRow11299 := by decide +kernel

def row11299 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11299 : row11299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11299 := by decide +kernel

theorem rowEval11299 (x : Key → ℝ) : Integer.Sparse.eval row11299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11299, Integer.Sparse.eval_collectBalanced, rawRowCheck11299]

def rawRow11300 : Integer.Sparse Key := [(key2864, -6), (key2720, -6), (key2823, -6), (key2864, -6), (key2854, 6), (key2634, 6), (key2788, 6), (key2854, 6)]

theorem rawRowCheck11300 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form16 = rawRow11300 := by decide +kernel

def row11300 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11300 : row11300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11300 := by decide +kernel

theorem rowEval11300 (x : Key → ℝ) : Integer.Sparse.eval row11300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11300, Integer.Sparse.eval_collectBalanced, rawRowCheck11300]

def rawRow11301 : Integer.Sparse Key := [(key2864, -6), (key2720, -6), (key2864, -6), (key2823, -6), (key2854, 6), (key2634, 6), (key2854, 6), (key2788, 6)]

theorem rawRowCheck11301 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form16 = rawRow11301 := by decide +kernel

def row11301 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11301 : row11301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11301 := by decide +kernel

theorem rowEval11301 (x : Key → ℝ) : Integer.Sparse.eval row11301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11301, Integer.Sparse.eval_collectBalanced, rawRowCheck11301]

def rawRow11302 : Integer.Sparse Key := [(key2864, -6), (key2823, -6), (key2720, -6), (key2864, -6), (key2854, 6), (key2788, 6), (key2634, 6), (key2854, 6)]

theorem rawRowCheck11302 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form16 = rawRow11302 := by decide +kernel

def row11302 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11302 : row11302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11302 := by decide +kernel

theorem rowEval11302 (x : Key → ℝ) : Integer.Sparse.eval row11302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11302, Integer.Sparse.eval_collectBalanced, rawRowCheck11302]

def rawRow11303 : Integer.Sparse Key := [(key2864, -6), (key2823, -6), (key2864, -6), (key2720, -6), (key2854, 6), (key2788, 6), (key2854, 6), (key2634, 6)]

theorem rawRowCheck11303 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form16 = rawRow11303 := by decide +kernel

def row11303 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11303 : row11303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11303 := by decide +kernel

theorem rowEval11303 (x : Key → ℝ) : Integer.Sparse.eval row11303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11303, Integer.Sparse.eval_collectBalanced, rawRowCheck11303]

def rawRow11304 : Integer.Sparse Key := [(key2864, -6), (key2864, -6), (key2720, -6), (key2823, -6), (key2854, 6), (key2854, 6), (key2634, 6), (key2788, 6)]

theorem rawRowCheck11304 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form16 = rawRow11304 := by decide +kernel

def row11304 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11304 : row11304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11304 := by decide +kernel

theorem rowEval11304 (x : Key → ℝ) : Integer.Sparse.eval row11304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck11304, Integer.Sparse.eval_collectBalanced, rawRowCheck11304]

def rawRow11305 : Integer.Sparse Key := [(key2864, -6), (key2864, -6), (key2823, -6), (key2720, -6), (key2854, 6), (key2854, 6), (key2788, 6), (key2634, 6)]

theorem rawRowCheck11305 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form16 = rawRow11305 := by decide +kernel

def row11305 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

theorem rowCheck11305 : row11305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11305 := by decide +kernel

theorem rowEval11305 (x : Key → ℝ) : Integer.Sparse.eval row11305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck11305, Integer.Sparse.eval_collectBalanced, rawRowCheck11305]

def rawRow11306 : Integer.Sparse Key := [(key2632, -2), (key2640, -2), (key2642, -2), (key2706, -2), (key2860, -2), (key2977, -2), (key2726, -2), (key2729, -2), (key2870, -2), (key2984, -2), (key2883, -2), (key2992, -2), (key2616, 2), (key2640, 2), (key2654, 2), (key2671, 2), (key2794, 2), (key2944, 2), (key2726, 2), (key2748, 2), (key2829, 2), (key2961, 2), (key2913, 2), (key2992, 2)]

theorem rawRowCheck11306 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form17 = rawRow11306 := by decide +kernel

def row11306 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11306 : row11306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11306 := by decide +kernel

theorem rowEval11306 (x : Key → ℝ) : Integer.Sparse.eval row11306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11306, Integer.Sparse.eval_collectBalanced, rawRowCheck11306]

def rawRow11307 : Integer.Sparse Key := [(key2632, -2), (key2642, -2), (key2640, -2), (key2706, -2), (key2977, -2), (key2860, -2), (key2729, -2), (key2726, -2), (key2984, -2), (key2870, -2), (key2992, -2), (key2883, -2), (key2616, 2), (key2654, 2), (key2640, 2), (key2671, 2), (key2944, 2), (key2794, 2), (key2748, 2), (key2726, 2), (key2961, 2), (key2829, 2), (key2992, 2), (key2913, 2)]

theorem rawRowCheck11307 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form17 = rawRow11307 := by decide +kernel

def row11307 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11307 : row11307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11307 := by decide +kernel

theorem rowEval11307 (x : Key → ℝ) : Integer.Sparse.eval row11307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11307, Integer.Sparse.eval_collectBalanced, rawRowCheck11307]

def rawRow11308 : Integer.Sparse Key := [(key2640, -2), (key2632, -2), (key2642, -2), (key2860, -2), (key2706, -2), (key2977, -2), (key2870, -2), (key2883, -2), (key2726, -2), (key2992, -2), (key2729, -2), (key2984, -2), (key2640, 2), (key2616, 2), (key2654, 2), (key2794, 2), (key2671, 2), (key2944, 2), (key2829, 2), (key2913, 2), (key2726, 2), (key2992, 2), (key2748, 2), (key2961, 2)]

theorem rawRowCheck11308 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form17 = rawRow11308 := by decide +kernel

def row11308 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11308 : row11308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11308 := by decide +kernel

theorem rowEval11308 (x : Key → ℝ) : Integer.Sparse.eval row11308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11308, Integer.Sparse.eval_collectBalanced, rawRowCheck11308]

def rawRow11309 : Integer.Sparse Key := [(key2640, -2), (key2642, -2), (key2632, -2), (key2860, -2), (key2977, -2), (key2706, -2), (key2883, -2), (key2870, -2), (key2992, -2), (key2726, -2), (key2984, -2), (key2729, -2), (key2640, 2), (key2654, 2), (key2616, 2), (key2794, 2), (key2944, 2), (key2671, 2), (key2913, 2), (key2829, 2), (key2992, 2), (key2726, 2), (key2961, 2), (key2748, 2)]

theorem rawRowCheck11309 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form17 = rawRow11309 := by decide +kernel

def row11309 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11309 : row11309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11309 := by decide +kernel

theorem rowEval11309 (x : Key → ℝ) : Integer.Sparse.eval row11309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11309, Integer.Sparse.eval_collectBalanced, rawRowCheck11309]

def rawRow11310 : Integer.Sparse Key := [(key2642, -2), (key2632, -2), (key2640, -2), (key2977, -2), (key2706, -2), (key2860, -2), (key2984, -2), (key2992, -2), (key2729, -2), (key2883, -2), (key2726, -2), (key2870, -2), (key2654, 2), (key2616, 2), (key2640, 2), (key2944, 2), (key2671, 2), (key2794, 2), (key2961, 2), (key2992, 2), (key2748, 2), (key2913, 2), (key2726, 2), (key2829, 2)]

theorem rawRowCheck11310 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form17 = rawRow11310 := by decide +kernel

def row11310 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11310 : row11310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11310 := by decide +kernel

theorem rowEval11310 (x : Key → ℝ) : Integer.Sparse.eval row11310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11310, Integer.Sparse.eval_collectBalanced, rawRowCheck11310]

def rawRow11311 : Integer.Sparse Key := [(key2642, -2), (key2640, -2), (key2632, -2), (key2977, -2), (key2860, -2), (key2706, -2), (key2992, -2), (key2984, -2), (key2883, -2), (key2729, -2), (key2870, -2), (key2726, -2), (key2654, 2), (key2640, 2), (key2616, 2), (key2944, 2), (key2794, 2), (key2671, 2), (key2992, 2), (key2961, 2), (key2913, 2), (key2748, 2), (key2829, 2), (key2726, 2)]

theorem rawRowCheck11311 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form17 = rawRow11311 := by decide +kernel

def row11311 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11311 : row11311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11311 := by decide +kernel

theorem rowEval11311 (x : Key → ℝ) : Integer.Sparse.eval row11311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11311, Integer.Sparse.eval_collectBalanced, rawRowCheck11311]

def rawRow11312 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2632, -2), (key2870, -2), (key2984, -2), (key2640, -2), (key2642, -2), (key2860, -2), (key2977, -2), (key2883, -2), (key2992, -2), (key2671, 2), (key2726, 2), (key2748, 2), (key2616, 2), (key2829, 2), (key2961, 2), (key2640, 2), (key2654, 2), (key2794, 2), (key2944, 2), (key2913, 2), (key2992, 2)]

theorem rawRowCheck11312 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form17 = rawRow11312 := by decide +kernel

def row11312 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11312 : row11312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11312 := by decide +kernel

theorem rowEval11312 (x : Key → ℝ) : Integer.Sparse.eval row11312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11312, Integer.Sparse.eval_collectBalanced, rawRowCheck11312]

def rawRow11313 : Integer.Sparse Key := [(key2706, -2), (key2729, -2), (key2726, -2), (key2632, -2), (key2984, -2), (key2870, -2), (key2642, -2), (key2640, -2), (key2977, -2), (key2860, -2), (key2992, -2), (key2883, -2), (key2671, 2), (key2748, 2), (key2726, 2), (key2616, 2), (key2961, 2), (key2829, 2), (key2654, 2), (key2640, 2), (key2944, 2), (key2794, 2), (key2992, 2), (key2913, 2)]

theorem rawRowCheck11313 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form17 = rawRow11313 := by decide +kernel

def row11313 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11313 : row11313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11313 := by decide +kernel

theorem rowEval11313 (x : Key → ℝ) : Integer.Sparse.eval row11313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11313, Integer.Sparse.eval_collectBalanced, rawRowCheck11313]

def rawRow11314 : Integer.Sparse Key := [(key2726, -2), (key2706, -2), (key2729, -2), (key2870, -2), (key2632, -2), (key2984, -2), (key2860, -2), (key2883, -2), (key2640, -2), (key2992, -2), (key2642, -2), (key2977, -2), (key2726, 2), (key2671, 2), (key2748, 2), (key2829, 2), (key2616, 2), (key2961, 2), (key2794, 2), (key2913, 2), (key2640, 2), (key2992, 2), (key2654, 2), (key2944, 2)]

theorem rawRowCheck11314 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form17 = rawRow11314 := by decide +kernel

def row11314 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11314 : row11314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11314 := by decide +kernel

theorem rowEval11314 (x : Key → ℝ) : Integer.Sparse.eval row11314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11314, Integer.Sparse.eval_collectBalanced, rawRowCheck11314]

def rawRow11315 : Integer.Sparse Key := [(key2726, -2), (key2729, -2), (key2706, -2), (key2870, -2), (key2984, -2), (key2632, -2), (key2883, -2), (key2860, -2), (key2992, -2), (key2640, -2), (key2977, -2), (key2642, -2), (key2726, 2), (key2748, 2), (key2671, 2), (key2829, 2), (key2961, 2), (key2616, 2), (key2913, 2), (key2794, 2), (key2992, 2), (key2640, 2), (key2944, 2), (key2654, 2)]

theorem rawRowCheck11315 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form17 = rawRow11315 := by decide +kernel

def row11315 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11315 : row11315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11315 := by decide +kernel

theorem rowEval11315 (x : Key → ℝ) : Integer.Sparse.eval row11315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11315, Integer.Sparse.eval_collectBalanced, rawRowCheck11315]

def rawRow11316 : Integer.Sparse Key := [(key2729, -2), (key2706, -2), (key2726, -2), (key2984, -2), (key2632, -2), (key2870, -2), (key2977, -2), (key2992, -2), (key2642, -2), (key2883, -2), (key2640, -2), (key2860, -2), (key2748, 2), (key2671, 2), (key2726, 2), (key2961, 2), (key2616, 2), (key2829, 2), (key2944, 2), (key2992, 2), (key2654, 2), (key2913, 2), (key2640, 2), (key2794, 2)]

theorem rawRowCheck11316 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form17 = rawRow11316 := by decide +kernel

def row11316 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11316 : row11316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11316 := by decide +kernel

theorem rowEval11316 (x : Key → ℝ) : Integer.Sparse.eval row11316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11316, Integer.Sparse.eval_collectBalanced, rawRowCheck11316]

def rawRow11317 : Integer.Sparse Key := [(key2729, -2), (key2726, -2), (key2706, -2), (key2984, -2), (key2870, -2), (key2632, -2), (key2992, -2), (key2977, -2), (key2883, -2), (key2642, -2), (key2860, -2), (key2640, -2), (key2748, 2), (key2726, 2), (key2671, 2), (key2961, 2), (key2829, 2), (key2616, 2), (key2992, 2), (key2944, 2), (key2913, 2), (key2654, 2), (key2794, 2), (key2640, 2)]

theorem rawRowCheck11317 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form17 = rawRow11317 := by decide +kernel

def row11317 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11317 : row11317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11317 := by decide +kernel

theorem rowEval11317 (x : Key → ℝ) : Integer.Sparse.eval row11317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11317, Integer.Sparse.eval_collectBalanced, rawRowCheck11317]

def rawRow11318 : Integer.Sparse Key := [(key2860, -2), (key2870, -2), (key2883, -2), (key2640, -2), (key2726, -2), (key2992, -2), (key2632, -2), (key2642, -2), (key2706, -2), (key2977, -2), (key2729, -2), (key2984, -2), (key2794, 2), (key2829, 2), (key2913, 2), (key2640, 2), (key2726, 2), (key2992, 2), (key2616, 2), (key2654, 2), (key2671, 2), (key2944, 2), (key2748, 2), (key2961, 2)]

theorem rawRowCheck11318 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form17 = rawRow11318 := by decide +kernel

def row11318 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11318 : row11318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11318 := by decide +kernel

theorem rowEval11318 (x : Key → ℝ) : Integer.Sparse.eval row11318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11318, Integer.Sparse.eval_collectBalanced, rawRowCheck11318]

def rawRow11319 : Integer.Sparse Key := [(key2860, -2), (key2883, -2), (key2870, -2), (key2640, -2), (key2992, -2), (key2726, -2), (key2642, -2), (key2632, -2), (key2977, -2), (key2706, -2), (key2984, -2), (key2729, -2), (key2794, 2), (key2913, 2), (key2829, 2), (key2640, 2), (key2992, 2), (key2726, 2), (key2654, 2), (key2616, 2), (key2944, 2), (key2671, 2), (key2961, 2), (key2748, 2)]

theorem rawRowCheck11319 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form17 = rawRow11319 := by decide +kernel

def row11319 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11319 : row11319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11319 := by decide +kernel

theorem rowEval11319 (x : Key → ℝ) : Integer.Sparse.eval row11319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11319, Integer.Sparse.eval_collectBalanced, rawRowCheck11319]

def rawRow11320 : Integer.Sparse Key := [(key2870, -2), (key2860, -2), (key2883, -2), (key2726, -2), (key2640, -2), (key2992, -2), (key2706, -2), (key2729, -2), (key2632, -2), (key2984, -2), (key2642, -2), (key2977, -2), (key2829, 2), (key2794, 2), (key2913, 2), (key2726, 2), (key2640, 2), (key2992, 2), (key2671, 2), (key2748, 2), (key2616, 2), (key2961, 2), (key2654, 2), (key2944, 2)]

theorem rawRowCheck11320 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form17 = rawRow11320 := by decide +kernel

def row11320 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11320 : row11320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11320 := by decide +kernel

theorem rowEval11320 (x : Key → ℝ) : Integer.Sparse.eval row11320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11320, Integer.Sparse.eval_collectBalanced, rawRowCheck11320]

def rawRow11321 : Integer.Sparse Key := [(key2870, -2), (key2883, -2), (key2860, -2), (key2726, -2), (key2992, -2), (key2640, -2), (key2729, -2), (key2706, -2), (key2984, -2), (key2632, -2), (key2977, -2), (key2642, -2), (key2829, 2), (key2913, 2), (key2794, 2), (key2726, 2), (key2992, 2), (key2640, 2), (key2748, 2), (key2671, 2), (key2961, 2), (key2616, 2), (key2944, 2), (key2654, 2)]

theorem rawRowCheck11321 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form17 = rawRow11321 := by decide +kernel

def row11321 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11321 : row11321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11321 := by decide +kernel

theorem rowEval11321 (x : Key → ℝ) : Integer.Sparse.eval row11321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11321, Integer.Sparse.eval_collectBalanced, rawRowCheck11321]

def rawRow11322 : Integer.Sparse Key := [(key2883, -2), (key2860, -2), (key2870, -2), (key2992, -2), (key2640, -2), (key2726, -2), (key2977, -2), (key2984, -2), (key2642, -2), (key2729, -2), (key2632, -2), (key2706, -2), (key2913, 2), (key2794, 2), (key2829, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2944, 2), (key2961, 2), (key2654, 2), (key2748, 2), (key2616, 2), (key2671, 2)]

theorem rawRowCheck11322 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form17 = rawRow11322 := by decide +kernel

def row11322 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11322 : row11322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11322 := by decide +kernel

theorem rowEval11322 (x : Key → ℝ) : Integer.Sparse.eval row11322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11322, Integer.Sparse.eval_collectBalanced, rawRowCheck11322]

def rawRow11323 : Integer.Sparse Key := [(key2883, -2), (key2870, -2), (key2860, -2), (key2992, -2), (key2726, -2), (key2640, -2), (key2984, -2), (key2977, -2), (key2729, -2), (key2642, -2), (key2706, -2), (key2632, -2), (key2913, 2), (key2829, 2), (key2794, 2), (key2992, 2), (key2726, 2), (key2640, 2), (key2961, 2), (key2944, 2), (key2748, 2), (key2654, 2), (key2671, 2), (key2616, 2)]

theorem rawRowCheck11323 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form17 = rawRow11323 := by decide +kernel

def row11323 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11323 : row11323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11323 := by decide +kernel

theorem rowEval11323 (x : Key → ℝ) : Integer.Sparse.eval row11323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11323, Integer.Sparse.eval_collectBalanced, rawRowCheck11323]

def rawRow11324 : Integer.Sparse Key := [(key2977, -2), (key2984, -2), (key2992, -2), (key2642, -2), (key2729, -2), (key2883, -2), (key2632, -2), (key2640, -2), (key2706, -2), (key2860, -2), (key2726, -2), (key2870, -2), (key2944, 2), (key2961, 2), (key2992, 2), (key2654, 2), (key2748, 2), (key2913, 2), (key2616, 2), (key2640, 2), (key2671, 2), (key2794, 2), (key2726, 2), (key2829, 2)]

theorem rawRowCheck11324 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form17 = rawRow11324 := by decide +kernel

def row11324 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11324 : row11324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11324 := by decide +kernel

theorem rowEval11324 (x : Key → ℝ) : Integer.Sparse.eval row11324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11324, Integer.Sparse.eval_collectBalanced, rawRowCheck11324]

def rawRow11325 : Integer.Sparse Key := [(key2977, -2), (key2992, -2), (key2984, -2), (key2642, -2), (key2883, -2), (key2729, -2), (key2640, -2), (key2632, -2), (key2860, -2), (key2706, -2), (key2870, -2), (key2726, -2), (key2944, 2), (key2992, 2), (key2961, 2), (key2654, 2), (key2913, 2), (key2748, 2), (key2640, 2), (key2616, 2), (key2794, 2), (key2671, 2), (key2829, 2), (key2726, 2)]

theorem rawRowCheck11325 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form17 = rawRow11325 := by decide +kernel

def row11325 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11325 : row11325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11325 := by decide +kernel

theorem rowEval11325 (x : Key → ℝ) : Integer.Sparse.eval row11325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11325, Integer.Sparse.eval_collectBalanced, rawRowCheck11325]

def rawRow11326 : Integer.Sparse Key := [(key2984, -2), (key2977, -2), (key2992, -2), (key2729, -2), (key2642, -2), (key2883, -2), (key2706, -2), (key2726, -2), (key2632, -2), (key2870, -2), (key2640, -2), (key2860, -2), (key2961, 2), (key2944, 2), (key2992, 2), (key2748, 2), (key2654, 2), (key2913, 2), (key2671, 2), (key2726, 2), (key2616, 2), (key2829, 2), (key2640, 2), (key2794, 2)]

theorem rawRowCheck11326 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form17 = rawRow11326 := by decide +kernel

def row11326 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11326 : row11326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11326 := by decide +kernel

theorem rowEval11326 (x : Key → ℝ) : Integer.Sparse.eval row11326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11326, Integer.Sparse.eval_collectBalanced, rawRowCheck11326]

def rawRow11327 : Integer.Sparse Key := [(key2984, -2), (key2992, -2), (key2977, -2), (key2729, -2), (key2883, -2), (key2642, -2), (key2726, -2), (key2706, -2), (key2870, -2), (key2632, -2), (key2860, -2), (key2640, -2), (key2961, 2), (key2992, 2), (key2944, 2), (key2748, 2), (key2913, 2), (key2654, 2), (key2726, 2), (key2671, 2), (key2829, 2), (key2616, 2), (key2794, 2), (key2640, 2)]

theorem rawRowCheck11327 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form17 = rawRow11327 := by decide +kernel

def row11327 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11327 : row11327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11327 := by decide +kernel

theorem rowEval11327 (x : Key → ℝ) : Integer.Sparse.eval row11327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11327, Integer.Sparse.eval_collectBalanced, rawRowCheck11327]

def rawRow11328 : Integer.Sparse Key := [(key2992, -2), (key2977, -2), (key2984, -2), (key2883, -2), (key2642, -2), (key2729, -2), (key2860, -2), (key2870, -2), (key2640, -2), (key2726, -2), (key2632, -2), (key2706, -2), (key2992, 2), (key2944, 2), (key2961, 2), (key2913, 2), (key2654, 2), (key2748, 2), (key2794, 2), (key2829, 2), (key2640, 2), (key2726, 2), (key2616, 2), (key2671, 2)]

theorem rawRowCheck11328 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form17 = rawRow11328 := by decide +kernel

def row11328 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11328 : row11328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11328 := by decide +kernel

theorem rowEval11328 (x : Key → ℝ) : Integer.Sparse.eval row11328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11328, Integer.Sparse.eval_collectBalanced, rawRowCheck11328]

def rawRow11329 : Integer.Sparse Key := [(key2992, -2), (key2984, -2), (key2977, -2), (key2883, -2), (key2729, -2), (key2642, -2), (key2870, -2), (key2860, -2), (key2726, -2), (key2640, -2), (key2706, -2), (key2632, -2), (key2992, 2), (key2961, 2), (key2944, 2), (key2913, 2), (key2748, 2), (key2654, 2), (key2829, 2), (key2794, 2), (key2726, 2), (key2640, 2), (key2671, 2), (key2616, 2)]

theorem rawRowCheck11329 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form17 = rawRow11329 := by decide +kernel

def row11329 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

theorem rowCheck11329 : row11329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11329 := by decide +kernel

theorem rowEval11329 (x : Key → ℝ) : Integer.Sparse.eval row11329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11329, Integer.Sparse.eval_collectBalanced, rawRowCheck11329]

def rawRow11330 : Integer.Sparse Key := [(key2649, -2), (key2654, -2), (key2654, -2), (key2738, -2), (key2898, -2), (key2898, -2), (key2748, -2), (key2748, -2), (key2905, -2), (key2905, -2), (key2913, -2), (key2913, -2), (key2619, 2), (key2642, 2), (key2642, 2), (key2674, 2), (key2796, 2), (key2796, 2), (key2729, 2), (key2729, 2), (key2832, 2), (key2832, 2), (key2883, 2), (key2883, 2)]

theorem rawRowCheck11330 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form17 = rawRow11330 := by decide +kernel

def row11330 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11330 : row11330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11330 := by decide +kernel

theorem rowEval11330 (x : Key → ℝ) : Integer.Sparse.eval row11330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11330, Integer.Sparse.eval_collectBalanced, rawRowCheck11330]

def rawRow11331 : Integer.Sparse Key := [(key2654, -2), (key2649, -2), (key2654, -2), (key2898, -2), (key2738, -2), (key2898, -2), (key2905, -2), (key2913, -2), (key2748, -2), (key2913, -2), (key2748, -2), (key2905, -2), (key2642, 2), (key2619, 2), (key2642, 2), (key2796, 2), (key2674, 2), (key2796, 2), (key2832, 2), (key2883, 2), (key2729, 2), (key2883, 2), (key2729, 2), (key2832, 2)]

theorem rawRowCheck11331 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form17 = rawRow11331 := by decide +kernel

def row11331 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11331 : row11331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11331 := by decide +kernel

theorem rowEval11331 (x : Key → ℝ) : Integer.Sparse.eval row11331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11331, Integer.Sparse.eval_collectBalanced, rawRowCheck11331]

def rawRow11332 : Integer.Sparse Key := [(key2654, -2), (key2654, -2), (key2649, -2), (key2898, -2), (key2898, -2), (key2738, -2), (key2913, -2), (key2905, -2), (key2913, -2), (key2748, -2), (key2905, -2), (key2748, -2), (key2642, 2), (key2642, 2), (key2619, 2), (key2796, 2), (key2796, 2), (key2674, 2), (key2883, 2), (key2832, 2), (key2883, 2), (key2729, 2), (key2832, 2), (key2729, 2)]

theorem rawRowCheck11332 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form17 = rawRow11332 := by decide +kernel

def row11332 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11332 : row11332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11332 := by decide +kernel

theorem rowEval11332 (x : Key → ℝ) : Integer.Sparse.eval row11332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11332, Integer.Sparse.eval_collectBalanced, rawRowCheck11332]

def rawRow11333 : Integer.Sparse Key := [(key2738, -2), (key2748, -2), (key2748, -2), (key2649, -2), (key2905, -2), (key2905, -2), (key2654, -2), (key2654, -2), (key2898, -2), (key2898, -2), (key2913, -2), (key2913, -2), (key2674, 2), (key2729, 2), (key2729, 2), (key2619, 2), (key2832, 2), (key2832, 2), (key2642, 2), (key2642, 2), (key2796, 2), (key2796, 2), (key2883, 2), (key2883, 2)]

theorem rawRowCheck11333 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form17 = rawRow11333 := by decide +kernel

def row11333 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11333 : row11333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11333 := by decide +kernel

theorem rowEval11333 (x : Key → ℝ) : Integer.Sparse.eval row11333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11333, Integer.Sparse.eval_collectBalanced, rawRowCheck11333]

def rawRow11334 : Integer.Sparse Key := [(key2748, -2), (key2738, -2), (key2748, -2), (key2905, -2), (key2649, -2), (key2905, -2), (key2898, -2), (key2913, -2), (key2654, -2), (key2913, -2), (key2654, -2), (key2898, -2), (key2729, 2), (key2674, 2), (key2729, 2), (key2832, 2), (key2619, 2), (key2832, 2), (key2796, 2), (key2883, 2), (key2642, 2), (key2883, 2), (key2642, 2), (key2796, 2)]

theorem rawRowCheck11334 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form17 = rawRow11334 := by decide +kernel

def row11334 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11334 : row11334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11334 := by decide +kernel

theorem rowEval11334 (x : Key → ℝ) : Integer.Sparse.eval row11334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11334, Integer.Sparse.eval_collectBalanced, rawRowCheck11334]

def rawRow11335 : Integer.Sparse Key := [(key2748, -2), (key2748, -2), (key2738, -2), (key2905, -2), (key2905, -2), (key2649, -2), (key2913, -2), (key2898, -2), (key2913, -2), (key2654, -2), (key2898, -2), (key2654, -2), (key2729, 2), (key2729, 2), (key2674, 2), (key2832, 2), (key2832, 2), (key2619, 2), (key2883, 2), (key2796, 2), (key2883, 2), (key2642, 2), (key2796, 2), (key2642, 2)]

theorem rawRowCheck11335 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form17 = rawRow11335 := by decide +kernel

def row11335 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11335 : row11335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11335 := by decide +kernel

theorem rowEval11335 (x : Key → ℝ) : Integer.Sparse.eval row11335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11335, Integer.Sparse.eval_collectBalanced, rawRowCheck11335]

def rawRow11336 : Integer.Sparse Key := [(key2898, -2), (key2905, -2), (key2913, -2), (key2654, -2), (key2748, -2), (key2913, -2), (key2649, -2), (key2654, -2), (key2738, -2), (key2898, -2), (key2748, -2), (key2905, -2), (key2796, 2), (key2832, 2), (key2883, 2), (key2642, 2), (key2729, 2), (key2883, 2), (key2619, 2), (key2642, 2), (key2674, 2), (key2796, 2), (key2729, 2), (key2832, 2)]

theorem rawRowCheck11336 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form17 = rawRow11336 := by decide +kernel

def row11336 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11336 : row11336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11336 := by decide +kernel

theorem rowEval11336 (x : Key → ℝ) : Integer.Sparse.eval row11336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11336, Integer.Sparse.eval_collectBalanced, rawRowCheck11336]

def rawRow11337 : Integer.Sparse Key := [(key2898, -2), (key2913, -2), (key2905, -2), (key2654, -2), (key2913, -2), (key2748, -2), (key2654, -2), (key2649, -2), (key2898, -2), (key2738, -2), (key2905, -2), (key2748, -2), (key2796, 2), (key2883, 2), (key2832, 2), (key2642, 2), (key2883, 2), (key2729, 2), (key2642, 2), (key2619, 2), (key2796, 2), (key2674, 2), (key2832, 2), (key2729, 2)]

theorem rawRowCheck11337 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form17 = rawRow11337 := by decide +kernel

def row11337 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11337 : row11337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11337 := by decide +kernel

theorem rowEval11337 (x : Key → ℝ) : Integer.Sparse.eval row11337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11337, Integer.Sparse.eval_collectBalanced, rawRowCheck11337]

def rawRow11338 : Integer.Sparse Key := [(key2905, -2), (key2898, -2), (key2913, -2), (key2748, -2), (key2654, -2), (key2913, -2), (key2738, -2), (key2748, -2), (key2649, -2), (key2905, -2), (key2654, -2), (key2898, -2), (key2832, 2), (key2796, 2), (key2883, 2), (key2729, 2), (key2642, 2), (key2883, 2), (key2674, 2), (key2729, 2), (key2619, 2), (key2832, 2), (key2642, 2), (key2796, 2)]

theorem rawRowCheck11338 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form17 = rawRow11338 := by decide +kernel

def row11338 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11338 : row11338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11338 := by decide +kernel

theorem rowEval11338 (x : Key → ℝ) : Integer.Sparse.eval row11338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck11338, Integer.Sparse.eval_collectBalanced, rawRowCheck11338]

def rawRow11339 : Integer.Sparse Key := [(key2905, -2), (key2913, -2), (key2898, -2), (key2748, -2), (key2913, -2), (key2654, -2), (key2748, -2), (key2738, -2), (key2905, -2), (key2649, -2), (key2898, -2), (key2654, -2), (key2832, 2), (key2883, 2), (key2796, 2), (key2729, 2), (key2883, 2), (key2642, 2), (key2729, 2), (key2674, 2), (key2832, 2), (key2619, 2), (key2796, 2), (key2642, 2)]

theorem rawRowCheck11339 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form17 = rawRow11339 := by decide +kernel

def row11339 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11339 : row11339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11339 := by decide +kernel

theorem rowEval11339 (x : Key → ℝ) : Integer.Sparse.eval row11339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11339, Integer.Sparse.eval_collectBalanced, rawRowCheck11339]

def rawRow11340 : Integer.Sparse Key := [(key2913, -2), (key2898, -2), (key2905, -2), (key2913, -2), (key2654, -2), (key2748, -2), (key2898, -2), (key2905, -2), (key2654, -2), (key2748, -2), (key2649, -2), (key2738, -2), (key2883, 2), (key2796, 2), (key2832, 2), (key2883, 2), (key2642, 2), (key2729, 2), (key2796, 2), (key2832, 2), (key2642, 2), (key2729, 2), (key2619, 2), (key2674, 2)]

theorem rawRowCheck11340 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form17 = rawRow11340 := by decide +kernel

def row11340 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11340 : row11340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11340 := by decide +kernel

theorem rowEval11340 (x : Key → ℝ) : Integer.Sparse.eval row11340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck11340, Integer.Sparse.eval_collectBalanced, rawRowCheck11340]

def rawRow11341 : Integer.Sparse Key := [(key2913, -2), (key2905, -2), (key2898, -2), (key2913, -2), (key2748, -2), (key2654, -2), (key2905, -2), (key2898, -2), (key2748, -2), (key2654, -2), (key2738, -2), (key2649, -2), (key2883, 2), (key2832, 2), (key2796, 2), (key2883, 2), (key2729, 2), (key2642, 2), (key2832, 2), (key2796, 2), (key2729, 2), (key2642, 2), (key2674, 2), (key2619, 2)]

theorem rawRowCheck11341 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form17 = rawRow11341 := by decide +kernel

def row11341 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

theorem rowCheck11341 : row11341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11341 := by decide +kernel

theorem rowEval11341 (x : Key → ℝ) : Integer.Sparse.eval row11341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck11341, Integer.Sparse.eval_collectBalanced, rawRowCheck11341]

def rawRow11342 : Integer.Sparse Key := [(key1003, 2), (key1017, 2), (key1020, 2), (key1038, 2), (key1125, 2), (key1200, 2), (key1073, 2), (key1077, 2), (key1152, 2), (key1213, 2), (key1172, 2), (key1223, 2), (key1003, -2), (key1007, -2), (key1020, -2), (key1038, -2), (key1042, -2), (key1116, -2), (key1194, -2), (key1128, -2), (key1200, -2), (key1077, -2), (key1156, -2), (key1213, -2)]

theorem rawRowCheck11342 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form18 = rawRow11342 := by decide +kernel

def row11342 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11342 : row11342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11342 := by decide +kernel

theorem rowEval11342 (x : Key → ℝ) : Integer.Sparse.eval row11342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11342, Integer.Sparse.eval_collectBalanced, rawRowCheck11342]

def rawRow11343 : Integer.Sparse Key := [(key1003, 2), (key1020, 2), (key1017, 2), (key1038, 2), (key1200, 2), (key1125, 2), (key1077, 2), (key1073, 2), (key1213, 2), (key1152, 2), (key1223, 2), (key1172, 2), (key1007, -2), (key1003, -2), (key1020, -2), (key1042, -2), (key1038, -2), (key1194, -2), (key1116, -2), (key1200, -2), (key1128, -2), (key1077, -2), (key1213, -2), (key1156, -2)]

theorem rawRowCheck11343 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form18 = rawRow11343 := by decide +kernel

def row11343 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11343 : row11343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11343 := by decide +kernel

theorem rowEval11343 (x : Key → ℝ) : Integer.Sparse.eval row11343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11343, Integer.Sparse.eval_collectBalanced, rawRowCheck11343]

def rawRow11344 : Integer.Sparse Key := [(key1017, 2), (key1003, 2), (key1020, 2), (key1125, 2), (key1038, 2), (key1200, 2), (key1152, 2), (key1172, 2), (key1073, 2), (key1223, 2), (key1077, 2), (key1213, 2), (key1003, -2), (key1020, -2), (key1007, -2), (key1116, -2), (key1128, -2), (key1038, -2), (key1200, -2), (key1042, -2), (key1194, -2), (key1156, -2), (key1077, -2), (key1213, -2)]

theorem rawRowCheck11344 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form18 = rawRow11344 := by decide +kernel

def row11344 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11344 : row11344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11344 := by decide +kernel

theorem rowEval11344 (x : Key → ℝ) : Integer.Sparse.eval row11344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11344, Integer.Sparse.eval_collectBalanced, rawRowCheck11344]

def rawRow11345 : Integer.Sparse Key := [(key1017, 2), (key1020, 2), (key1003, 2), (key1125, 2), (key1200, 2), (key1038, 2), (key1172, 2), (key1152, 2), (key1223, 2), (key1073, 2), (key1213, 2), (key1077, 2), (key1020, -2), (key1003, -2), (key1007, -2), (key1128, -2), (key1116, -2), (key1200, -2), (key1038, -2), (key1194, -2), (key1042, -2), (key1156, -2), (key1213, -2), (key1077, -2)]

theorem rawRowCheck11345 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form18 = rawRow11345 := by decide +kernel

def row11345 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11345 : row11345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11345 := by decide +kernel

theorem rowEval11345 (x : Key → ℝ) : Integer.Sparse.eval row11345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11345, Integer.Sparse.eval_collectBalanced, rawRowCheck11345]

def rawRow11346 : Integer.Sparse Key := [(key1020, 2), (key1003, 2), (key1017, 2), (key1200, 2), (key1038, 2), (key1125, 2), (key1213, 2), (key1223, 2), (key1077, 2), (key1172, 2), (key1073, 2), (key1152, 2), (key1007, -2), (key1020, -2), (key1003, -2), (key1194, -2), (key1200, -2), (key1042, -2), (key1128, -2), (key1038, -2), (key1116, -2), (key1213, -2), (key1077, -2), (key1156, -2)]

theorem rawRowCheck11346 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form18 = rawRow11346 := by decide +kernel

def row11346 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11346 : row11346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11346 := by decide +kernel

theorem rowEval11346 (x : Key → ℝ) : Integer.Sparse.eval row11346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11346, Integer.Sparse.eval_collectBalanced, rawRowCheck11346]

def rawRow11347 : Integer.Sparse Key := [(key1020, 2), (key1017, 2), (key1003, 2), (key1200, 2), (key1125, 2), (key1038, 2), (key1223, 2), (key1213, 2), (key1172, 2), (key1077, 2), (key1152, 2), (key1073, 2), (key1020, -2), (key1007, -2), (key1003, -2), (key1200, -2), (key1194, -2), (key1128, -2), (key1042, -2), (key1116, -2), (key1038, -2), (key1213, -2), (key1156, -2), (key1077, -2)]

theorem rawRowCheck11347 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form18 = rawRow11347 := by decide +kernel

def row11347 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11347 : row11347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11347 := by decide +kernel

theorem rowEval11347 (x : Key → ℝ) : Integer.Sparse.eval row11347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11347, Integer.Sparse.eval_collectBalanced, rawRowCheck11347]

def rawRow11348 : Integer.Sparse Key := [(key1038, 2), (key1073, 2), (key1077, 2), (key1003, 2), (key1152, 2), (key1213, 2), (key1017, 2), (key1020, 2), (key1125, 2), (key1200, 2), (key1172, 2), (key1223, 2), (key1038, -2), (key1042, -2), (key1077, -2), (key1003, -2), (key1007, -2), (key1116, -2), (key1194, -2), (key1156, -2), (key1213, -2), (key1020, -2), (key1128, -2), (key1200, -2)]

theorem rawRowCheck11348 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form18 = rawRow11348 := by decide +kernel

def row11348 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11348 : row11348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11348 := by decide +kernel

theorem rowEval11348 (x : Key → ℝ) : Integer.Sparse.eval row11348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11348, Integer.Sparse.eval_collectBalanced, rawRowCheck11348]

def rawRow11349 : Integer.Sparse Key := [(key1038, 2), (key1077, 2), (key1073, 2), (key1003, 2), (key1213, 2), (key1152, 2), (key1020, 2), (key1017, 2), (key1200, 2), (key1125, 2), (key1223, 2), (key1172, 2), (key1042, -2), (key1038, -2), (key1077, -2), (key1007, -2), (key1003, -2), (key1194, -2), (key1116, -2), (key1213, -2), (key1156, -2), (key1020, -2), (key1200, -2), (key1128, -2)]

theorem rawRowCheck11349 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form18 = rawRow11349 := by decide +kernel

def row11349 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11349 : row11349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11349 := by decide +kernel

theorem rowEval11349 (x : Key → ℝ) : Integer.Sparse.eval row11349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11349, Integer.Sparse.eval_collectBalanced, rawRowCheck11349]

def rawRow11350 : Integer.Sparse Key := [(key1073, 2), (key1038, 2), (key1077, 2), (key1152, 2), (key1003, 2), (key1213, 2), (key1125, 2), (key1172, 2), (key1017, 2), (key1223, 2), (key1020, 2), (key1200, 2), (key1038, -2), (key1077, -2), (key1042, -2), (key1116, -2), (key1156, -2), (key1003, -2), (key1213, -2), (key1007, -2), (key1194, -2), (key1128, -2), (key1020, -2), (key1200, -2)]

theorem rawRowCheck11350 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form18 = rawRow11350 := by decide +kernel

def row11350 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11350 : row11350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11350 := by decide +kernel

theorem rowEval11350 (x : Key → ℝ) : Integer.Sparse.eval row11350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11350, Integer.Sparse.eval_collectBalanced, rawRowCheck11350]

def rawRow11351 : Integer.Sparse Key := [(key1073, 2), (key1077, 2), (key1038, 2), (key1152, 2), (key1213, 2), (key1003, 2), (key1172, 2), (key1125, 2), (key1223, 2), (key1017, 2), (key1200, 2), (key1020, 2), (key1077, -2), (key1038, -2), (key1042, -2), (key1156, -2), (key1116, -2), (key1213, -2), (key1003, -2), (key1194, -2), (key1007, -2), (key1128, -2), (key1200, -2), (key1020, -2)]

theorem rawRowCheck11351 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form18 = rawRow11351 := by decide +kernel

def row11351 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11351 : row11351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11351 := by decide +kernel

theorem rowEval11351 (x : Key → ℝ) : Integer.Sparse.eval row11351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11351, Integer.Sparse.eval_collectBalanced, rawRowCheck11351]

def rawRow11352 : Integer.Sparse Key := [(key1077, 2), (key1038, 2), (key1073, 2), (key1213, 2), (key1003, 2), (key1152, 2), (key1200, 2), (key1223, 2), (key1020, 2), (key1172, 2), (key1017, 2), (key1125, 2), (key1042, -2), (key1077, -2), (key1038, -2), (key1194, -2), (key1213, -2), (key1007, -2), (key1156, -2), (key1003, -2), (key1116, -2), (key1200, -2), (key1020, -2), (key1128, -2)]

theorem rawRowCheck11352 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form18 = rawRow11352 := by decide +kernel

def row11352 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11352 : row11352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11352 := by decide +kernel

theorem rowEval11352 (x : Key → ℝ) : Integer.Sparse.eval row11352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11352, Integer.Sparse.eval_collectBalanced, rawRowCheck11352]

def rawRow11353 : Integer.Sparse Key := [(key1077, 2), (key1073, 2), (key1038, 2), (key1213, 2), (key1152, 2), (key1003, 2), (key1223, 2), (key1200, 2), (key1172, 2), (key1020, 2), (key1125, 2), (key1017, 2), (key1077, -2), (key1042, -2), (key1038, -2), (key1213, -2), (key1194, -2), (key1156, -2), (key1007, -2), (key1116, -2), (key1003, -2), (key1200, -2), (key1128, -2), (key1020, -2)]

theorem rawRowCheck11353 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form18 = rawRow11353 := by decide +kernel

def row11353 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11353 : row11353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11353 := by decide +kernel

theorem rowEval11353 (x : Key → ℝ) : Integer.Sparse.eval row11353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11353, Integer.Sparse.eval_collectBalanced, rawRowCheck11353]

def rawRow11354 : Integer.Sparse Key := [(key1125, 2), (key1152, 2), (key1172, 2), (key1017, 2), (key1073, 2), (key1223, 2), (key1003, 2), (key1020, 2), (key1038, 2), (key1200, 2), (key1077, 2), (key1213, 2), (key1116, -2), (key1128, -2), (key1156, -2), (key1003, -2), (key1020, -2), (key1038, -2), (key1200, -2), (key1077, -2), (key1213, -2), (key1007, -2), (key1042, -2), (key1194, -2)]

theorem rawRowCheck11354 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form18 = rawRow11354 := by decide +kernel

def row11354 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11354 : row11354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11354 := by decide +kernel

theorem rowEval11354 (x : Key → ℝ) : Integer.Sparse.eval row11354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11354, Integer.Sparse.eval_collectBalanced, rawRowCheck11354]

def rawRow11355 : Integer.Sparse Key := [(key1125, 2), (key1172, 2), (key1152, 2), (key1017, 2), (key1223, 2), (key1073, 2), (key1020, 2), (key1003, 2), (key1200, 2), (key1038, 2), (key1213, 2), (key1077, 2), (key1128, -2), (key1116, -2), (key1156, -2), (key1020, -2), (key1003, -2), (key1200, -2), (key1038, -2), (key1213, -2), (key1077, -2), (key1007, -2), (key1194, -2), (key1042, -2)]

theorem rawRowCheck11355 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form18 = rawRow11355 := by decide +kernel

def row11355 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11355 : row11355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11355 := by decide +kernel

theorem rowEval11355 (x : Key → ℝ) : Integer.Sparse.eval row11355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11355, Integer.Sparse.eval_collectBalanced, rawRowCheck11355]

def rawRow11356 : Integer.Sparse Key := [(key1152, 2), (key1125, 2), (key1172, 2), (key1073, 2), (key1017, 2), (key1223, 2), (key1038, 2), (key1077, 2), (key1003, 2), (key1213, 2), (key1020, 2), (key1200, 2), (key1116, -2), (key1156, -2), (key1128, -2), (key1038, -2), (key1077, -2), (key1003, -2), (key1213, -2), (key1020, -2), (key1200, -2), (key1042, -2), (key1007, -2), (key1194, -2)]

theorem rawRowCheck11356 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form18 = rawRow11356 := by decide +kernel

def row11356 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11356 : row11356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11356 := by decide +kernel

theorem rowEval11356 (x : Key → ℝ) : Integer.Sparse.eval row11356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11356, Integer.Sparse.eval_collectBalanced, rawRowCheck11356]

def rawRow11357 : Integer.Sparse Key := [(key1152, 2), (key1172, 2), (key1125, 2), (key1073, 2), (key1223, 2), (key1017, 2), (key1077, 2), (key1038, 2), (key1213, 2), (key1003, 2), (key1200, 2), (key1020, 2), (key1156, -2), (key1116, -2), (key1128, -2), (key1077, -2), (key1038, -2), (key1213, -2), (key1003, -2), (key1200, -2), (key1020, -2), (key1042, -2), (key1194, -2), (key1007, -2)]

theorem rawRowCheck11357 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form18 = rawRow11357 := by decide +kernel

def row11357 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11357 : row11357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11357 := by decide +kernel

theorem rowEval11357 (x : Key → ℝ) : Integer.Sparse.eval row11357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11357, Integer.Sparse.eval_collectBalanced, rawRowCheck11357]

def rawRow11358 : Integer.Sparse Key := [(key1172, 2), (key1125, 2), (key1152, 2), (key1223, 2), (key1017, 2), (key1073, 2), (key1200, 2), (key1213, 2), (key1020, 2), (key1077, 2), (key1003, 2), (key1038, 2), (key1128, -2), (key1156, -2), (key1116, -2), (key1200, -2), (key1213, -2), (key1020, -2), (key1077, -2), (key1003, -2), (key1038, -2), (key1194, -2), (key1007, -2), (key1042, -2)]

theorem rawRowCheck11358 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form18 = rawRow11358 := by decide +kernel

def row11358 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11358 : row11358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11358 := by decide +kernel

theorem rowEval11358 (x : Key → ℝ) : Integer.Sparse.eval row11358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11358, Integer.Sparse.eval_collectBalanced, rawRowCheck11358]

def rawRow11359 : Integer.Sparse Key := [(key1172, 2), (key1152, 2), (key1125, 2), (key1223, 2), (key1073, 2), (key1017, 2), (key1213, 2), (key1200, 2), (key1077, 2), (key1020, 2), (key1038, 2), (key1003, 2), (key1156, -2), (key1128, -2), (key1116, -2), (key1213, -2), (key1200, -2), (key1077, -2), (key1020, -2), (key1038, -2), (key1003, -2), (key1194, -2), (key1042, -2), (key1007, -2)]

theorem rawRowCheck11359 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form18 = rawRow11359 := by decide +kernel

def row11359 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11359 : row11359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11359 := by decide +kernel

theorem rowEval11359 (x : Key → ℝ) : Integer.Sparse.eval row11359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11359, Integer.Sparse.eval_collectBalanced, rawRowCheck11359]

def rawRow11360 : Integer.Sparse Key := [(key1200, 2), (key1213, 2), (key1223, 2), (key1020, 2), (key1077, 2), (key1172, 2), (key1003, 2), (key1017, 2), (key1038, 2), (key1125, 2), (key1073, 2), (key1152, 2), (key1194, -2), (key1200, -2), (key1213, -2), (key1007, -2), (key1020, -2), (key1042, -2), (key1128, -2), (key1077, -2), (key1156, -2), (key1003, -2), (key1038, -2), (key1116, -2)]

theorem rawRowCheck11360 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form18 = rawRow11360 := by decide +kernel

def row11360 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11360 : row11360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11360 := by decide +kernel

theorem rowEval11360 (x : Key → ℝ) : Integer.Sparse.eval row11360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11360, Integer.Sparse.eval_collectBalanced, rawRowCheck11360]

def rawRow11361 : Integer.Sparse Key := [(key1200, 2), (key1223, 2), (key1213, 2), (key1020, 2), (key1172, 2), (key1077, 2), (key1017, 2), (key1003, 2), (key1125, 2), (key1038, 2), (key1152, 2), (key1073, 2), (key1200, -2), (key1194, -2), (key1213, -2), (key1020, -2), (key1007, -2), (key1128, -2), (key1042, -2), (key1156, -2), (key1077, -2), (key1003, -2), (key1116, -2), (key1038, -2)]

theorem rawRowCheck11361 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form18 = rawRow11361 := by decide +kernel

def row11361 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11361 : row11361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11361 := by decide +kernel

theorem rowEval11361 (x : Key → ℝ) : Integer.Sparse.eval row11361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11361, Integer.Sparse.eval_collectBalanced, rawRowCheck11361]

def rawRow11362 : Integer.Sparse Key := [(key1213, 2), (key1200, 2), (key1223, 2), (key1077, 2), (key1020, 2), (key1172, 2), (key1038, 2), (key1073, 2), (key1003, 2), (key1152, 2), (key1017, 2), (key1125, 2), (key1194, -2), (key1213, -2), (key1200, -2), (key1042, -2), (key1077, -2), (key1007, -2), (key1156, -2), (key1020, -2), (key1128, -2), (key1038, -2), (key1003, -2), (key1116, -2)]

theorem rawRowCheck11362 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form18 = rawRow11362 := by decide +kernel

def row11362 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11362 : row11362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11362 := by decide +kernel

theorem rowEval11362 (x : Key → ℝ) : Integer.Sparse.eval row11362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11362, Integer.Sparse.eval_collectBalanced, rawRowCheck11362]

def rawRow11363 : Integer.Sparse Key := [(key1213, 2), (key1223, 2), (key1200, 2), (key1077, 2), (key1172, 2), (key1020, 2), (key1073, 2), (key1038, 2), (key1152, 2), (key1003, 2), (key1125, 2), (key1017, 2), (key1213, -2), (key1194, -2), (key1200, -2), (key1077, -2), (key1042, -2), (key1156, -2), (key1007, -2), (key1128, -2), (key1020, -2), (key1038, -2), (key1116, -2), (key1003, -2)]

theorem rawRowCheck11363 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form18 = rawRow11363 := by decide +kernel

def row11363 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11363 : row11363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11363 := by decide +kernel

theorem rowEval11363 (x : Key → ℝ) : Integer.Sparse.eval row11363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11363, Integer.Sparse.eval_collectBalanced, rawRowCheck11363]

def rawRow11364 : Integer.Sparse Key := [(key1223, 2), (key1200, 2), (key1213, 2), (key1172, 2), (key1020, 2), (key1077, 2), (key1125, 2), (key1152, 2), (key1017, 2), (key1073, 2), (key1003, 2), (key1038, 2), (key1200, -2), (key1213, -2), (key1194, -2), (key1128, -2), (key1156, -2), (key1020, -2), (key1077, -2), (key1007, -2), (key1042, -2), (key1116, -2), (key1003, -2), (key1038, -2)]

theorem rawRowCheck11364 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form18 = rawRow11364 := by decide +kernel

def row11364 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11364 : row11364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11364 := by decide +kernel

theorem rowEval11364 (x : Key → ℝ) : Integer.Sparse.eval row11364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11364, Integer.Sparse.eval_collectBalanced, rawRowCheck11364]

def rawRow11365 : Integer.Sparse Key := [(key1223, 2), (key1213, 2), (key1200, 2), (key1172, 2), (key1077, 2), (key1020, 2), (key1152, 2), (key1125, 2), (key1073, 2), (key1017, 2), (key1038, 2), (key1003, 2), (key1213, -2), (key1200, -2), (key1194, -2), (key1156, -2), (key1128, -2), (key1077, -2), (key1020, -2), (key1042, -2), (key1007, -2), (key1116, -2), (key1038, -2), (key1003, -2)]

theorem rawRowCheck11365 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form18 = rawRow11365 := by decide +kernel

def row11365 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

theorem rowCheck11365 : row11365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11365 := by decide +kernel

theorem rowEval11365 (x : Key → ℝ) : Integer.Sparse.eval row11365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11365, Integer.Sparse.eval_collectBalanced, rawRowCheck11365]

def rawRow11366 : Integer.Sparse Key := [(key1007, 2), (key1020, 2), (key1020, 2), (key1042, 2), (key1128, 2), (key1128, 2), (key1077, 2), (key1077, 2), (key1156, 2), (key1156, 2), (key1172, 2), (key1172, 2), (key1003, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1152, -2)]

theorem rawRowCheck11366 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form18 = rawRow11366 := by decide +kernel

def row11366 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11366 : row11366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11366 := by decide +kernel

theorem rowEval11366 (x : Key → ℝ) : Integer.Sparse.eval row11366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11366, Integer.Sparse.eval_collectBalanced, rawRowCheck11366]

def rawRow11367 : Integer.Sparse Key := [(key1020, 2), (key1007, 2), (key1020, 2), (key1128, 2), (key1042, 2), (key1128, 2), (key1156, 2), (key1172, 2), (key1077, 2), (key1172, 2), (key1077, 2), (key1156, 2), (key1003, -2), (key1017, -2), (key1003, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, -2), (key1073, -2), (key1152, -2)]

theorem rawRowCheck11367 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form18 = rawRow11367 := by decide +kernel

def row11367 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11367 : row11367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11367 := by decide +kernel

theorem rowEval11367 (x : Key → ℝ) : Integer.Sparse.eval row11367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11367, Integer.Sparse.eval_collectBalanced, rawRowCheck11367]

def rawRow11368 : Integer.Sparse Key := [(key1020, 2), (key1020, 2), (key1007, 2), (key1128, 2), (key1128, 2), (key1042, 2), (key1172, 2), (key1156, 2), (key1172, 2), (key1077, 2), (key1156, 2), (key1077, 2), (key1017, -2), (key1003, -2), (key1003, -2), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1152, -2), (key1152, -2), (key1073, -2)]

theorem rawRowCheck11368 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form18 = rawRow11368 := by decide +kernel

def row11368 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11368 : row11368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11368 := by decide +kernel

theorem rowEval11368 (x : Key → ℝ) : Integer.Sparse.eval row11368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11368, Integer.Sparse.eval_collectBalanced, rawRowCheck11368]

def rawRow11369 : Integer.Sparse Key := [(key1042, 2), (key1077, 2), (key1077, 2), (key1007, 2), (key1156, 2), (key1156, 2), (key1020, 2), (key1020, 2), (key1128, 2), (key1128, 2), (key1172, 2), (key1172, 2), (key1038, -2), (key1038, -2), (key1073, -2), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1125, -2)]

theorem rawRowCheck11369 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form18 = rawRow11369 := by decide +kernel

def row11369 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11369 : row11369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11369 := by decide +kernel

theorem rowEval11369 (x : Key → ℝ) : Integer.Sparse.eval row11369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11369, Integer.Sparse.eval_collectBalanced, rawRowCheck11369]

def rawRow11370 : Integer.Sparse Key := [(key1077, 2), (key1042, 2), (key1077, 2), (key1156, 2), (key1007, 2), (key1156, 2), (key1128, 2), (key1172, 2), (key1020, 2), (key1172, 2), (key1020, 2), (key1128, 2), (key1038, -2), (key1073, -2), (key1038, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1125, -2), (key1017, -2), (key1125, -2)]

theorem rawRowCheck11370 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form18 = rawRow11370 := by decide +kernel

def row11370 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11370 : row11370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11370 := by decide +kernel

theorem rowEval11370 (x : Key → ℝ) : Integer.Sparse.eval row11370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11370, Integer.Sparse.eval_collectBalanced, rawRowCheck11370]

def rawRow11371 : Integer.Sparse Key := [(key1077, 2), (key1077, 2), (key1042, 2), (key1156, 2), (key1156, 2), (key1007, 2), (key1172, 2), (key1128, 2), (key1172, 2), (key1020, 2), (key1128, 2), (key1020, 2), (key1073, -2), (key1038, -2), (key1038, -2), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1125, -2), (key1125, -2), (key1017, -2)]

theorem rawRowCheck11371 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form18 = rawRow11371 := by decide +kernel

def row11371 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11371 : row11371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11371 := by decide +kernel

theorem rowEval11371 (x : Key → ℝ) : Integer.Sparse.eval row11371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11371, Integer.Sparse.eval_collectBalanced, rawRowCheck11371]

def rawRow11372 : Integer.Sparse Key := [(key1128, 2), (key1156, 2), (key1172, 2), (key1020, 2), (key1077, 2), (key1172, 2), (key1007, 2), (key1020, 2), (key1042, 2), (key1128, 2), (key1077, 2), (key1156, 2), (key1116, -2), (key1125, -2), (key1152, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1003, -2), (key1038, -2), (key1116, -2)]

theorem rawRowCheck11372 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form18 = rawRow11372 := by decide +kernel

def row11372 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11372 : row11372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11372 := by decide +kernel

theorem rowEval11372 (x : Key → ℝ) : Integer.Sparse.eval row11372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11372, Integer.Sparse.eval_collectBalanced, rawRowCheck11372]

def rawRow11373 : Integer.Sparse Key := [(key1128, 2), (key1172, 2), (key1156, 2), (key1020, 2), (key1172, 2), (key1077, 2), (key1020, 2), (key1007, 2), (key1128, 2), (key1042, 2), (key1156, 2), (key1077, 2), (key1125, -2), (key1116, -2), (key1152, -2), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1003, -2), (key1116, -2), (key1038, -2)]

theorem rawRowCheck11373 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form18 = rawRow11373 := by decide +kernel

def row11373 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11373 : row11373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11373 := by decide +kernel

theorem rowEval11373 (x : Key → ℝ) : Integer.Sparse.eval row11373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11373, Integer.Sparse.eval_collectBalanced, rawRowCheck11373]

def rawRow11374 : Integer.Sparse Key := [(key1156, 2), (key1128, 2), (key1172, 2), (key1077, 2), (key1020, 2), (key1172, 2), (key1042, 2), (key1077, 2), (key1007, 2), (key1156, 2), (key1020, 2), (key1128, 2), (key1116, -2), (key1152, -2), (key1125, -2), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1038, -2), (key1003, -2), (key1116, -2)]

theorem rawRowCheck11374 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form18 = rawRow11374 := by decide +kernel

def row11374 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11374 : row11374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11374 := by decide +kernel

theorem rowEval11374 (x : Key → ℝ) : Integer.Sparse.eval row11374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck11374, Integer.Sparse.eval_collectBalanced, rawRowCheck11374]

def rawRow11375 : Integer.Sparse Key := [(key1156, 2), (key1172, 2), (key1128, 2), (key1077, 2), (key1172, 2), (key1020, 2), (key1077, 2), (key1042, 2), (key1156, 2), (key1007, 2), (key1128, 2), (key1020, 2), (key1152, -2), (key1116, -2), (key1125, -2), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1038, -2), (key1116, -2), (key1003, -2)]

theorem rawRowCheck11375 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form18 = rawRow11375 := by decide +kernel

def row11375 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11375 : row11375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11375 := by decide +kernel

theorem rowEval11375 (x : Key → ℝ) : Integer.Sparse.eval row11375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11375, Integer.Sparse.eval_collectBalanced, rawRowCheck11375]

def rawRow11376 : Integer.Sparse Key := [(key1172, 2), (key1128, 2), (key1156, 2), (key1172, 2), (key1020, 2), (key1077, 2), (key1128, 2), (key1156, 2), (key1020, 2), (key1077, 2), (key1007, 2), (key1042, 2), (key1125, -2), (key1152, -2), (key1116, -2), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1116, -2), (key1003, -2), (key1038, -2)]

theorem rawRowCheck11376 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form18 = rawRow11376 := by decide +kernel

def row11376 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11376 : row11376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11376 := by decide +kernel

theorem rowEval11376 (x : Key → ℝ) : Integer.Sparse.eval row11376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck11376, Integer.Sparse.eval_collectBalanced, rawRowCheck11376]

def rawRow11377 : Integer.Sparse Key := [(key1172, 2), (key1156, 2), (key1128, 2), (key1172, 2), (key1077, 2), (key1020, 2), (key1156, 2), (key1128, 2), (key1077, 2), (key1020, 2), (key1042, 2), (key1007, 2), (key1152, -2), (key1125, -2), (key1116, -2), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1116, -2), (key1038, -2), (key1003, -2)]

theorem rawRowCheck11377 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form18 = rawRow11377 := by decide +kernel

def row11377 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

theorem rowCheck11377 : row11377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11377 := by decide +kernel

theorem rowEval11377 (x : Key → ℝ) : Integer.Sparse.eval row11377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck11377, Integer.Sparse.eval_collectBalanced, rawRowCheck11377]

def rawRow11378 : Integer.Sparse Key := [(key2678, -4), (key2709, -4), (key2713, -4), (key2812, -4), (key2816, -4), (key2862, -4), (key2678, 6), (key2687, 6), (key2713, 6), (key2816, 6)]

theorem rawRowCheck11378 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form19 = rawRow11378 := by decide +kernel

def row11378 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11378 : row11378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11378 := by decide +kernel

theorem rowEval11378 (x : Key → ℝ) : Integer.Sparse.eval row11378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11378, Integer.Sparse.eval_collectBalanced, rawRowCheck11378]

def rawRow11379 : Integer.Sparse Key := [(key2678, -4), (key2713, -4), (key2709, -4), (key2816, -4), (key2812, -4), (key2862, -4), (key2687, 6), (key2678, 6), (key2713, 6), (key2816, 6)]

theorem rawRowCheck11379 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form19 = rawRow11379 := by decide +kernel

def row11379 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11379 : row11379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11379 := by decide +kernel

theorem rowEval11379 (x : Key → ℝ) : Integer.Sparse.eval row11379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11379, Integer.Sparse.eval_collectBalanced, rawRowCheck11379]

def rawRow11380 : Integer.Sparse Key := [(key2709, -4), (key2678, -4), (key2713, -4), (key2812, -4), (key2862, -4), (key2816, -4), (key2678, 6), (key2713, 6), (key2687, 6), (key2816, 6)]

theorem rawRowCheck11380 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form19 = rawRow11380 := by decide +kernel

def row11380 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11380 : row11380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11380 := by decide +kernel

theorem rowEval11380 (x : Key → ℝ) : Integer.Sparse.eval row11380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11380, Integer.Sparse.eval_collectBalanced, rawRowCheck11380]

def rawRow11381 : Integer.Sparse Key := [(key2709, -4), (key2713, -4), (key2678, -4), (key2862, -4), (key2812, -4), (key2816, -4), (key2713, 6), (key2678, 6), (key2687, 6), (key2816, 6)]

theorem rawRowCheck11381 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form19 = rawRow11381 := by decide +kernel

def row11381 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11381 : row11381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11381 := by decide +kernel

theorem rowEval11381 (x : Key → ℝ) : Integer.Sparse.eval row11381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11381, Integer.Sparse.eval_collectBalanced, rawRowCheck11381]

def rawRow11382 : Integer.Sparse Key := [(key2713, -4), (key2678, -4), (key2709, -4), (key2816, -4), (key2862, -4), (key2812, -4), (key2687, 6), (key2713, 6), (key2678, 6), (key2816, 6)]

theorem rawRowCheck11382 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form19 = rawRow11382 := by decide +kernel

def row11382 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11382 : row11382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11382 := by decide +kernel

theorem rowEval11382 (x : Key → ℝ) : Integer.Sparse.eval row11382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11382, Integer.Sparse.eval_collectBalanced, rawRowCheck11382]

def rawRow11383 : Integer.Sparse Key := [(key2713, -4), (key2709, -4), (key2678, -4), (key2862, -4), (key2816, -4), (key2812, -4), (key2713, 6), (key2687, 6), (key2678, 6), (key2816, 6)]

theorem rawRowCheck11383 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form19 = rawRow11383 := by decide +kernel

def row11383 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11383 : row11383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11383 := by decide +kernel

theorem rowEval11383 (x : Key → ℝ) : Integer.Sparse.eval row11383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11383, Integer.Sparse.eval_collectBalanced, rawRowCheck11383]

def rawRow11384 : Integer.Sparse Key := [(key2678, -4), (key2812, -4), (key2816, -4), (key2709, -4), (key2713, -4), (key2862, -4), (key2678, 6), (key2687, 6), (key2816, 6), (key2713, 6)]

theorem rawRowCheck11384 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form19 = rawRow11384 := by decide +kernel

def row11384 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11384 : row11384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11384 := by decide +kernel

theorem rowEval11384 (x : Key → ℝ) : Integer.Sparse.eval row11384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11384, Integer.Sparse.eval_collectBalanced, rawRowCheck11384]

def rawRow11385 : Integer.Sparse Key := [(key2678, -4), (key2816, -4), (key2812, -4), (key2713, -4), (key2709, -4), (key2862, -4), (key2687, 6), (key2678, 6), (key2816, 6), (key2713, 6)]

theorem rawRowCheck11385 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form19 = rawRow11385 := by decide +kernel

def row11385 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11385 : row11385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11385 := by decide +kernel

theorem rowEval11385 (x : Key → ℝ) : Integer.Sparse.eval row11385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11385, Integer.Sparse.eval_collectBalanced, rawRowCheck11385]

def rawRow11386 : Integer.Sparse Key := [(key2812, -4), (key2678, -4), (key2816, -4), (key2709, -4), (key2862, -4), (key2713, -4), (key2678, 6), (key2816, 6), (key2687, 6), (key2713, 6)]

theorem rawRowCheck11386 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form19 = rawRow11386 := by decide +kernel

def row11386 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11386 : row11386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11386 := by decide +kernel

theorem rowEval11386 (x : Key → ℝ) : Integer.Sparse.eval row11386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11386, Integer.Sparse.eval_collectBalanced, rawRowCheck11386]

def rawRow11387 : Integer.Sparse Key := [(key2812, -4), (key2816, -4), (key2678, -4), (key2862, -4), (key2709, -4), (key2713, -4), (key2816, 6), (key2678, 6), (key2687, 6), (key2713, 6)]

theorem rawRowCheck11387 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form19 = rawRow11387 := by decide +kernel

def row11387 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11387 : row11387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11387 := by decide +kernel

theorem rowEval11387 (x : Key → ℝ) : Integer.Sparse.eval row11387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11387, Integer.Sparse.eval_collectBalanced, rawRowCheck11387]

def rawRow11388 : Integer.Sparse Key := [(key2816, -4), (key2678, -4), (key2812, -4), (key2713, -4), (key2862, -4), (key2709, -4), (key2687, 6), (key2816, 6), (key2678, 6), (key2713, 6)]

theorem rawRowCheck11388 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form19 = rawRow11388 := by decide +kernel

def row11388 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11388 : row11388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11388 := by decide +kernel

theorem rowEval11388 (x : Key → ℝ) : Integer.Sparse.eval row11388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck11388, Integer.Sparse.eval_collectBalanced, rawRowCheck11388]

def rawRow11389 : Integer.Sparse Key := [(key2816, -4), (key2812, -4), (key2678, -4), (key2862, -4), (key2713, -4), (key2709, -4), (key2816, 6), (key2687, 6), (key2678, 6), (key2713, 6)]

theorem rawRowCheck11389 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form19 = rawRow11389 := by decide +kernel

def row11389 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11389 : row11389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11389 := by decide +kernel

theorem rowEval11389 (x : Key → ℝ) : Integer.Sparse.eval row11389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck11389, Integer.Sparse.eval_collectBalanced, rawRowCheck11389]

def rawRow11390 : Integer.Sparse Key := [(key2709, -4), (key2812, -4), (key2862, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, 6), (key2713, 6), (key2816, 6), (key2687, 6)]

theorem rawRowCheck11390 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form19 = rawRow11390 := by decide +kernel

def row11390 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11390 : row11390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11390 := by decide +kernel

theorem rowEval11390 (x : Key → ℝ) : Integer.Sparse.eval row11390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11390, Integer.Sparse.eval_collectBalanced, rawRowCheck11390]

def rawRow11391 : Integer.Sparse Key := [(key2709, -4), (key2862, -4), (key2812, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, 6), (key2678, 6), (key2816, 6), (key2687, 6)]

theorem rawRowCheck11391 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form19 = rawRow11391 := by decide +kernel

def row11391 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

theorem rowCheck11391 : row11391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11391 := by decide +kernel

theorem rowEval11391 (x : Key → ℝ) : Integer.Sparse.eval row11391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck11391, Integer.Sparse.eval_collectBalanced, rawRowCheck11391]

end MUB6.Certificate.GramRows

end OAI

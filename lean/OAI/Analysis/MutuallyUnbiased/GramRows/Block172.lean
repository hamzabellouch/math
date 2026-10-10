import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
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

def rawRow18944 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2559, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2453, 6)]

theorem rawRowCheck18944 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18944 := by decide +kernel

def row18944 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18944 : row18944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18944 := by decide +kernel

theorem rowEval18944 (x : Key → ℝ) : Integer.Sparse.eval row18944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18944, Integer.Sparse.eval_collectBalanced, rawRowCheck18944]

def rawRow18945 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2559, 6), (key2514, 6), (key2514, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2453, 6)]

theorem rawRowCheck18945 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18945 := by decide +kernel

def row18945 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18945 : row18945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18945 := by decide +kernel

theorem rowEval18945 (x : Key → ℝ) : Integer.Sparse.eval row18945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18945, Integer.Sparse.eval_collectBalanced, rawRowCheck18945]

def rawRow18946 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2354, 6), (key2358, 6), (key2449, 6), (key2529, 6), (key2514, 6), (key2559, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2529, 6)]

theorem rawRowCheck18946 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form0 = rawRow18946 := by decide +kernel

def row18946 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18946 : row18946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18946 := by decide +kernel

theorem rowEval18946 (x : Key → ℝ) : Integer.Sparse.eval row18946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18946, Integer.Sparse.eval_collectBalanced, rawRowCheck18946]

def rawRow18947 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2358, 6), (key2354, 6), (key2529, 6), (key2449, 6), (key2559, 6), (key2514, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2529, 6), (key2453, 6)]

theorem rawRowCheck18947 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form0 = rawRow18947 := by decide +kernel

def row18947 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18947 : row18947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18947 := by decide +kernel

theorem rowEval18947 (x : Key → ℝ) : Integer.Sparse.eval row18947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18947, Integer.Sparse.eval_collectBalanced, rawRowCheck18947]

def rawRow18948 : Integer.Sparse Key := [(key2449, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2354, 6), (key2559, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2529, 6)]

theorem rawRowCheck18948 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form0 = rawRow18948 := by decide +kernel

def row18948 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18948 : row18948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18948 := by decide +kernel

theorem rowEval18948 (x : Key → ℝ) : Integer.Sparse.eval row18948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18948, Integer.Sparse.eval_collectBalanced, rawRowCheck18948]

def rawRow18949 : Integer.Sparse Key := [(key2514, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2559, 6), (key2354, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2358, 6)]

theorem rawRowCheck18949 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form0 = rawRow18949 := by decide +kernel

def row18949 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18949 : row18949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18949 := by decide +kernel

theorem rowEval18949 (x : Key → ℝ) : Integer.Sparse.eval row18949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18949, Integer.Sparse.eval_collectBalanced, rawRowCheck18949]

def rawRow18950 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2529, 6), (key2559, 6), (key2358, 6), (key2514, 6), (key2354, 6), (key2449, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2358, 6), (key2453, 6)]

theorem rawRowCheck18950 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form0 = rawRow18950 := by decide +kernel

def row18950 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18950 : row18950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18950 := by decide +kernel

theorem rowEval18950 (x : Key → ℝ) : Integer.Sparse.eval row18950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18950, Integer.Sparse.eval_collectBalanced, rawRowCheck18950]

def rawRow18951 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2559, 6), (key2529, 6), (key2514, 6), (key2358, 6), (key2449, 6), (key2354, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2358, 6)]

theorem rawRowCheck18951 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form0 = rawRow18951 := by decide +kernel

def row18951 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18951 : row18951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18951 := by decide +kernel

theorem rowEval18951 (x : Key → ℝ) : Integer.Sparse.eval row18951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18951, Integer.Sparse.eval_collectBalanced, rawRowCheck18951]

def rawRow18952 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2529, 6), (key2529, 6), (key2559, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2354, 6), (key2449, 6), (key2449, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2453, 6)]

theorem rawRowCheck18952 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18952 := by decide +kernel

def row18952 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18952 : row18952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18952 := by decide +kernel

theorem rowEval18952 (x : Key → ℝ) : Integer.Sparse.eval row18952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18952, Integer.Sparse.eval_collectBalanced, rawRowCheck18952]

def rawRow18953 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2559, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2354, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2453, 6)]

theorem rawRowCheck18953 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18953 := by decide +kernel

def row18953 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18953 : row18953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18953 := by decide +kernel

theorem rowEval18953 (x : Key → ℝ) : Integer.Sparse.eval row18953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18953, Integer.Sparse.eval_collectBalanced, rawRowCheck18953]

def rawRow18954 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2559, 6), (key2529, 6), (key2529, 6), (key2514, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2358, 6), (key2449, 6), (key2449, 6), (key2354, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2358, 6)]

theorem rawRowCheck18954 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18954 := by decide +kernel

def row18954 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18954 : row18954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18954 := by decide +kernel

theorem rowEval18954 (x : Key → ℝ) : Integer.Sparse.eval row18954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18954, Integer.Sparse.eval_collectBalanced, rawRowCheck18954]

def rawRow18955 : Integer.Sparse Key := [(key2529, 6), (key2529, 6), (key2529, 6), (key2559, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2514, 6), (key2354, 6), (key2449, 6), (key2449, 6), (key2449, 6)]

theorem rawRowCheck18955 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18955 := by decide +kernel

def row18955 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18955 : row18955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18955 := by decide +kernel

theorem rowEval18955 (x : Key → ℝ) : Integer.Sparse.eval row18955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18955, Integer.Sparse.eval_collectBalanced, rawRowCheck18955]

def rawRow18956 : Integer.Sparse Key := [(key2529, 6), (key2529, 6), (key2559, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2354, 6), (key2449, 6), (key2449, 6)]

theorem rawRowCheck18956 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18956 := by decide +kernel

def row18956 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18956 : row18956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18956 := by decide +kernel

theorem rowEval18956 (x : Key → ℝ) : Integer.Sparse.eval row18956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18956, Integer.Sparse.eval_collectBalanced, rawRowCheck18956]

def rawRow18957 : Integer.Sparse Key := [(key2529, 6), (key2559, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2354, 6), (key2449, 6)]

theorem rawRowCheck18957 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18957 := by decide +kernel

def row18957 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18957 : row18957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18957 := by decide +kernel

theorem rowEval18957 (x : Key → ℝ) : Integer.Sparse.eval row18957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18957, Integer.Sparse.eval_collectBalanced, rawRowCheck18957]

def rawRow18958 : Integer.Sparse Key := [(key2559, 6), (key2529, 6), (key2529, 6), (key2529, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2449, 6), (key2449, 6), (key2449, 6), (key2354, 6)]

theorem rawRowCheck18958 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18958 := by decide +kernel

def row18958 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

theorem rowCheck18958 : row18958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18958 := by decide +kernel

theorem rowEval18958 (x : Key → ℝ) : Integer.Sparse.eval row18958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18958, Integer.Sparse.eval_collectBalanced, rawRowCheck18958]

def rawRow18959 : Integer.Sparse Key := [(key969, 24), (key1083, 24), (key1083, 24), (key1083, 24), (key1177, 24)]

theorem rawRowCheck18959 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18959 := by decide +kernel

def row18959 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18959 : row18959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18959 := by decide +kernel

theorem rowEval18959 (x : Key → ℝ) : Integer.Sparse.eval row18959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18959, Integer.Sparse.eval_collectBalanced, rawRowCheck18959]

def rawRow18960 : Integer.Sparse Key := [(key969, 24), (key1083, 24), (key1083, 24), (key1177, 24), (key1083, 24)]

theorem rawRowCheck18960 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18960 := by decide +kernel

def row18960 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18960 : row18960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18960 := by decide +kernel

theorem rowEval18960 (x : Key → ℝ) : Integer.Sparse.eval row18960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18960, Integer.Sparse.eval_collectBalanced, rawRowCheck18960]

def rawRow18961 : Integer.Sparse Key := [(key969, 24), (key1083, 24), (key1177, 24), (key1083, 24), (key1083, 24)]

theorem rawRowCheck18961 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18961 := by decide +kernel

def row18961 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18961 : row18961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18961 := by decide +kernel

theorem rowEval18961 (x : Key → ℝ) : Integer.Sparse.eval row18961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18961, Integer.Sparse.eval_collectBalanced, rawRowCheck18961]

def rawRow18962 : Integer.Sparse Key := [(key969, 24), (key1177, 24), (key1083, 24), (key1083, 24), (key1083, 24)]

theorem rawRowCheck18962 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18962 := by decide +kernel

def row18962 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18962 : row18962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18962 := by decide +kernel

theorem rowEval18962 (x : Key → ℝ) : Integer.Sparse.eval row18962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18962, Integer.Sparse.eval_collectBalanced, rawRowCheck18962]

def rawRow18963 : Integer.Sparse Key := [(key1083, 24), (key969, 24), (key1083, 24), (key1083, 24), (key1177, 24)]

theorem rawRowCheck18963 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18963 := by decide +kernel

def row18963 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18963 : row18963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18963 := by decide +kernel

theorem rowEval18963 (x : Key → ℝ) : Integer.Sparse.eval row18963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18963, Integer.Sparse.eval_collectBalanced, rawRowCheck18963]

def rawRow18964 : Integer.Sparse Key := [(key1083, 24), (key969, 24), (key1083, 24), (key1177, 24), (key1083, 24)]

theorem rawRowCheck18964 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18964 := by decide +kernel

def row18964 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18964 : row18964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18964 := by decide +kernel

theorem rowEval18964 (x : Key → ℝ) : Integer.Sparse.eval row18964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18964, Integer.Sparse.eval_collectBalanced, rawRowCheck18964]

def rawRow18965 : Integer.Sparse Key := [(key1083, 24), (key969, 24), (key1177, 24), (key1083, 24), (key1083, 24)]

theorem rawRowCheck18965 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18965 := by decide +kernel

def row18965 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18965 : row18965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18965 := by decide +kernel

theorem rowEval18965 (x : Key → ℝ) : Integer.Sparse.eval row18965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18965, Integer.Sparse.eval_collectBalanced, rawRowCheck18965]

def rawRow18966 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key969, 24), (key1083, 24), (key1177, 24)]

theorem rawRowCheck18966 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form1 = rawRow18966 := by decide +kernel

def row18966 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18966 : row18966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18966 := by decide +kernel

theorem rowEval18966 (x : Key → ℝ) : Integer.Sparse.eval row18966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18966, Integer.Sparse.eval_collectBalanced, rawRowCheck18966]

def rawRow18967 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key969, 24), (key1177, 24), (key1083, 24)]

theorem rawRowCheck18967 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form1 = rawRow18967 := by decide +kernel

def row18967 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18967 : row18967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18967 := by decide +kernel

theorem rowEval18967 (x : Key → ℝ) : Integer.Sparse.eval row18967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18967, Integer.Sparse.eval_collectBalanced, rawRowCheck18967]

def rawRow18968 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1083, 24), (key969, 24), (key1177, 24)]

theorem rawRowCheck18968 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form1 = rawRow18968 := by decide +kernel

def row18968 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18968 : row18968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18968 := by decide +kernel

theorem rowEval18968 (x : Key → ℝ) : Integer.Sparse.eval row18968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18968, Integer.Sparse.eval_collectBalanced, rawRowCheck18968]

def rawRow18969 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1083, 24), (key1177, 24), (key969, 24)]

theorem rawRowCheck18969 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form1 = rawRow18969 := by decide +kernel

def row18969 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18969 : row18969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18969 := by decide +kernel

theorem rowEval18969 (x : Key → ℝ) : Integer.Sparse.eval row18969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18969, Integer.Sparse.eval_collectBalanced, rawRowCheck18969]

def rawRow18970 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1177, 24), (key969, 24), (key1083, 24)]

theorem rawRowCheck18970 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form1 = rawRow18970 := by decide +kernel

def row18970 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18970 : row18970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18970 := by decide +kernel

theorem rowEval18970 (x : Key → ℝ) : Integer.Sparse.eval row18970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18970, Integer.Sparse.eval_collectBalanced, rawRowCheck18970]

def rawRow18971 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1177, 24), (key1083, 24), (key969, 24)]

theorem rawRowCheck18971 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form1 = rawRow18971 := by decide +kernel

def row18971 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18971 : row18971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18971 := by decide +kernel

theorem rowEval18971 (x : Key → ℝ) : Integer.Sparse.eval row18971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18971, Integer.Sparse.eval_collectBalanced, rawRowCheck18971]

def rawRow18972 : Integer.Sparse Key := [(key1083, 24), (key1177, 24), (key969, 24), (key1083, 24), (key1083, 24)]

theorem rawRowCheck18972 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18972 := by decide +kernel

def row18972 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18972 : row18972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18972 := by decide +kernel

theorem rowEval18972 (x : Key → ℝ) : Integer.Sparse.eval row18972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18972, Integer.Sparse.eval_collectBalanced, rawRowCheck18972]

def rawRow18973 : Integer.Sparse Key := [(key1083, 24), (key1177, 24), (key1083, 24), (key969, 24), (key1083, 24)]

theorem rawRowCheck18973 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18973 := by decide +kernel

def row18973 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18973 : row18973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18973 := by decide +kernel

theorem rowEval18973 (x : Key → ℝ) : Integer.Sparse.eval row18973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18973, Integer.Sparse.eval_collectBalanced, rawRowCheck18973]

def rawRow18974 : Integer.Sparse Key := [(key1083, 24), (key1177, 24), (key1083, 24), (key1083, 24), (key969, 24)]

theorem rawRowCheck18974 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18974 := by decide +kernel

def row18974 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18974 : row18974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18974 := by decide +kernel

theorem rowEval18974 (x : Key → ℝ) : Integer.Sparse.eval row18974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18974, Integer.Sparse.eval_collectBalanced, rawRowCheck18974]

def rawRow18975 : Integer.Sparse Key := [(key1177, 24), (key969, 24), (key1083, 24), (key1083, 24), (key1083, 24)]

theorem rawRowCheck18975 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18975 := by decide +kernel

def row18975 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18975 : row18975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18975 := by decide +kernel

theorem rowEval18975 (x : Key → ℝ) : Integer.Sparse.eval row18975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18975, Integer.Sparse.eval_collectBalanced, rawRowCheck18975]

def rawRow18976 : Integer.Sparse Key := [(key1177, 24), (key1083, 24), (key969, 24), (key1083, 24), (key1083, 24)]

theorem rawRowCheck18976 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18976 := by decide +kernel

def row18976 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18976 : row18976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18976 := by decide +kernel

theorem rowEval18976 (x : Key → ℝ) : Integer.Sparse.eval row18976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18976, Integer.Sparse.eval_collectBalanced, rawRowCheck18976]

def rawRow18977 : Integer.Sparse Key := [(key1177, 24), (key1083, 24), (key1083, 24), (key969, 24), (key1083, 24)]

theorem rawRowCheck18977 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18977 := by decide +kernel

def row18977 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18977 : row18977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18977 := by decide +kernel

theorem rowEval18977 (x : Key → ℝ) : Integer.Sparse.eval row18977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18977, Integer.Sparse.eval_collectBalanced, rawRowCheck18977]

def rawRow18978 : Integer.Sparse Key := [(key1177, 24), (key1083, 24), (key1083, 24), (key1083, 24), (key969, 24)]

theorem rawRowCheck18978 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18978 := by decide +kernel

def row18978 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

theorem rowCheck18978 : row18978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18978 := by decide +kernel

theorem rowEval18978 (x : Key → ℝ) : Integer.Sparse.eval row18978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18978, Integer.Sparse.eval_collectBalanced, rawRowCheck18978]

def rawRow18979 : Integer.Sparse Key := [(key2584, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2599, 2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2888, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2844, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2875, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2909, 2), (key2988, 2)]

theorem rawRowCheck18979 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form2 = rawRow18979 := by decide +kernel

def row18979 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18979 : row18979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18979 := by decide +kernel

theorem rowEval18979 (x : Key → ℝ) : Integer.Sparse.eval row18979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18979, Integer.Sparse.eval_collectBalanced, rawRowCheck18979]

def rawRow18980 : Integer.Sparse Key := [(key2588, 2), (key2584, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2599, 2), (key2588, 2), (key2767, 2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2888, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2988, 2), (key2909, 2)]

theorem rawRowCheck18980 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form2 = rawRow18980 := by decide +kernel

def row18980 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18980 : row18980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18980 := by decide +kernel

theorem rowEval18980 (x : Key → ℝ) : Integer.Sparse.eval row18980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18980, Integer.Sparse.eval_collectBalanced, rawRowCheck18980]

def rawRow18981 : Integer.Sparse Key := [(key2588, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2988, 2), (key2909, 2), (key2909, 2), (key2875, 2), (key2875, 2)]

theorem rawRowCheck18981 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form2 = rawRow18981 := by decide +kernel

def row18981 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18981 : row18981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18981 := by decide +kernel

theorem rowEval18981 (x : Key → ℝ) : Integer.Sparse.eval row18981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18981, Integer.Sparse.eval_collectBalanced, rawRowCheck18981]

def rawRow18982 : Integer.Sparse Key := [(key2599, 2), (key2599, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2584, 2), (key2584, 2), (key2930, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2763, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2988, 2), (key2988, 2), (key2909, 2), (key2909, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2)]

theorem rawRowCheck18982 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18982 := by decide +kernel

def row18982 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18982 : row18982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18982 := by decide +kernel

theorem rowEval18982 (x : Key → ℝ) : Integer.Sparse.eval row18982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18982, Integer.Sparse.eval_collectBalanced, rawRowCheck18982]

def rawRow18983 : Integer.Sparse Key := [(key2763, 2), (key2767, 2), (key2767, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2888, 2), (key2875, 2), (key2875, 2), (key2909, 2), (key2584, 2), (key2588, 2), (key2588, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2584, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2599, 2), (key2763, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2930, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2909, 2), (key2988, 2), (key2588, 2), (key2588, 2), (key2599, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2844, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2888, 2), (key2967, 2)]

theorem rawRowCheck18983 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form2 = rawRow18983 := by decide +kernel

def row18983 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18983 : row18983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18983 := by decide +kernel

theorem rowEval18983 (x : Key → ℝ) : Integer.Sparse.eval row18983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18983, Integer.Sparse.eval_collectBalanced, rawRowCheck18983]

def rawRow18984 : Integer.Sparse Key := [(key2767, 2), (key2763, 2), (key2767, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2988, 2), (key2909, 2), (key2588, 2), (key2599, 2), (key2588, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2888, 2)]

theorem rawRowCheck18984 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form2 = rawRow18984 := by decide +kernel

def row18984 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18984 : row18984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18984 := by decide +kernel

theorem rowEval18984 (x : Key → ℝ) : Integer.Sparse.eval row18984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18984, Integer.Sparse.eval_collectBalanced, rawRowCheck18984]

def rawRow18985 : Integer.Sparse Key := [(key2767, 2), (key2767, 2), (key2763, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2967, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2875, 2), (key2599, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2584, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2988, 2), (key2909, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2)]

theorem rawRowCheck18985 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form2 = rawRow18985 := by decide +kernel

def row18985 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18985 : row18985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18985 := by decide +kernel

theorem rowEval18985 (x : Key → ℝ) : Integer.Sparse.eval row18985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18985, Integer.Sparse.eval_collectBalanced, rawRowCheck18985]

def rawRow18986 : Integer.Sparse Key := [(key2840, 2), (key2844, 2), (key2875, 2), (key2763, 2), (key2767, 2), (key2840, 2), (key2888, 2), (key2875, 2), (key2909, 2), (key2767, 2), (key2844, 2), (key2888, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2584, 2), (key2588, 2), (key2840, 2), (key2967, 2), (key2875, 2), (key2988, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2763, 2), (key2767, 2), (key2840, 2), (key2888, 2), (key2875, 2), (key2909, 2), (key2584, 2), (key2588, 2), (key2840, 2), (key2967, 2), (key2875, 2), (key2988, 2), (key2584, 2), (key2599, 2), (key2763, 2), (key2930, 2), (key2909, 2), (key2988, 2), (key2588, 2), (key2599, 2), (key2767, 2), (key2930, 2), (key2888, 2), (key2967, 2), (key2767, 2), (key2844, 2), (key2888, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2599, 2), (key2767, 2), (key2930, 2), (key2888, 2), (key2967, 2)]

theorem rawRowCheck18986 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form2 = rawRow18986 := by decide +kernel

def row18986 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18986 : row18986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18986 := by decide +kernel

theorem rowEval18986 (x : Key → ℝ) : Integer.Sparse.eval row18986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18986, Integer.Sparse.eval_collectBalanced, rawRowCheck18986]

def rawRow18987 : Integer.Sparse Key := [(key2844, 2), (key2840, 2), (key2875, 2), (key2767, 2), (key2763, 2), (key2888, 2), (key2840, 2), (key2909, 2), (key2875, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2767, 2), (key2763, 2), (key2888, 2), (key2840, 2), (key2909, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2599, 2), (key2584, 2), (key2930, 2), (key2763, 2), (key2988, 2), (key2909, 2), (key2599, 2), (key2588, 2), (key2930, 2), (key2767, 2), (key2967, 2), (key2888, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2599, 2), (key2588, 2), (key2930, 2), (key2767, 2), (key2967, 2), (key2888, 2)]

theorem rawRowCheck18987 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form2 = rawRow18987 := by decide +kernel

def row18987 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18987 : row18987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18987 := by decide +kernel

theorem rowEval18987 (x : Key → ℝ) : Integer.Sparse.eval row18987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18987, Integer.Sparse.eval_collectBalanced, rawRowCheck18987]

def rawRow18988 : Integer.Sparse Key := [(key2840, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2767, 2), (key2888, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2840, 2), (key2875, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2840, 2), (key2875, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2763, 2), (key2909, 2), (key2584, 2), (key2988, 2), (key2599, 2), (key2930, 2), (key2767, 2), (key2888, 2), (key2588, 2), (key2967, 2), (key2599, 2), (key2930, 2), (key2844, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2767, 2), (key2888, 2), (key2588, 2), (key2967, 2), (key2599, 2), (key2930, 2)]

theorem rawRowCheck18988 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form2 = rawRow18988 := by decide +kernel

def row18988 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18988 : row18988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18988 := by decide +kernel

theorem rowEval18988 (x : Key → ℝ) : Integer.Sparse.eval row18988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18988, Integer.Sparse.eval_collectBalanced, rawRowCheck18988]

def rawRow18989 : Integer.Sparse Key := [(key2875, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2875, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2888, 2), (key2767, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2967, 2), (key2588, 2), (key2909, 2), (key2763, 2), (key2988, 2), (key2584, 2), (key2930, 2), (key2599, 2), (key2888, 2), (key2767, 2), (key2967, 2), (key2588, 2), (key2930, 2), (key2599, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2888, 2), (key2767, 2), (key2967, 2), (key2588, 2), (key2930, 2), (key2599, 2)]

theorem rawRowCheck18989 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form2 = rawRow18989 := by decide +kernel

def row18989 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18989 : row18989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18989 := by decide +kernel

theorem rowEval18989 (x : Key → ℝ) : Integer.Sparse.eval row18989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18989, Integer.Sparse.eval_collectBalanced, rawRowCheck18989]

def rawRow18990 : Integer.Sparse Key := [(key2844, 2), (key2875, 2), (key2840, 2), (key2888, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2763, 2), (key2840, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2888, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2763, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2930, 2), (key2988, 2), (key2599, 2), (key2909, 2), (key2584, 2), (key2763, 2), (key2930, 2), (key2967, 2), (key2599, 2), (key2888, 2), (key2588, 2), (key2767, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2930, 2), (key2967, 2), (key2599, 2), (key2888, 2), (key2588, 2), (key2767, 2)]

theorem rawRowCheck18990 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form2 = rawRow18990 := by decide +kernel

def row18990 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18990 : row18990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18990 := by decide +kernel

theorem rowEval18990 (x : Key → ℝ) : Integer.Sparse.eval row18990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18990, Integer.Sparse.eval_collectBalanced, rawRowCheck18990]

def rawRow18991 : Integer.Sparse Key := [(key2875, 2), (key2844, 2), (key2840, 2), (key2909, 2), (key2888, 2), (key2875, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2888, 2), (key2844, 2), (key2767, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2875, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2909, 2), (key2888, 2), (key2875, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2988, 2), (key2967, 2), (key2875, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2988, 2), (key2930, 2), (key2909, 2), (key2599, 2), (key2763, 2), (key2584, 2), (key2967, 2), (key2930, 2), (key2888, 2), (key2599, 2), (key2767, 2), (key2588, 2), (key2888, 2), (key2844, 2), (key2767, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2930, 2), (key2888, 2), (key2599, 2), (key2767, 2), (key2588, 2)]

theorem rawRowCheck18991 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form2 = rawRow18991 := by decide +kernel

def row18991 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18991 : row18991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18991 := by decide +kernel

theorem rowEval18991 (x : Key → ℝ) : Integer.Sparse.eval row18991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18991, Integer.Sparse.eval_collectBalanced, rawRowCheck18991]

def rawRow18992 : Integer.Sparse Key := [(key2888, 2), (key2888, 2), (key2909, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2840, 2), (key2930, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2988, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2584, 2), (key2763, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2)]

theorem rawRowCheck18992 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18992 := by decide +kernel

def row18992 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18992 : row18992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18992 := by decide +kernel

theorem rowEval18992 (x : Key → ℝ) : Integer.Sparse.eval row18992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18992, Integer.Sparse.eval_collectBalanced, rawRowCheck18992]

def rawRow18993 : Integer.Sparse Key := [(key2888, 2), (key2909, 2), (key2888, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2584, 2), (key2763, 2), (key2967, 2), (key2930, 2), (key2967, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2767, 2)]

theorem rawRowCheck18993 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18993 := by decide +kernel

def row18993 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18993 : row18993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18993 := by decide +kernel

theorem rowEval18993 (x : Key → ℝ) : Integer.Sparse.eval row18993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18993, Integer.Sparse.eval_collectBalanced, rawRowCheck18993]

def rawRow18994 : Integer.Sparse Key := [(key2909, 2), (key2888, 2), (key2888, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2840, 2), (key2840, 2), (key2763, 2), (key2988, 2), (key2967, 2), (key2967, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2988, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2930, 2), (key2909, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2599, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2763, 2), (key2584, 2), (key2967, 2), (key2967, 2), (key2930, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2844, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2767, 2), (key2588, 2)]

theorem rawRowCheck18994 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18994 := by decide +kernel

def row18994 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18994 : row18994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18994 := by decide +kernel

theorem rowEval18994 (x : Key → ℝ) : Integer.Sparse.eval row18994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18994, Integer.Sparse.eval_collectBalanced, rawRowCheck18994]

def rawRow18995 : Integer.Sparse Key := [(key2930, 2), (key2930, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2988, 2), (key2988, 2), (key2599, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2909, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2584, 2), (key2584, 2), (key2763, 2), (key2763, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2)]

theorem rawRowCheck18995 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18995 := by decide +kernel

def row18995 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18995 : row18995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18995 := by decide +kernel

theorem rowEval18995 (x : Key → ℝ) : Integer.Sparse.eval row18995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18995, Integer.Sparse.eval_collectBalanced, rawRowCheck18995]

def rawRow18996 : Integer.Sparse Key := [(key2967, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2584, 2), (key2763, 2), (key2763, 2), (key2840, 2), (key2840, 2)]

theorem rawRowCheck18996 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18996 := by decide +kernel

def row18996 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18996 : row18996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18996 := by decide +kernel

theorem rowEval18996 (x : Key → ℝ) : Integer.Sparse.eval row18996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18996, Integer.Sparse.eval_collectBalanced, rawRowCheck18996]

def rawRow18997 : Integer.Sparse Key := [(key2967, 2), (key2988, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2930, 2), (key2967, 2), (key2888, 2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2584, 2), (key2763, 2)]

theorem rawRowCheck18997 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18997 := by decide +kernel

def row18997 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18997 : row18997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18997 := by decide +kernel

theorem rowEval18997 (x : Key → ℝ) : Integer.Sparse.eval row18997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18997, Integer.Sparse.eval_collectBalanced, rawRowCheck18997]

def rawRow18998 : Integer.Sparse Key := [(key2988, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2930, 2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2844, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2840, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2763, 2), (key2584, 2)]

theorem rawRowCheck18998 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18998 := by decide +kernel

def row18998 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

theorem rowCheck18998 : row18998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18998 := by decide +kernel

theorem rowEval18998 (x : Key → ℝ) : Integer.Sparse.eval row18998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18998, Integer.Sparse.eval_collectBalanced, rawRowCheck18998]

def rawRow18999 : Integer.Sparse Key := [(key2352, 24), (key2447, 24), (key2447, 24), (key2447, 24), (key2511, 24)]

theorem rawRowCheck18999 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form3 = rawRow18999 := by decide +kernel

def row18999 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck18999 : row18999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18999 := by decide +kernel

theorem rowEval18999 (x : Key → ℝ) : Integer.Sparse.eval row18999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18999, Integer.Sparse.eval_collectBalanced, rawRowCheck18999]

def rawRow19000 : Integer.Sparse Key := [(key2352, 24), (key2447, 24), (key2447, 24), (key2511, 24), (key2447, 24)]

theorem rawRowCheck19000 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form3 = rawRow19000 := by decide +kernel

def row19000 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19000 : row19000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19000 := by decide +kernel

theorem rowEval19000 (x : Key → ℝ) : Integer.Sparse.eval row19000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19000, Integer.Sparse.eval_collectBalanced, rawRowCheck19000]

def rawRow19001 : Integer.Sparse Key := [(key2352, 24), (key2447, 24), (key2511, 24), (key2447, 24), (key2447, 24)]

theorem rawRowCheck19001 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form3 = rawRow19001 := by decide +kernel

def row19001 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19001 : row19001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19001 := by decide +kernel

theorem rowEval19001 (x : Key → ℝ) : Integer.Sparse.eval row19001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19001, Integer.Sparse.eval_collectBalanced, rawRowCheck19001]

def rawRow19002 : Integer.Sparse Key := [(key2352, 24), (key2511, 24), (key2447, 24), (key2447, 24), (key2447, 24)]

theorem rawRowCheck19002 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19002 := by decide +kernel

def row19002 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19002 : row19002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19002 := by decide +kernel

theorem rowEval19002 (x : Key → ℝ) : Integer.Sparse.eval row19002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19002, Integer.Sparse.eval_collectBalanced, rawRowCheck19002]

def rawRow19003 : Integer.Sparse Key := [(key2447, 24), (key2352, 24), (key2447, 24), (key2447, 24), (key2511, 24)]

theorem rawRowCheck19003 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form3 = rawRow19003 := by decide +kernel

def row19003 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19003 : row19003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19003 := by decide +kernel

theorem rowEval19003 (x : Key → ℝ) : Integer.Sparse.eval row19003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19003, Integer.Sparse.eval_collectBalanced, rawRowCheck19003]

def rawRow19004 : Integer.Sparse Key := [(key2447, 24), (key2352, 24), (key2447, 24), (key2511, 24), (key2447, 24)]

theorem rawRowCheck19004 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form3 = rawRow19004 := by decide +kernel

def row19004 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19004 : row19004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19004 := by decide +kernel

theorem rowEval19004 (x : Key → ℝ) : Integer.Sparse.eval row19004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19004, Integer.Sparse.eval_collectBalanced, rawRowCheck19004]

def rawRow19005 : Integer.Sparse Key := [(key2447, 24), (key2352, 24), (key2511, 24), (key2447, 24), (key2447, 24)]

theorem rawRowCheck19005 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form3 = rawRow19005 := by decide +kernel

def row19005 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19005 : row19005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19005 := by decide +kernel

theorem rowEval19005 (x : Key → ℝ) : Integer.Sparse.eval row19005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19005, Integer.Sparse.eval_collectBalanced, rawRowCheck19005]

def rawRow19006 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2352, 24), (key2447, 24), (key2511, 24)]

theorem rawRowCheck19006 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form3 = rawRow19006 := by decide +kernel

def row19006 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19006 : row19006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19006 := by decide +kernel

theorem rowEval19006 (x : Key → ℝ) : Integer.Sparse.eval row19006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19006, Integer.Sparse.eval_collectBalanced, rawRowCheck19006]

def rawRow19007 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2352, 24), (key2511, 24), (key2447, 24)]

theorem rawRowCheck19007 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form3 = rawRow19007 := by decide +kernel

def row19007 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19007 : row19007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19007 := by decide +kernel

theorem rowEval19007 (x : Key → ℝ) : Integer.Sparse.eval row19007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19007, Integer.Sparse.eval_collectBalanced, rawRowCheck19007]

def rawRow19008 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2447, 24), (key2352, 24), (key2511, 24)]

theorem rawRowCheck19008 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form3 = rawRow19008 := by decide +kernel

def row19008 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19008 : row19008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19008 := by decide +kernel

theorem rowEval19008 (x : Key → ℝ) : Integer.Sparse.eval row19008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19008, Integer.Sparse.eval_collectBalanced, rawRowCheck19008]

def rawRow19009 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2447, 24), (key2511, 24), (key2352, 24)]

theorem rawRowCheck19009 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form3 = rawRow19009 := by decide +kernel

def row19009 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19009 : row19009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19009 := by decide +kernel

theorem rowEval19009 (x : Key → ℝ) : Integer.Sparse.eval row19009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck19009, Integer.Sparse.eval_collectBalanced, rawRowCheck19009]

def rawRow19010 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2511, 24), (key2352, 24), (key2447, 24)]

theorem rawRowCheck19010 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form3 = rawRow19010 := by decide +kernel

def row19010 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19010 : row19010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19010 := by decide +kernel

theorem rowEval19010 (x : Key → ℝ) : Integer.Sparse.eval row19010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19010, Integer.Sparse.eval_collectBalanced, rawRowCheck19010]

def rawRow19011 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2511, 24), (key2447, 24), (key2352, 24)]

theorem rawRowCheck19011 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form3 = rawRow19011 := by decide +kernel

def row19011 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19011 : row19011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19011 := by decide +kernel

theorem rowEval19011 (x : Key → ℝ) : Integer.Sparse.eval row19011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck19011, Integer.Sparse.eval_collectBalanced, rawRowCheck19011]

def rawRow19012 : Integer.Sparse Key := [(key2447, 24), (key2511, 24), (key2352, 24), (key2447, 24), (key2447, 24)]

theorem rawRowCheck19012 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form3 = rawRow19012 := by decide +kernel

def row19012 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19012 : row19012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19012 := by decide +kernel

theorem rowEval19012 (x : Key → ℝ) : Integer.Sparse.eval row19012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19012, Integer.Sparse.eval_collectBalanced, rawRowCheck19012]

def rawRow19013 : Integer.Sparse Key := [(key2447, 24), (key2511, 24), (key2447, 24), (key2352, 24), (key2447, 24)]

theorem rawRowCheck19013 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form3 = rawRow19013 := by decide +kernel

def row19013 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19013 : row19013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19013 := by decide +kernel

theorem rowEval19013 (x : Key → ℝ) : Integer.Sparse.eval row19013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19013, Integer.Sparse.eval_collectBalanced, rawRowCheck19013]

def rawRow19014 : Integer.Sparse Key := [(key2447, 24), (key2511, 24), (key2447, 24), (key2447, 24), (key2352, 24)]

theorem rawRowCheck19014 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form3 = rawRow19014 := by decide +kernel

def row19014 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19014 : row19014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19014 := by decide +kernel

theorem rowEval19014 (x : Key → ℝ) : Integer.Sparse.eval row19014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck19014, Integer.Sparse.eval_collectBalanced, rawRowCheck19014]

def rawRow19015 : Integer.Sparse Key := [(key2511, 24), (key2352, 24), (key2447, 24), (key2447, 24), (key2447, 24)]

theorem rawRowCheck19015 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19015 := by decide +kernel

def row19015 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19015 : row19015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19015 := by decide +kernel

theorem rowEval19015 (x : Key → ℝ) : Integer.Sparse.eval row19015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19015, Integer.Sparse.eval_collectBalanced, rawRowCheck19015]

def rawRow19016 : Integer.Sparse Key := [(key2511, 24), (key2447, 24), (key2352, 24), (key2447, 24), (key2447, 24)]

theorem rawRowCheck19016 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form3 = rawRow19016 := by decide +kernel

def row19016 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19016 : row19016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19016 := by decide +kernel

theorem rowEval19016 (x : Key → ℝ) : Integer.Sparse.eval row19016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19016, Integer.Sparse.eval_collectBalanced, rawRowCheck19016]

def rawRow19017 : Integer.Sparse Key := [(key2511, 24), (key2447, 24), (key2447, 24), (key2352, 24), (key2447, 24)]

theorem rawRowCheck19017 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form3 = rawRow19017 := by decide +kernel

def row19017 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19017 : row19017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19017 := by decide +kernel

theorem rowEval19017 (x : Key → ℝ) : Integer.Sparse.eval row19017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19017, Integer.Sparse.eval_collectBalanced, rawRowCheck19017]

def rawRow19018 : Integer.Sparse Key := [(key2511, 24), (key2447, 24), (key2447, 24), (key2447, 24), (key2352, 24)]

theorem rawRowCheck19018 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form3 = rawRow19018 := by decide +kernel

def row19018 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

theorem rowCheck19018 : row19018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19018 := by decide +kernel

theorem rowEval19018 (x : Key → ℝ) : Integer.Sparse.eval row19018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck19018, Integer.Sparse.eval_collectBalanced, rawRowCheck19018]

def rawRow19019 : Integer.Sparse Key := [(key972, 6), (key977, 6), (key977, 6), (key977, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key1162, 6), (key1162, 6), (key1162, 6), (key1218, 6)]

theorem rawRowCheck19019 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form4 = rawRow19019 := by decide +kernel

def row19019 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19019 : row19019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19019 := by decide +kernel

theorem rowEval19019 (x : Key → ℝ) : Integer.Sparse.eval row19019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19019, Integer.Sparse.eval_collectBalanced, rawRowCheck19019]

def rawRow19020 : Integer.Sparse Key := [(key977, 6), (key972, 6), (key977, 6), (key977, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key1218, 6), (key1162, 6)]

theorem rawRowCheck19020 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form4 = rawRow19020 := by decide +kernel

def row19020 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19020 : row19020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19020 := by decide +kernel

theorem rowEval19020 (x : Key → ℝ) : Integer.Sparse.eval row19020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19020, Integer.Sparse.eval_collectBalanced, rawRowCheck19020]

def rawRow19021 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key972, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1218, 6), (key1162, 6), (key1162, 6)]

theorem rawRowCheck19021 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form4 = rawRow19021 := by decide +kernel

def row19021 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19021 : row19021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19021 := by decide +kernel

theorem rowEval19021 (x : Key → ℝ) : Integer.Sparse.eval row19021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19021, Integer.Sparse.eval_collectBalanced, rawRowCheck19021]

def rawRow19022 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key977, 6), (key972, 6), (key1181, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key1086, 6), (key1218, 6), (key1162, 6), (key1162, 6), (key1162, 6)]

theorem rawRowCheck19022 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19022 := by decide +kernel

def row19022 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19022 : row19022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19022 := by decide +kernel

theorem rowEval19022 (x : Key → ℝ) : Integer.Sparse.eval row19022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19022, Integer.Sparse.eval_collectBalanced, rawRowCheck19022]

def rawRow19023 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key972, 6), (key977, 6), (key977, 6), (key1086, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1181, 6), (key1162, 6), (key1162, 6), (key1218, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1181, 6)]

theorem rawRowCheck19023 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form4 = rawRow19023 := by decide +kernel

def row19023 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19023 : row19023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19023 := by decide +kernel

theorem rowEval19023 (x : Key → ℝ) : Integer.Sparse.eval row19023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19023, Integer.Sparse.eval_collectBalanced, rawRowCheck19023]

def rawRow19024 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key977, 6), (key972, 6), (key977, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key1218, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1181, 6), (key1091, 6)]

theorem rawRowCheck19024 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form4 = rawRow19024 := by decide +kernel

def row19024 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19024 : row19024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19024 := by decide +kernel

theorem rowEval19024 (x : Key → ℝ) : Integer.Sparse.eval row19024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19024, Integer.Sparse.eval_collectBalanced, rawRowCheck19024]

def rawRow19025 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key977, 6), (key977, 6), (key972, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key1218, 6), (key1162, 6), (key1162, 6), (key977, 6), (key1181, 6), (key1091, 6), (key1091, 6)]

theorem rawRowCheck19025 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form4 = rawRow19025 := by decide +kernel

def row19025 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19025 : row19025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19025 := by decide +kernel

theorem rowEval19025 (x : Key → ℝ) : Integer.Sparse.eval row19025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19025, Integer.Sparse.eval_collectBalanced, rawRowCheck19025]

def rawRow19026 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key972, 6), (key977, 6), (key1086, 6), (key1181, 6), (key1162, 6), (key1218, 6), (key977, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1181, 6)]

theorem rawRowCheck19026 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form4 = rawRow19026 := by decide +kernel

def row19026 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19026 : row19026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19026 := by decide +kernel

theorem rowEval19026 (x : Key → ℝ) : Integer.Sparse.eval row19026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19026, Integer.Sparse.eval_collectBalanced, rawRowCheck19026]

def rawRow19027 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key977, 6), (key972, 6), (key1181, 6), (key1086, 6), (key1218, 6), (key1162, 6), (key977, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1181, 6), (key1091, 6)]

theorem rawRowCheck19027 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form4 = rawRow19027 := by decide +kernel

def row19027 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19027 : row19027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19027 := by decide +kernel

theorem rowEval19027 (x : Key → ℝ) : Integer.Sparse.eval row19027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19027, Integer.Sparse.eval_collectBalanced, rawRowCheck19027]

def rawRow19028 : Integer.Sparse Key := [(key1086, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key972, 6), (key1218, 6), (key977, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1181, 6)]

theorem rawRowCheck19028 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form4 = rawRow19028 := by decide +kernel

def row19028 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19028 : row19028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19028 := by decide +kernel

theorem rowEval19028 (x : Key → ℝ) : Integer.Sparse.eval row19028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19028, Integer.Sparse.eval_collectBalanced, rawRowCheck19028]

def rawRow19029 : Integer.Sparse Key := [(key1162, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1218, 6), (key972, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key977, 6)]

theorem rawRowCheck19029 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form4 = rawRow19029 := by decide +kernel

def row19029 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19029 : row19029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19029 := by decide +kernel

theorem rowEval19029 (x : Key → ℝ) : Integer.Sparse.eval row19029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck19029, Integer.Sparse.eval_collectBalanced, rawRowCheck19029]

def rawRow19030 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1181, 6), (key1218, 6), (key977, 6), (key1162, 6), (key972, 6), (key1086, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key977, 6), (key1091, 6)]

theorem rawRowCheck19030 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form4 = rawRow19030 := by decide +kernel

def row19030 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19030 : row19030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19030 := by decide +kernel

theorem rowEval19030 (x : Key → ℝ) : Integer.Sparse.eval row19030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19030, Integer.Sparse.eval_collectBalanced, rawRowCheck19030]

def rawRow19031 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1218, 6), (key1181, 6), (key1162, 6), (key977, 6), (key1086, 6), (key972, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key977, 6)]

theorem rawRowCheck19031 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form4 = rawRow19031 := by decide +kernel

def row19031 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19031 : row19031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19031 := by decide +kernel

theorem rowEval19031 (x : Key → ℝ) : Integer.Sparse.eval row19031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck19031, Integer.Sparse.eval_collectBalanced, rawRowCheck19031]

def rawRow19032 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1181, 6), (key1181, 6), (key1218, 6), (key977, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key972, 6), (key1086, 6), (key1086, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1091, 6)]

theorem rawRowCheck19032 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form4 = rawRow19032 := by decide +kernel

def row19032 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19032 : row19032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19032 := by decide +kernel

theorem rowEval19032 (x : Key → ℝ) : Integer.Sparse.eval row19032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19032, Integer.Sparse.eval_collectBalanced, rawRowCheck19032]

def rawRow19033 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1218, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1086, 6), (key972, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1091, 6)]

theorem rawRowCheck19033 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form4 = rawRow19033 := by decide +kernel

def row19033 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19033 : row19033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19033 := by decide +kernel

theorem rowEval19033 (x : Key → ℝ) : Integer.Sparse.eval row19033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19033, Integer.Sparse.eval_collectBalanced, rawRowCheck19033]

def rawRow19034 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1218, 6), (key1181, 6), (key1181, 6), (key1162, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1091, 6), (key977, 6), (key1086, 6), (key1086, 6), (key972, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key977, 6)]

theorem rawRowCheck19034 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form4 = rawRow19034 := by decide +kernel

def row19034 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19034 : row19034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19034 := by decide +kernel

theorem rowEval19034 (x : Key → ℝ) : Integer.Sparse.eval row19034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck19034, Integer.Sparse.eval_collectBalanced, rawRowCheck19034]

def rawRow19035 : Integer.Sparse Key := [(key1181, 6), (key1181, 6), (key1181, 6), (key1218, 6), (key977, 6), (key977, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key1162, 6), (key972, 6), (key1086, 6), (key1086, 6), (key1086, 6)]

theorem rawRowCheck19035 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19035 := by decide +kernel

def row19035 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19035 : row19035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19035 := by decide +kernel

theorem rowEval19035 (x : Key → ℝ) : Integer.Sparse.eval row19035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19035, Integer.Sparse.eval_collectBalanced, rawRowCheck19035]

def rawRow19036 : Integer.Sparse Key := [(key1181, 6), (key1181, 6), (key1218, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key977, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key972, 6), (key1086, 6), (key1086, 6)]

theorem rawRowCheck19036 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form4 = rawRow19036 := by decide +kernel

def row19036 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19036 : row19036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19036 := by decide +kernel

theorem rowEval19036 (x : Key → ℝ) : Integer.Sparse.eval row19036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19036, Integer.Sparse.eval_collectBalanced, rawRowCheck19036]

def rawRow19037 : Integer.Sparse Key := [(key1181, 6), (key1218, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key972, 6), (key1086, 6)]

theorem rawRowCheck19037 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form4 = rawRow19037 := by decide +kernel

def row19037 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19037 : row19037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19037 := by decide +kernel

theorem rowEval19037 (x : Key → ℝ) : Integer.Sparse.eval row19037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19037, Integer.Sparse.eval_collectBalanced, rawRowCheck19037]

def rawRow19038 : Integer.Sparse Key := [(key1218, 6), (key1181, 6), (key1181, 6), (key1181, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1086, 6), (key1086, 6), (key1086, 6), (key972, 6)]

theorem rawRowCheck19038 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form4 = rawRow19038 := by decide +kernel

def row19038 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

theorem rowCheck19038 : row19038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19038 := by decide +kernel

theorem rowEval19038 (x : Key → ℝ) : Integer.Sparse.eval row19038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck19038, Integer.Sparse.eval_collectBalanced, rawRowCheck19038]

def rawRow19039 : Integer.Sparse Key := [(key2361, 4), (key2361, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2364, 4), (key2456, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2531, 4), (key2517, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2561, 4)]

theorem rawRowCheck19039 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form5 = rawRow19039 := by decide +kernel

def row19039 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19039 : row19039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19039 := by decide +kernel

theorem rowEval19039 (x : Key → ℝ) : Integer.Sparse.eval row19039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19039, Integer.Sparse.eval_collectBalanced, rawRowCheck19039]

def rawRow19040 : Integer.Sparse Key := [(key2361, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2520, 4), (key2517, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2561, 4), (key2520, 4)]

theorem rawRowCheck19040 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form5 = rawRow19040 := by decide +kernel

def row19040 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19040 : row19040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19040 := by decide +kernel

theorem rowEval19040 (x : Key → ℝ) : Integer.Sparse.eval row19040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19040, Integer.Sparse.eval_collectBalanced, rawRowCheck19040]

def rawRow19041 : Integer.Sparse Key := [(key2364, 4), (key2361, 4), (key2361, 4), (key2364, 4), (key2364, 4), (key2361, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2531, 4), (key2459, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2520, 4)]

theorem rawRowCheck19041 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form5 = rawRow19041 := by decide +kernel

def row19041 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19041 : row19041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19041 := by decide +kernel

theorem rowEval19041 (x : Key → ℝ) : Integer.Sparse.eval row19041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19041, Integer.Sparse.eval_collectBalanced, rawRowCheck19041]

def rawRow19042 : Integer.Sparse Key := [(key2364, 4), (key2364, 4), (key2364, 4), (key2361, 4), (key2361, 4), (key2361, 4), (key2531, 4), (key2531, 4), (key2531, 4), (key2459, 4), (key2459, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2561, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2517, 4), (key2517, 4)]

theorem rawRowCheck19042 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19042 := by decide +kernel

def row19042 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19042 : row19042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19042 := by decide +kernel

theorem rowEval19042 (x : Key → ℝ) : Integer.Sparse.eval row19042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19042, Integer.Sparse.eval_collectBalanced, rawRowCheck19042]

def rawRow19043 : Integer.Sparse Key := [(key2456, 4), (key2456, 4), (key2459, 4), (key2517, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2517, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2561, 4), (key2361, 4), (key2364, 4), (key2364, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2531, 4), (key2520, 4), (key2520, 4), (key2561, 4)]

theorem rawRowCheck19043 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form5 = rawRow19043 := by decide +kernel

def row19043 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19043 : row19043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19043 := by decide +kernel

theorem rowEval19043 (x : Key → ℝ) : Integer.Sparse.eval row19043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19043, Integer.Sparse.eval_collectBalanced, rawRowCheck19043]

def rawRow19044 : Integer.Sparse Key := [(key2456, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2520, 4), (key2361, 4), (key2364, 4), (key2361, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2520, 4), (key2561, 4), (key2520, 4)]

theorem rawRowCheck19044 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form5 = rawRow19044 := by decide +kernel

def row19044 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19044 : row19044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19044 := by decide +kernel

theorem rowEval19044 (x : Key → ℝ) : Integer.Sparse.eval row19044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19044, Integer.Sparse.eval_collectBalanced, rawRowCheck19044]

def rawRow19045 : Integer.Sparse Key := [(key2459, 4), (key2456, 4), (key2456, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2364, 4), (key2361, 4), (key2361, 4), (key2531, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2517, 4), (key2364, 4), (key2364, 4), (key2361, 4), (key2531, 4), (key2531, 4), (key2459, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2520, 4), (key2520, 4)]

theorem rawRowCheck19045 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form5 = rawRow19045 := by decide +kernel

def row19045 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19045 : row19045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19045 := by decide +kernel

theorem rowEval19045 (x : Key → ℝ) : Integer.Sparse.eval row19045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19045, Integer.Sparse.eval_collectBalanced, rawRowCheck19045]

def rawRow19046 : Integer.Sparse Key := [(key2456, 4), (key2517, 4), (key2520, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2520, 4), (key2361, 4), (key2517, 4), (key2561, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2531, 4), (key2520, 4), (key2561, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2531, 4), (key2520, 4), (key2561, 4), (key2364, 4), (key2459, 4), (key2531, 4)]

theorem rawRowCheck19046 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form5 = rawRow19046 := by decide +kernel

def row19046 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19046 : row19046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19046 := by decide +kernel

theorem rowEval19046 (x : Key → ℝ) : Integer.Sparse.eval row19046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19046, Integer.Sparse.eval_collectBalanced, rawRowCheck19046]

def rawRow19047 : Integer.Sparse Key := [(key2456, 4), (key2520, 4), (key2517, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2361, 4), (key2561, 4), (key2517, 4), (key2364, 4), (key2361, 4), (key2531, 4), (key2456, 4), (key2561, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2364, 4), (key2361, 4), (key2531, 4), (key2456, 4), (key2561, 4), (key2520, 4), (key2364, 4), (key2531, 4), (key2459, 4)]

theorem rawRowCheck19047 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form5 = rawRow19047 := by decide +kernel

def row19047 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19047 : row19047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19047 := by decide +kernel

theorem rowEval19047 (x : Key → ℝ) : Integer.Sparse.eval row19047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19047, Integer.Sparse.eval_collectBalanced, rawRowCheck19047]

def rawRow19048 : Integer.Sparse Key := [(key2517, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2459, 4), (key2517, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2361, 4), (key2561, 4), (key2456, 4), (key2520, 4), (key2361, 4), (key2561, 4), (key2364, 4), (key2531, 4), (key2456, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2361, 4), (key2561, 4), (key2364, 4), (key2531, 4), (key2459, 4), (key2364, 4), (key2531, 4)]

theorem rawRowCheck19048 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form5 = rawRow19048 := by decide +kernel

def row19048 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19048 : row19048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19048 := by decide +kernel

theorem rowEval19048 (x : Key → ℝ) : Integer.Sparse.eval row19048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19048, Integer.Sparse.eval_collectBalanced, rawRowCheck19048]

def rawRow19049 : Integer.Sparse Key := [(key2517, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2459, 4), (key2517, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2561, 4), (key2361, 4), (key2520, 4), (key2456, 4), (key2561, 4), (key2361, 4), (key2531, 4), (key2364, 4), (key2520, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2561, 4), (key2361, 4), (key2531, 4), (key2364, 4), (key2459, 4), (key2531, 4), (key2364, 4)]

theorem rawRowCheck19049 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form5 = rawRow19049 := by decide +kernel

def row19049 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19049 : row19049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19049 := by decide +kernel

theorem rowEval19049 (x : Key → ℝ) : Integer.Sparse.eval row19049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19049, Integer.Sparse.eval_collectBalanced, rawRowCheck19049]

def rawRow19050 : Integer.Sparse Key := [(key2520, 4), (key2456, 4), (key2517, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2561, 4), (key2361, 4), (key2517, 4), (key2531, 4), (key2561, 4), (key2364, 4), (key2520, 4), (key2361, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2531, 4), (key2561, 4), (key2364, 4), (key2520, 4), (key2361, 4), (key2456, 4), (key2531, 4), (key2364, 4), (key2459, 4)]

theorem rawRowCheck19050 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form5 = rawRow19050 := by decide +kernel

def row19050 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19050 : row19050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19050 := by decide +kernel

theorem rowEval19050 (x : Key → ℝ) : Integer.Sparse.eval row19050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19050, Integer.Sparse.eval_collectBalanced, rawRowCheck19050]

def rawRow19051 : Integer.Sparse Key := [(key2520, 4), (key2517, 4), (key2456, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2456, 4), (key2561, 4), (key2517, 4), (key2361, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2364, 4), (key2456, 4), (key2361, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2364, 4), (key2456, 4), (key2361, 4), (key2531, 4), (key2459, 4), (key2364, 4)]

theorem rawRowCheck19051 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form5 = rawRow19051 := by decide +kernel

def row19051 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19051 : row19051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19051 := by decide +kernel

theorem rowEval19051 (x : Key → ℝ) : Integer.Sparse.eval row19051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19051, Integer.Sparse.eval_collectBalanced, rawRowCheck19051]

def rawRow19052 : Integer.Sparse Key := [(key2459, 4), (key2520, 4), (key2520, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2531, 4), (key2561, 4), (key2561, 4), (key2364, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2517, 4), (key2531, 4), (key2531, 4), (key2561, 4), (key2364, 4), (key2364, 4), (key2459, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2456, 4), (key2456, 4)]

theorem rawRowCheck19052 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form5 = rawRow19052 := by decide +kernel

def row19052 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19052 : row19052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19052 := by decide +kernel

theorem rowEval19052 (x : Key → ℝ) : Integer.Sparse.eval row19052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19052, Integer.Sparse.eval_collectBalanced, rawRowCheck19052]

def rawRow19053 : Integer.Sparse Key := [(key2520, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2456, 4), (key2561, 4), (key2531, 4), (key2561, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2456, 4), (key2361, 4), (key2456, 4)]

theorem rawRowCheck19053 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form5 = rawRow19053 := by decide +kernel

def row19053 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19053 : row19053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19053 := by decide +kernel

theorem rowEval19053 (x : Key → ℝ) : Integer.Sparse.eval row19053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19053, Integer.Sparse.eval_collectBalanced, rawRowCheck19053]

def rawRow19054 : Integer.Sparse Key := [(key2520, 4), (key2520, 4), (key2459, 4), (key2517, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2517, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2361, 4), (key2561, 4), (key2531, 4), (key2531, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2364, 4), (key2456, 4), (key2456, 4), (key2361, 4)]

theorem rawRowCheck19054 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form5 = rawRow19054 := by decide +kernel

def row19054 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19054 : row19054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19054 := by decide +kernel

theorem rowEval19054 (x : Key → ℝ) : Integer.Sparse.eval row19054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19054, Integer.Sparse.eval_collectBalanced, rawRowCheck19054]

def rawRow19055 : Integer.Sparse Key := [(key2531, 4), (key2531, 4), (key2531, 4), (key2561, 4), (key2561, 4), (key2561, 4), (key2364, 4), (key2364, 4), (key2364, 4), (key2459, 4), (key2459, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2361, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2517, 4), (key2517, 4)]

theorem rawRowCheck19055 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19055 := by decide +kernel

def row19055 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19055 : row19055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19055 := by decide +kernel

theorem rowEval19055 (x : Key → ℝ) : Integer.Sparse.eval row19055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19055, Integer.Sparse.eval_collectBalanced, rawRowCheck19055]

def rawRow19056 : Integer.Sparse Key := [(key2531, 4), (key2561, 4), (key2561, 4), (key2531, 4), (key2531, 4), (key2561, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2364, 4), (key2459, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2456, 4)]

theorem rawRowCheck19056 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form5 = rawRow19056 := by decide +kernel

def row19056 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19056 : row19056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19056 := by decide +kernel

theorem rowEval19056 (x : Key → ℝ) : Integer.Sparse.eval row19056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19056, Integer.Sparse.eval_collectBalanced, rawRowCheck19056]

def rawRow19057 : Integer.Sparse Key := [(key2561, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2456, 4), (key2517, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2361, 4), (key2456, 4)]

theorem rawRowCheck19057 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form5 = rawRow19057 := by decide +kernel

def row19057 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19057 : row19057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19057 := by decide +kernel

theorem rowEval19057 (x : Key → ℝ) : Integer.Sparse.eval row19057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19057, Integer.Sparse.eval_collectBalanced, rawRowCheck19057]

def rawRow19058 : Integer.Sparse Key := [(key2561, 4), (key2561, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2531, 4), (key2520, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2364, 4), (key2517, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2361, 4)]

theorem rawRowCheck19058 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form5 = rawRow19058 := by decide +kernel

def row19058 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

theorem rowCheck19058 : row19058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19058 := by decide +kernel

theorem rowEval19058 (x : Key → ℝ) : Integer.Sparse.eval row19058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19058, Integer.Sparse.eval_collectBalanced, rawRowCheck19058]

def rawRow19059 : Integer.Sparse Key := [(key2353, 6), (key2356, 6), (key2356, 6), (key2356, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2527, 6), (key2527, 6), (key2527, 6), (key2558, 6)]

theorem rawRowCheck19059 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form6 = rawRow19059 := by decide +kernel

def row19059 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

theorem rowCheck19059 : row19059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19059 := by decide +kernel

theorem rowEval19059 (x : Key → ℝ) : Integer.Sparse.eval row19059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19059, Integer.Sparse.eval_collectBalanced, rawRowCheck19059]

def rawRow19060 : Integer.Sparse Key := [(key2356, 6), (key2353, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2527, 6)]

theorem rawRowCheck19060 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form6 = rawRow19060 := by decide +kernel

def row19060 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

theorem rowCheck19060 : row19060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19060 := by decide +kernel

theorem rowEval19060 (x : Key → ℝ) : Integer.Sparse.eval row19060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19060, Integer.Sparse.eval_collectBalanced, rawRowCheck19060]

def rawRow19061 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2353, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2527, 6)]

theorem rawRowCheck19061 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form6 = rawRow19061 := by decide +kernel

def row19061 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

theorem rowCheck19061 : row19061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19061 := by decide +kernel

theorem rowEval19061 (x : Key → ℝ) : Integer.Sparse.eval row19061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19061, Integer.Sparse.eval_collectBalanced, rawRowCheck19061]

def rawRow19062 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2356, 6), (key2353, 6), (key2513, 6), (key2513, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2527, 6)]

theorem rawRowCheck19062 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19062 := by decide +kernel

def row19062 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

theorem rowCheck19062 : row19062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19062 := by decide +kernel

theorem rowEval19062 (x : Key → ℝ) : Integer.Sparse.eval row19062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19062, Integer.Sparse.eval_collectBalanced, rawRowCheck19062]

def rawRow19063 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2353, 6), (key2356, 6), (key2356, 6), (key2448, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6)]

theorem rawRowCheck19063 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form6 = rawRow19063 := by decide +kernel

def row19063 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

theorem rowCheck19063 : row19063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19063 := by decide +kernel

theorem rowEval19063 (x : Key → ℝ) : Integer.Sparse.eval row19063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19063, Integer.Sparse.eval_collectBalanced, rawRowCheck19063]

def rawRow19064 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2353, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2451, 6)]

theorem rawRowCheck19064 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form6 = rawRow19064 := by decide +kernel

def row19064 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

theorem rowCheck19064 : row19064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19064 := by decide +kernel

theorem rowEval19064 (x : Key → ℝ) : Integer.Sparse.eval row19064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19064, Integer.Sparse.eval_collectBalanced, rawRowCheck19064]

def rawRow19065 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2356, 6), (key2353, 6), (key2513, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2451, 6)]

theorem rawRowCheck19065 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form6 = rawRow19065 := by decide +kernel

def row19065 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

theorem rowCheck19065 : row19065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19065 := by decide +kernel

theorem rowEval19065 (x : Key → ℝ) : Integer.Sparse.eval row19065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19065, Integer.Sparse.eval_collectBalanced, rawRowCheck19065]

def rawRow19066 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2353, 6), (key2356, 6), (key2448, 6), (key2513, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2513, 6)]

theorem rawRowCheck19066 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form6 = rawRow19066 := by decide +kernel

def row19066 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

theorem rowCheck19066 : row19066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19066 := by decide +kernel

theorem rowEval19066 (x : Key → ℝ) : Integer.Sparse.eval row19066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19066, Integer.Sparse.eval_collectBalanced, rawRowCheck19066]

def rawRow19067 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2353, 6), (key2513, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2513, 6), (key2451, 6)]

theorem rawRowCheck19067 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form6 = rawRow19067 := by decide +kernel

def row19067 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

theorem rowCheck19067 : row19067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19067 := by decide +kernel

theorem rowEval19067 (x : Key → ℝ) : Integer.Sparse.eval row19067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19067, Integer.Sparse.eval_collectBalanced, rawRowCheck19067]

def rawRow19068 : Integer.Sparse Key := [(key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2353, 6), (key2558, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2513, 6)]

theorem rawRowCheck19068 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form6 = rawRow19068 := by decide +kernel

def row19068 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 36), (key2558, 6)]

theorem rowCheck19068 : row19068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19068 := by decide +kernel

theorem rowEval19068 (x : Key → ℝ) : Integer.Sparse.eval row19068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19068, Integer.Sparse.eval_collectBalanced, rawRowCheck19068]

def rawRow19069 : Integer.Sparse Key := [(key2513, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2558, 6), (key2353, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6)]

theorem rawRowCheck19069 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form6 = rawRow19069 := by decide +kernel

def row19069 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 36), (key2558, 6)]

theorem rowCheck19069 : row19069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19069 := by decide +kernel

theorem rowEval19069 (x : Key → ℝ) : Integer.Sparse.eval row19069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form6) x := by
  rw [rowCheck19069, Integer.Sparse.eval_collectBalanced, rawRowCheck19069]

def rawRow19070 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2513, 6), (key2353, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6)]

theorem rawRowCheck19070 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form6 = rawRow19070 := by decide +kernel

def row19070 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

theorem rowCheck19070 : row19070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19070 := by decide +kernel

theorem rowEval19070 (x : Key → ℝ) : Integer.Sparse.eval row19070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19070, Integer.Sparse.eval_collectBalanced, rawRowCheck19070]

def rawRow19071 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2513, 6), (key2356, 6), (key2448, 6), (key2353, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2356, 6)]

theorem rawRowCheck19071 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form6 = rawRow19071 := by decide +kernel

def row19071 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

theorem rowCheck19071 : row19071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19071 := by decide +kernel

theorem rowEval19071 (x : Key → ℝ) : Integer.Sparse.eval row19071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form6) x := by
  rw [rowCheck19071, Integer.Sparse.eval_collectBalanced, rawRowCheck19071]

end MUB6.Certificate.GramRows

end OAI

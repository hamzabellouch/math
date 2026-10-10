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

def rawRow13952 : Integer.Sparse Key := [(key1086, -2), (key1091, -2), (key1162, -2), (key1091, 6), (key1086, -2), (key1091, -2), (key1162, -2), (key972, 2), (key977, 2), (key1086, 2), (key1181, 2), (key1162, 2), (key1218, 2), (key977, -2), (key1091, -2), (key1181, -2), (key1091, 6), (key977, -2), (key1091, -2), (key1181, -2)]

theorem rawRowCheck13952 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13952 := by decide +kernel

def row13952 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck13952 : row13952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13952 := by decide +kernel

theorem rowEval13952 (x : Key → ℝ) : Integer.Sparse.eval row13952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13952, Integer.Sparse.eval_collectBalanced, rawRowCheck13952]

def rawRow13953 : Integer.Sparse Key := [(key1091, -2), (key1086, -2), (key1162, -2), (key1091, 6), (key1091, -2), (key1086, -2), (key1162, -2), (key977, 2), (key972, 2), (key1181, 2), (key1086, 2), (key1218, 2), (key1162, 2), (key977, -2), (key1181, -2), (key1091, -2), (key1091, 6), (key977, -2), (key1181, -2), (key1091, -2)]

theorem rawRowCheck13953 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13953 := by decide +kernel

def row13953 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck13953 : row13953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13953 := by decide +kernel

theorem rowEval13953 (x : Key → ℝ) : Integer.Sparse.eval row13953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13953, Integer.Sparse.eval_collectBalanced, rawRowCheck13953]

def rawRow13954 : Integer.Sparse Key := [(key1086, -2), (key1162, -2), (key1091, -2), (key1091, 6), (key1086, -2), (key1162, -2), (key1091, -2), (key1086, 2), (key1162, 2), (key972, 2), (key1218, 2), (key977, 2), (key1181, 2), (key1091, -2), (key977, -2), (key1181, -2), (key1091, 6), (key1091, -2), (key977, -2), (key1181, -2)]

theorem rawRowCheck13954 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13954 := by decide +kernel

def row13954 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck13954 : row13954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13954 := by decide +kernel

theorem rowEval13954 (x : Key → ℝ) : Integer.Sparse.eval row13954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13954, Integer.Sparse.eval_collectBalanced, rawRowCheck13954]

def rawRow13955 : Integer.Sparse Key := [(key1162, -2), (key1086, -2), (key1091, -2), (key1091, 6), (key1162, -2), (key1086, -2), (key1091, -2), (key1162, 2), (key1086, 2), (key1218, 2), (key972, 2), (key1181, 2), (key977, 2), (key1091, -2), (key1181, -2), (key977, -2), (key1091, 6), (key1091, -2), (key1181, -2), (key977, -2)]

theorem rawRowCheck13955 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13955 := by decide +kernel

def row13955 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck13955 : row13955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13955 := by decide +kernel

theorem rowEval13955 (x : Key → ℝ) : Integer.Sparse.eval row13955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13955, Integer.Sparse.eval_collectBalanced, rawRowCheck13955]

def rawRow13956 : Integer.Sparse Key := [(key1091, -2), (key1162, -2), (key1086, -2), (key1091, 6), (key1091, -2), (key1162, -2), (key1086, -2), (key1181, 2), (key1218, 2), (key977, 2), (key1162, 2), (key972, 2), (key1086, 2), (key1181, -2), (key977, -2), (key1091, -2), (key1091, 6), (key1181, -2), (key977, -2), (key1091, -2)]

theorem rawRowCheck13956 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13956 := by decide +kernel

def row13956 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck13956 : row13956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13956 := by decide +kernel

theorem rowEval13956 (x : Key → ℝ) : Integer.Sparse.eval row13956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13956, Integer.Sparse.eval_collectBalanced, rawRowCheck13956]

def rawRow13957 : Integer.Sparse Key := [(key1162, -2), (key1091, -2), (key1086, -2), (key1091, 6), (key1162, -2), (key1091, -2), (key1086, -2), (key1218, 2), (key1181, 2), (key1162, 2), (key977, 2), (key1086, 2), (key972, 2), (key1181, -2), (key1091, -2), (key977, -2), (key1091, 6), (key1181, -2), (key1091, -2), (key977, -2)]

theorem rawRowCheck13957 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13957 := by decide +kernel

def row13957 : Integer.Sparse Key := [(key972, 2), (key977, -2), (key1086, -2), (key1091, 4), (key1162, -2), (key1181, -2), (key1218, 2)]

theorem rowCheck13957 : row13957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13957 := by decide +kernel

theorem rowEval13957 (x : Key → ℝ) : Integer.Sparse.eval row13957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13957, Integer.Sparse.eval_collectBalanced, rawRowCheck13957]

def rawRow13958 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1162, -2), (key1086, 6), (key1181, -2), (key1181, -2), (key1218, -2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1181, 6), (key977, -2), (key1091, -2), (key1091, -2)]

theorem rawRowCheck13958 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13958 := by decide +kernel

def row13958 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13958 : row13958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13958 := by decide +kernel

theorem rowEval13958 (x : Key → ℝ) : Integer.Sparse.eval row13958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13958, Integer.Sparse.eval_collectBalanced, rawRowCheck13958]

def rawRow13959 : Integer.Sparse Key := [(key1091, -2), (key1162, -2), (key1091, -2), (key1086, 6), (key1181, -2), (key1218, -2), (key1181, -2), (key1091, 2), (key1162, 2), (key977, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1181, 6), (key1091, -2), (key977, -2), (key1091, -2)]

theorem rawRowCheck13959 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13959 := by decide +kernel

def row13959 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13959 : row13959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13959 := by decide +kernel

theorem rowEval13959 (x : Key → ℝ) : Integer.Sparse.eval row13959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13959, Integer.Sparse.eval_collectBalanced, rawRowCheck13959]

def rawRow13960 : Integer.Sparse Key := [(key1162, -2), (key1091, -2), (key1091, -2), (key1086, 6), (key1218, -2), (key1181, -2), (key1181, -2), (key1162, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1091, 2), (key977, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1181, 6), (key1091, -2), (key1091, -2), (key977, -2)]

theorem rawRowCheck13960 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13960 := by decide +kernel

def row13960 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13960 : row13960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13960 := by decide +kernel

theorem rowEval13960 (x : Key → ℝ) : Integer.Sparse.eval row13960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13960, Integer.Sparse.eval_collectBalanced, rawRowCheck13960]

def rawRow13961 : Integer.Sparse Key := [(key1181, -2), (key1181, -2), (key1181, -2), (key1218, 6), (key977, -2), (key977, -2), (key977, -2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1162, -2), (key1162, -2), (key1162, -2), (key972, 6), (key1086, -2), (key1086, -2), (key1086, -2)]

theorem rawRowCheck13961 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13961 := by decide +kernel

def row13961 : Integer.Sparse Key := [(key972, 6), (key977, -6), (key1086, -6), (key1091, 12), (key1162, -6), (key1181, -6), (key1218, 6)]

theorem rowCheck13961 : row13961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13961 := by decide +kernel

theorem rowEval13961 (x : Key → ℝ) : Integer.Sparse.eval row13961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13961, Integer.Sparse.eval_collectBalanced, rawRowCheck13961]

def rawRow13962 : Integer.Sparse Key := [(key1181, -2), (key1181, -2), (key1218, -2), (key1181, 6), (key1091, -2), (key1091, -2), (key1162, -2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key977, -2), (key1091, -2), (key1091, -2), (key1086, 6), (key972, -2), (key1086, -2), (key1086, -2)]

theorem rawRowCheck13962 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13962 := by decide +kernel

def row13962 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13962 : row13962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13962 := by decide +kernel

theorem rowEval13962 (x : Key → ℝ) : Integer.Sparse.eval row13962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13962, Integer.Sparse.eval_collectBalanced, rawRowCheck13962]

def rawRow13963 : Integer.Sparse Key := [(key1181, -2), (key1218, -2), (key1181, -2), (key1181, 6), (key1091, -2), (key1162, -2), (key1091, -2), (key1091, 2), (key1162, 2), (key977, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1091, -2), (key977, -2), (key1091, -2), (key1086, 6), (key1086, -2), (key972, -2), (key1086, -2)]

theorem rawRowCheck13963 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13963 := by decide +kernel

def row13963 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13963 : row13963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13963 := by decide +kernel

theorem rowEval13963 (x : Key → ℝ) : Integer.Sparse.eval row13963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13963, Integer.Sparse.eval_collectBalanced, rawRowCheck13963]

def rawRow13964 : Integer.Sparse Key := [(key1218, -2), (key1181, -2), (key1181, -2), (key1181, 6), (key1162, -2), (key1091, -2), (key1091, -2), (key1162, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1091, 2), (key977, 2), (key1091, -2), (key1091, -2), (key977, -2), (key1086, 6), (key1086, -2), (key1086, -2), (key972, -2)]

theorem rawRowCheck13964 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13964 := by decide +kernel

def row13964 : Integer.Sparse Key := [(key972, -2), (key977, 2), (key1086, 2), (key1091, -4), (key1162, 2), (key1181, 2), (key1218, -2)]

theorem rowCheck13964 : row13964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13964 := by decide +kernel

theorem rowEval13964 (x : Key → ℝ) : Integer.Sparse.eval row13964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13964, Integer.Sparse.eval_collectBalanced, rawRowCheck13964]

def rawRow13965 : Integer.Sparse Key := [(key2354, -2), (key2358, -2), (key2358, -2), (key2358, 6), (key2449, -2), (key2453, -2), (key2453, -2), (key2449, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2529, 2), (key2453, -2), (key2453, -2), (key2529, -2), (key2514, 6), (key2514, -2), (key2514, -2), (key2559, -2)]

theorem rawRowCheck13965 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13965 := by decide +kernel

def row13965 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13965 : row13965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13965 := by decide +kernel

theorem rowEval13965 (x : Key → ℝ) : Integer.Sparse.eval row13965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13965, Integer.Sparse.eval_collectBalanced, rawRowCheck13965]

def rawRow13966 : Integer.Sparse Key := [(key2358, -2), (key2354, -2), (key2358, -2), (key2358, 6), (key2453, -2), (key2449, -2), (key2453, -2), (key2453, 2), (key2449, 2), (key2529, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2453, -2), (key2529, -2), (key2453, -2), (key2514, 6), (key2514, -2), (key2559, -2), (key2514, -2)]

theorem rawRowCheck13966 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13966 := by decide +kernel

def row13966 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13966 : row13966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13966 := by decide +kernel

theorem rowEval13966 (x : Key → ℝ) : Integer.Sparse.eval row13966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13966, Integer.Sparse.eval_collectBalanced, rawRowCheck13966]

def rawRow13967 : Integer.Sparse Key := [(key2358, -2), (key2358, -2), (key2354, -2), (key2358, 6), (key2453, -2), (key2453, -2), (key2449, -2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2529, -2), (key2453, -2), (key2453, -2), (key2514, 6), (key2559, -2), (key2514, -2), (key2514, -2)]

theorem rawRowCheck13967 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13967 := by decide +kernel

def row13967 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13967 : row13967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13967 := by decide +kernel

theorem rowEval13967 (x : Key → ℝ) : Integer.Sparse.eval row13967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13967, Integer.Sparse.eval_collectBalanced, rawRowCheck13967]

def rawRow13968 : Integer.Sparse Key := [(key2358, -2), (key2358, -2), (key2358, -2), (key2354, 6), (key2529, -2), (key2529, -2), (key2529, -2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2449, -2), (key2449, -2), (key2449, -2), (key2559, 6), (key2514, -2), (key2514, -2), (key2514, -2)]

theorem rawRowCheck13968 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13968 := by decide +kernel

def row13968 : Integer.Sparse Key := [(key2354, 6), (key2358, -6), (key2449, -6), (key2453, 12), (key2514, -6), (key2529, -6), (key2559, 6)]

theorem rowCheck13968 : row13968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13968 := by decide +kernel

theorem rowEval13968 (x : Key → ℝ) : Integer.Sparse.eval row13968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13968, Integer.Sparse.eval_collectBalanced, rawRowCheck13968]

def rawRow13969 : Integer.Sparse Key := [(key2449, -2), (key2453, -2), (key2453, -2), (key2514, 6), (key2354, -2), (key2358, -2), (key2358, -2), (key2449, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2529, 2), (key2514, -2), (key2514, -2), (key2559, -2), (key2358, 6), (key2453, -2), (key2453, -2), (key2529, -2)]

theorem rawRowCheck13969 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13969 := by decide +kernel

def row13969 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13969 : row13969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13969 := by decide +kernel

theorem rowEval13969 (x : Key → ℝ) : Integer.Sparse.eval row13969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13969, Integer.Sparse.eval_collectBalanced, rawRowCheck13969]

def rawRow13970 : Integer.Sparse Key := [(key2453, -2), (key2449, -2), (key2453, -2), (key2514, 6), (key2358, -2), (key2354, -2), (key2358, -2), (key2453, 2), (key2449, 2), (key2529, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2514, -2), (key2559, -2), (key2514, -2), (key2358, 6), (key2453, -2), (key2529, -2), (key2453, -2)]

theorem rawRowCheck13970 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13970 := by decide +kernel

def row13970 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13970 : row13970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13970 := by decide +kernel

theorem rowEval13970 (x : Key → ℝ) : Integer.Sparse.eval row13970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13970, Integer.Sparse.eval_collectBalanced, rawRowCheck13970]

def rawRow13971 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2449, -2), (key2514, 6), (key2358, -2), (key2358, -2), (key2354, -2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2559, -2), (key2514, -2), (key2514, -2), (key2358, 6), (key2529, -2), (key2453, -2), (key2453, -2)]

theorem rawRowCheck13971 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13971 := by decide +kernel

def row13971 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13971 : row13971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13971 := by decide +kernel

theorem rowEval13971 (x : Key → ℝ) : Integer.Sparse.eval row13971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13971, Integer.Sparse.eval_collectBalanced, rawRowCheck13971]

def rawRow13972 : Integer.Sparse Key := [(key2449, -2), (key2453, -2), (key2514, -2), (key2453, 6), (key2449, -2), (key2453, -2), (key2514, -2), (key2354, 2), (key2358, 2), (key2449, 2), (key2529, 2), (key2514, 2), (key2559, 2), (key2358, -2), (key2453, -2), (key2529, -2), (key2453, 6), (key2358, -2), (key2453, -2), (key2529, -2)]

theorem rawRowCheck13972 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13972 := by decide +kernel

def row13972 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck13972 : row13972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13972 := by decide +kernel

theorem rowEval13972 (x : Key → ℝ) : Integer.Sparse.eval row13972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13972, Integer.Sparse.eval_collectBalanced, rawRowCheck13972]

def rawRow13973 : Integer.Sparse Key := [(key2453, -2), (key2449, -2), (key2514, -2), (key2453, 6), (key2453, -2), (key2449, -2), (key2514, -2), (key2358, 2), (key2354, 2), (key2529, 2), (key2449, 2), (key2559, 2), (key2514, 2), (key2358, -2), (key2529, -2), (key2453, -2), (key2453, 6), (key2358, -2), (key2529, -2), (key2453, -2)]

theorem rawRowCheck13973 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13973 := by decide +kernel

def row13973 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck13973 : row13973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13973 := by decide +kernel

theorem rowEval13973 (x : Key → ℝ) : Integer.Sparse.eval row13973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13973, Integer.Sparse.eval_collectBalanced, rawRowCheck13973]

def rawRow13974 : Integer.Sparse Key := [(key2449, -2), (key2514, -2), (key2453, -2), (key2453, 6), (key2449, -2), (key2514, -2), (key2453, -2), (key2449, 2), (key2514, 2), (key2354, 2), (key2559, 2), (key2358, 2), (key2529, 2), (key2453, -2), (key2358, -2), (key2529, -2), (key2453, 6), (key2453, -2), (key2358, -2), (key2529, -2)]

theorem rawRowCheck13974 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13974 := by decide +kernel

def row13974 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck13974 : row13974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13974 := by decide +kernel

theorem rowEval13974 (x : Key → ℝ) : Integer.Sparse.eval row13974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13974, Integer.Sparse.eval_collectBalanced, rawRowCheck13974]

def rawRow13975 : Integer.Sparse Key := [(key2514, -2), (key2449, -2), (key2453, -2), (key2453, 6), (key2514, -2), (key2449, -2), (key2453, -2), (key2514, 2), (key2449, 2), (key2559, 2), (key2354, 2), (key2529, 2), (key2358, 2), (key2453, -2), (key2529, -2), (key2358, -2), (key2453, 6), (key2453, -2), (key2529, -2), (key2358, -2)]

theorem rawRowCheck13975 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13975 := by decide +kernel

def row13975 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck13975 : row13975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13975 := by decide +kernel

theorem rowEval13975 (x : Key → ℝ) : Integer.Sparse.eval row13975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13975, Integer.Sparse.eval_collectBalanced, rawRowCheck13975]

def rawRow13976 : Integer.Sparse Key := [(key2453, -2), (key2514, -2), (key2449, -2), (key2453, 6), (key2453, -2), (key2514, -2), (key2449, -2), (key2529, 2), (key2559, 2), (key2358, 2), (key2514, 2), (key2354, 2), (key2449, 2), (key2529, -2), (key2358, -2), (key2453, -2), (key2453, 6), (key2529, -2), (key2358, -2), (key2453, -2)]

theorem rawRowCheck13976 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13976 := by decide +kernel

def row13976 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck13976 : row13976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13976 := by decide +kernel

theorem rowEval13976 (x : Key → ℝ) : Integer.Sparse.eval row13976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13976, Integer.Sparse.eval_collectBalanced, rawRowCheck13976]

def rawRow13977 : Integer.Sparse Key := [(key2514, -2), (key2453, -2), (key2449, -2), (key2453, 6), (key2514, -2), (key2453, -2), (key2449, -2), (key2559, 2), (key2529, 2), (key2514, 2), (key2358, 2), (key2449, 2), (key2354, 2), (key2529, -2), (key2453, -2), (key2358, -2), (key2453, 6), (key2529, -2), (key2453, -2), (key2358, -2)]

theorem rawRowCheck13977 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13977 := by decide +kernel

def row13977 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2453, 4), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck13977 : row13977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13977 := by decide +kernel

theorem rowEval13977 (x : Key → ℝ) : Integer.Sparse.eval row13977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13977, Integer.Sparse.eval_collectBalanced, rawRowCheck13977]

def rawRow13978 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2514, -2), (key2449, 6), (key2529, -2), (key2529, -2), (key2559, -2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2354, -2), (key2449, -2), (key2449, -2), (key2529, 6), (key2358, -2), (key2453, -2), (key2453, -2)]

theorem rawRowCheck13978 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13978 := by decide +kernel

def row13978 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13978 : row13978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13978 := by decide +kernel

theorem rowEval13978 (x : Key → ℝ) : Integer.Sparse.eval row13978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13978, Integer.Sparse.eval_collectBalanced, rawRowCheck13978]

def rawRow13979 : Integer.Sparse Key := [(key2453, -2), (key2514, -2), (key2453, -2), (key2449, 6), (key2529, -2), (key2559, -2), (key2529, -2), (key2453, 2), (key2514, 2), (key2358, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2449, -2), (key2354, -2), (key2449, -2), (key2529, 6), (key2453, -2), (key2358, -2), (key2453, -2)]

theorem rawRowCheck13979 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13979 := by decide +kernel

def row13979 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13979 : row13979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13979 := by decide +kernel

theorem rowEval13979 (x : Key → ℝ) : Integer.Sparse.eval row13979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13979, Integer.Sparse.eval_collectBalanced, rawRowCheck13979]

def rawRow13980 : Integer.Sparse Key := [(key2514, -2), (key2453, -2), (key2453, -2), (key2449, 6), (key2559, -2), (key2529, -2), (key2529, -2), (key2514, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2358, 2), (key2449, -2), (key2449, -2), (key2354, -2), (key2529, 6), (key2453, -2), (key2453, -2), (key2358, -2)]

theorem rawRowCheck13980 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13980 := by decide +kernel

def row13980 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13980 : row13980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13980 := by decide +kernel

theorem rowEval13980 (x : Key → ℝ) : Integer.Sparse.eval row13980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13980, Integer.Sparse.eval_collectBalanced, rawRowCheck13980]

def rawRow13981 : Integer.Sparse Key := [(key2529, -2), (key2529, -2), (key2529, -2), (key2559, 6), (key2358, -2), (key2358, -2), (key2358, -2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2514, -2), (key2514, -2), (key2514, -2), (key2354, 6), (key2449, -2), (key2449, -2), (key2449, -2)]

theorem rawRowCheck13981 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13981 := by decide +kernel

def row13981 : Integer.Sparse Key := [(key2354, 6), (key2358, -6), (key2449, -6), (key2453, 12), (key2514, -6), (key2529, -6), (key2559, 6)]

theorem rowCheck13981 : row13981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13981 := by decide +kernel

theorem rowEval13981 (x : Key → ℝ) : Integer.Sparse.eval row13981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13981, Integer.Sparse.eval_collectBalanced, rawRowCheck13981]

def rawRow13982 : Integer.Sparse Key := [(key2529, -2), (key2529, -2), (key2559, -2), (key2529, 6), (key2453, -2), (key2453, -2), (key2514, -2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2358, -2), (key2453, -2), (key2453, -2), (key2449, 6), (key2354, -2), (key2449, -2), (key2449, -2)]

theorem rawRowCheck13982 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13982 := by decide +kernel

def row13982 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13982 : row13982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13982 := by decide +kernel

theorem rowEval13982 (x : Key → ℝ) : Integer.Sparse.eval row13982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13982, Integer.Sparse.eval_collectBalanced, rawRowCheck13982]

def rawRow13983 : Integer.Sparse Key := [(key2529, -2), (key2559, -2), (key2529, -2), (key2529, 6), (key2453, -2), (key2514, -2), (key2453, -2), (key2453, 2), (key2514, 2), (key2358, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2453, -2), (key2358, -2), (key2453, -2), (key2449, 6), (key2449, -2), (key2354, -2), (key2449, -2)]

theorem rawRowCheck13983 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13983 := by decide +kernel

def row13983 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13983 : row13983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13983 := by decide +kernel

theorem rowEval13983 (x : Key → ℝ) : Integer.Sparse.eval row13983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13983, Integer.Sparse.eval_collectBalanced, rawRowCheck13983]

def rawRow13984 : Integer.Sparse Key := [(key2559, -2), (key2529, -2), (key2529, -2), (key2529, 6), (key2514, -2), (key2453, -2), (key2453, -2), (key2514, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2358, 2), (key2453, -2), (key2453, -2), (key2358, -2), (key2449, 6), (key2449, -2), (key2449, -2), (key2354, -2)]

theorem rawRowCheck13984 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13984 := by decide +kernel

def row13984 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2453, -4), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck13984 : row13984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13984 := by decide +kernel

theorem rowEval13984 (x : Key → ℝ) : Integer.Sparse.eval row13984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13984, Integer.Sparse.eval_collectBalanced, rawRowCheck13984]

def rawRow13985 : Integer.Sparse Key := [(key2369, 6), (key2369, -2), (key2369, -2), (key2384, -2), (key2397, 6), (key2397, -2), (key2397, -2), (key2431, -2), (key2463, -2), (key2463, -2), (key2474, -2), (key2463, -2), (key2463, -2), (key2497, -2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2474, 2), (key2497, 2)]

theorem rawRowCheck13985 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13985 := by decide +kernel

def row13985 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck13985 : row13985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13985 := by decide +kernel

theorem rowEval13985 (x : Key → ℝ) : Integer.Sparse.eval row13985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13985, Integer.Sparse.eval_collectBalanced, rawRowCheck13985]

def rawRow13986 : Integer.Sparse Key := [(key2369, 6), (key2369, -2), (key2384, -2), (key2369, -2), (key2397, 6), (key2397, -2), (key2431, -2), (key2397, -2), (key2463, -2), (key2474, -2), (key2463, -2), (key2463, -2), (key2497, -2), (key2463, -2), (key2474, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2474, 2)]

theorem rawRowCheck13986 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13986 := by decide +kernel

def row13986 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck13986 : row13986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13986 := by decide +kernel

theorem rowEval13986 (x : Key → ℝ) : Integer.Sparse.eval row13986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13986, Integer.Sparse.eval_collectBalanced, rawRowCheck13986]

def rawRow13987 : Integer.Sparse Key := [(key2369, 6), (key2384, -2), (key2369, -2), (key2369, -2), (key2397, 6), (key2431, -2), (key2397, -2), (key2397, -2), (key2474, -2), (key2463, -2), (key2463, -2), (key2497, -2), (key2463, -2), (key2463, -2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck13987 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13987 := by decide +kernel

def row13987 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck13987 : row13987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13987 := by decide +kernel

theorem rowEval13987 (x : Key → ℝ) : Integer.Sparse.eval row13987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13987, Integer.Sparse.eval_collectBalanced, rawRowCheck13987]

def rawRow13988 : Integer.Sparse Key := [(key2384, 6), (key2369, -2), (key2369, -2), (key2369, -2), (key2431, 6), (key2397, -2), (key2397, -2), (key2397, -2), (key2497, -2), (key2497, -2), (key2497, -2), (key2474, -2), (key2474, -2), (key2474, -2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck13988 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13988 := by decide +kernel

def row13988 : Integer.Sparse Key := [(key2369, -6), (key2384, 6), (key2397, -6), (key2431, 6), (key2463, 12), (key2474, -6), (key2497, -6)]

theorem rowCheck13988 : row13988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13988 := by decide +kernel

theorem rowEval13988 (x : Key → ℝ) : Integer.Sparse.eval row13988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13988, Integer.Sparse.eval_collectBalanced, rawRowCheck13988]

def rawRow13989 : Integer.Sparse Key := [(key2397, 6), (key2463, -2), (key2463, -2), (key2474, -2), (key2369, 6), (key2463, -2), (key2463, -2), (key2497, -2), (key2369, -2), (key2369, -2), (key2384, -2), (key2397, -2), (key2397, -2), (key2431, -2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2474, 2), (key2497, 2)]

theorem rawRowCheck13989 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13989 := by decide +kernel

def row13989 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck13989 : row13989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13989 := by decide +kernel

theorem rowEval13989 (x : Key → ℝ) : Integer.Sparse.eval row13989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13989, Integer.Sparse.eval_collectBalanced, rawRowCheck13989]

def rawRow13990 : Integer.Sparse Key := [(key2397, 6), (key2463, -2), (key2474, -2), (key2463, -2), (key2369, 6), (key2463, -2), (key2497, -2), (key2463, -2), (key2369, -2), (key2384, -2), (key2369, -2), (key2397, -2), (key2431, -2), (key2397, -2), (key2474, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2474, 2)]

theorem rawRowCheck13990 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13990 := by decide +kernel

def row13990 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck13990 : row13990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13990 := by decide +kernel

theorem rowEval13990 (x : Key → ℝ) : Integer.Sparse.eval row13990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13990, Integer.Sparse.eval_collectBalanced, rawRowCheck13990]

def rawRow13991 : Integer.Sparse Key := [(key2397, 6), (key2474, -2), (key2463, -2), (key2463, -2), (key2369, 6), (key2497, -2), (key2463, -2), (key2463, -2), (key2384, -2), (key2369, -2), (key2369, -2), (key2431, -2), (key2397, -2), (key2397, -2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck13991 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13991 := by decide +kernel

def row13991 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck13991 : row13991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13991 := by decide +kernel

theorem rowEval13991 (x : Key → ℝ) : Integer.Sparse.eval row13991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13991, Integer.Sparse.eval_collectBalanced, rawRowCheck13991]

def rawRow13992 : Integer.Sparse Key := [(key2463, 6), (key2397, -2), (key2463, -2), (key2474, -2), (key2463, 6), (key2369, -2), (key2463, -2), (key2497, -2), (key2397, -2), (key2463, -2), (key2474, -2), (key2369, -2), (key2463, -2), (key2497, -2), (key2369, 2), (key2384, 2), (key2397, 2), (key2431, 2), (key2474, 2), (key2497, 2)]

theorem rawRowCheck13992 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13992 := by decide +kernel

def row13992 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

theorem rowCheck13992 : row13992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13992 := by decide +kernel

theorem rowEval13992 (x : Key → ℝ) : Integer.Sparse.eval row13992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13992, Integer.Sparse.eval_collectBalanced, rawRowCheck13992]

def rawRow13993 : Integer.Sparse Key := [(key2463, 6), (key2397, -2), (key2474, -2), (key2463, -2), (key2463, 6), (key2369, -2), (key2497, -2), (key2463, -2), (key2397, -2), (key2474, -2), (key2463, -2), (key2369, -2), (key2497, -2), (key2463, -2), (key2384, 2), (key2369, 2), (key2431, 2), (key2397, 2), (key2497, 2), (key2474, 2)]

theorem rawRowCheck13993 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13993 := by decide +kernel

def row13993 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

theorem rowCheck13993 : row13993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13993 := by decide +kernel

theorem rowEval13993 (x : Key → ℝ) : Integer.Sparse.eval row13993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13993, Integer.Sparse.eval_collectBalanced, rawRowCheck13993]

def rawRow13994 : Integer.Sparse Key := [(key2463, 6), (key2463, -2), (key2397, -2), (key2474, -2), (key2463, 6), (key2463, -2), (key2369, -2), (key2497, -2), (key2463, -2), (key2397, -2), (key2474, -2), (key2463, -2), (key2369, -2), (key2497, -2), (key2397, 2), (key2474, 2), (key2369, 2), (key2497, 2), (key2384, 2), (key2431, 2)]

theorem rawRowCheck13994 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13994 := by decide +kernel

def row13994 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

theorem rowCheck13994 : row13994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13994 := by decide +kernel

theorem rowEval13994 (x : Key → ℝ) : Integer.Sparse.eval row13994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13994, Integer.Sparse.eval_collectBalanced, rawRowCheck13994]

def rawRow13995 : Integer.Sparse Key := [(key2463, 6), (key2463, -2), (key2474, -2), (key2397, -2), (key2463, 6), (key2463, -2), (key2497, -2), (key2369, -2), (key2463, -2), (key2474, -2), (key2397, -2), (key2463, -2), (key2497, -2), (key2369, -2), (key2474, 2), (key2397, 2), (key2497, 2), (key2369, 2), (key2431, 2), (key2384, 2)]

theorem rawRowCheck13995 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13995 := by decide +kernel

def row13995 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

theorem rowCheck13995 : row13995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13995 := by decide +kernel

theorem rowEval13995 (x : Key → ℝ) : Integer.Sparse.eval row13995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13995, Integer.Sparse.eval_collectBalanced, rawRowCheck13995]

def rawRow13996 : Integer.Sparse Key := [(key2463, 6), (key2474, -2), (key2397, -2), (key2463, -2), (key2463, 6), (key2497, -2), (key2369, -2), (key2463, -2), (key2474, -2), (key2397, -2), (key2463, -2), (key2497, -2), (key2369, -2), (key2463, -2), (key2431, 2), (key2497, 2), (key2384, 2), (key2474, 2), (key2369, 2), (key2397, 2)]

theorem rawRowCheck13996 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13996 := by decide +kernel

def row13996 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

theorem rowCheck13996 : row13996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13996 := by decide +kernel

theorem rowEval13996 (x : Key → ℝ) : Integer.Sparse.eval row13996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13996, Integer.Sparse.eval_collectBalanced, rawRowCheck13996]

def rawRow13997 : Integer.Sparse Key := [(key2463, 6), (key2474, -2), (key2463, -2), (key2397, -2), (key2463, 6), (key2497, -2), (key2463, -2), (key2369, -2), (key2474, -2), (key2463, -2), (key2397, -2), (key2497, -2), (key2463, -2), (key2369, -2), (key2497, 2), (key2431, 2), (key2474, 2), (key2384, 2), (key2397, 2), (key2369, 2)]

theorem rawRowCheck13997 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13997 := by decide +kernel

def row13997 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, -2), (key2431, 2), (key2463, 4), (key2474, -2), (key2497, -2)]

theorem rowCheck13997 : row13997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13997 := by decide +kernel

theorem rowEval13997 (x : Key → ℝ) : Integer.Sparse.eval row13997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13997, Integer.Sparse.eval_collectBalanced, rawRowCheck13997]

def rawRow13998 : Integer.Sparse Key := [(key2474, 6), (key2397, -2), (key2463, -2), (key2463, -2), (key2497, 6), (key2369, -2), (key2463, -2), (key2463, -2), (key2431, -2), (key2497, -2), (key2497, -2), (key2384, -2), (key2474, -2), (key2474, -2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck13998 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13998 := by decide +kernel

def row13998 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck13998 : row13998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13998 := by decide +kernel

theorem rowEval13998 (x : Key → ℝ) : Integer.Sparse.eval row13998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13998, Integer.Sparse.eval_collectBalanced, rawRowCheck13998]

def rawRow13999 : Integer.Sparse Key := [(key2474, 6), (key2463, -2), (key2397, -2), (key2463, -2), (key2497, 6), (key2463, -2), (key2369, -2), (key2463, -2), (key2497, -2), (key2431, -2), (key2497, -2), (key2474, -2), (key2384, -2), (key2474, -2), (key2397, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2397, 2)]

theorem rawRowCheck13999 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13999 := by decide +kernel

def row13999 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck13999 : row13999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13999 := by decide +kernel

theorem rowEval13999 (x : Key → ℝ) : Integer.Sparse.eval row13999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13999, Integer.Sparse.eval_collectBalanced, rawRowCheck13999]

def rawRow14000 : Integer.Sparse Key := [(key2474, 6), (key2463, -2), (key2463, -2), (key2397, -2), (key2497, 6), (key2463, -2), (key2463, -2), (key2369, -2), (key2497, -2), (key2497, -2), (key2431, -2), (key2474, -2), (key2474, -2), (key2384, -2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2397, 2), (key2369, 2)]

theorem rawRowCheck14000 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3 = rawRow14000 := by decide +kernel

def row14000 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck14000 : row14000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14000 := by decide +kernel

theorem rowEval14000 (x : Key → ℝ) : Integer.Sparse.eval row14000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck14000, Integer.Sparse.eval_collectBalanced, rawRowCheck14000]

def rawRow14001 : Integer.Sparse Key := [(key2431, 6), (key2497, -2), (key2497, -2), (key2497, -2), (key2384, 6), (key2474, -2), (key2474, -2), (key2474, -2), (key2369, -2), (key2369, -2), (key2369, -2), (key2397, -2), (key2397, -2), (key2397, -2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck14001 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3 = rawRow14001 := by decide +kernel

def row14001 : Integer.Sparse Key := [(key2369, -6), (key2384, 6), (key2397, -6), (key2431, 6), (key2463, 12), (key2474, -6), (key2497, -6)]

theorem rowCheck14001 : row14001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14001 := by decide +kernel

theorem rowEval14001 (x : Key → ℝ) : Integer.Sparse.eval row14001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14001, Integer.Sparse.eval_collectBalanced, rawRowCheck14001]

def rawRow14002 : Integer.Sparse Key := [(key2497, 6), (key2431, -2), (key2497, -2), (key2497, -2), (key2474, 6), (key2384, -2), (key2474, -2), (key2474, -2), (key2397, -2), (key2463, -2), (key2463, -2), (key2369, -2), (key2463, -2), (key2463, -2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck14002 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3 = rawRow14002 := by decide +kernel

def row14002 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck14002 : row14002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14002 := by decide +kernel

theorem rowEval14002 (x : Key → ℝ) : Integer.Sparse.eval row14002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14002, Integer.Sparse.eval_collectBalanced, rawRowCheck14002]

def rawRow14003 : Integer.Sparse Key := [(key2497, 6), (key2497, -2), (key2431, -2), (key2497, -2), (key2474, 6), (key2474, -2), (key2384, -2), (key2474, -2), (key2463, -2), (key2397, -2), (key2463, -2), (key2463, -2), (key2369, -2), (key2463, -2), (key2397, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2397, 2)]

theorem rawRowCheck14003 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3 = rawRow14003 := by decide +kernel

def row14003 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck14003 : row14003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14003 := by decide +kernel

theorem rowEval14003 (x : Key → ℝ) : Integer.Sparse.eval row14003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck14003, Integer.Sparse.eval_collectBalanced, rawRowCheck14003]

def rawRow14004 : Integer.Sparse Key := [(key2497, 6), (key2497, -2), (key2497, -2), (key2431, -2), (key2474, 6), (key2474, -2), (key2474, -2), (key2384, -2), (key2463, -2), (key2463, -2), (key2397, -2), (key2463, -2), (key2463, -2), (key2369, -2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2397, 2), (key2369, 2)]

theorem rawRowCheck14004 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3 = rawRow14004 := by decide +kernel

def row14004 : Integer.Sparse Key := [(key2369, 2), (key2384, -2), (key2397, 2), (key2431, -2), (key2463, -4), (key2474, 2), (key2497, 2)]

theorem rowCheck14004 : row14004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14004 := by decide +kernel

theorem rowEval14004 (x : Key → ℝ) : Integer.Sparse.eval row14004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck14004, Integer.Sparse.eval_collectBalanced, rawRowCheck14004]

def rawRow14005 : Integer.Sparse Key := [(key971, -2), (key975, -2), (key975, -2), (key975, 6), (key1085, -2), (key1089, -2), (key1089, -2), (key1085, 2), (key1089, 2), (key1085, 2), (key1179, 2), (key1089, 2), (key1179, 2), (key1089, -2), (key1089, -2), (key1179, -2), (key1161, 6), (key1161, -2), (key1161, -2), (key1217, -2)]

theorem rawRowCheck14005 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14005 := by decide +kernel

def row14005 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14005 : row14005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14005 := by decide +kernel

theorem rowEval14005 (x : Key → ℝ) : Integer.Sparse.eval row14005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14005, Integer.Sparse.eval_collectBalanced, rawRowCheck14005]

def rawRow14006 : Integer.Sparse Key := [(key975, -2), (key971, -2), (key975, -2), (key975, 6), (key1089, -2), (key1085, -2), (key1089, -2), (key1089, 2), (key1085, 2), (key1179, 2), (key1085, 2), (key1179, 2), (key1089, 2), (key1089, -2), (key1179, -2), (key1089, -2), (key1161, 6), (key1161, -2), (key1217, -2), (key1161, -2)]

theorem rawRowCheck14006 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14006 := by decide +kernel

def row14006 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14006 : row14006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14006 := by decide +kernel

theorem rowEval14006 (x : Key → ℝ) : Integer.Sparse.eval row14006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14006, Integer.Sparse.eval_collectBalanced, rawRowCheck14006]

def rawRow14007 : Integer.Sparse Key := [(key975, -2), (key975, -2), (key971, -2), (key975, 6), (key1089, -2), (key1089, -2), (key1085, -2), (key1179, 2), (key1179, 2), (key1089, 2), (key1089, 2), (key1085, 2), (key1085, 2), (key1179, -2), (key1089, -2), (key1089, -2), (key1161, 6), (key1217, -2), (key1161, -2), (key1161, -2)]

theorem rawRowCheck14007 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14007 := by decide +kernel

def row14007 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14007 : row14007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14007 := by decide +kernel

theorem rowEval14007 (x : Key → ℝ) : Integer.Sparse.eval row14007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14007, Integer.Sparse.eval_collectBalanced, rawRowCheck14007]

def rawRow14008 : Integer.Sparse Key := [(key975, -2), (key975, -2), (key975, -2), (key971, 6), (key1179, -2), (key1179, -2), (key1179, -2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1085, -2), (key1085, -2), (key1085, -2), (key1217, 6), (key1161, -2), (key1161, -2), (key1161, -2)]

theorem rawRowCheck14008 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14008 := by decide +kernel

def row14008 : Integer.Sparse Key := [(key971, 6), (key975, -6), (key1085, -6), (key1089, 12), (key1161, -6), (key1179, -6), (key1217, 6)]

theorem rowCheck14008 : row14008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14008 := by decide +kernel

theorem rowEval14008 (x : Key → ℝ) : Integer.Sparse.eval row14008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14008, Integer.Sparse.eval_collectBalanced, rawRowCheck14008]

def rawRow14009 : Integer.Sparse Key := [(key1085, -2), (key1089, -2), (key1089, -2), (key1161, 6), (key971, -2), (key975, -2), (key975, -2), (key1085, 2), (key1089, 2), (key1085, 2), (key1179, 2), (key1089, 2), (key1179, 2), (key1161, -2), (key1161, -2), (key1217, -2), (key975, 6), (key1089, -2), (key1089, -2), (key1179, -2)]

theorem rawRowCheck14009 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14009 := by decide +kernel

def row14009 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14009 : row14009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14009 := by decide +kernel

theorem rowEval14009 (x : Key → ℝ) : Integer.Sparse.eval row14009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14009, Integer.Sparse.eval_collectBalanced, rawRowCheck14009]

def rawRow14010 : Integer.Sparse Key := [(key1089, -2), (key1085, -2), (key1089, -2), (key1161, 6), (key975, -2), (key971, -2), (key975, -2), (key1089, 2), (key1085, 2), (key1179, 2), (key1085, 2), (key1179, 2), (key1089, 2), (key1161, -2), (key1217, -2), (key1161, -2), (key975, 6), (key1089, -2), (key1179, -2), (key1089, -2)]

theorem rawRowCheck14010 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14010 := by decide +kernel

def row14010 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14010 : row14010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14010 := by decide +kernel

theorem rowEval14010 (x : Key → ℝ) : Integer.Sparse.eval row14010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14010, Integer.Sparse.eval_collectBalanced, rawRowCheck14010]

def rawRow14011 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1085, -2), (key1161, 6), (key975, -2), (key975, -2), (key971, -2), (key1179, 2), (key1179, 2), (key1089, 2), (key1089, 2), (key1085, 2), (key1085, 2), (key1217, -2), (key1161, -2), (key1161, -2), (key975, 6), (key1179, -2), (key1089, -2), (key1089, -2)]

theorem rawRowCheck14011 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14011 := by decide +kernel

def row14011 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14011 : row14011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14011 := by decide +kernel

theorem rowEval14011 (x : Key → ℝ) : Integer.Sparse.eval row14011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14011, Integer.Sparse.eval_collectBalanced, rawRowCheck14011]

def rawRow14012 : Integer.Sparse Key := [(key1085, -2), (key1089, -2), (key1161, -2), (key1089, 6), (key1085, -2), (key1089, -2), (key1161, -2), (key971, 2), (key975, 2), (key1085, 2), (key1179, 2), (key1161, 2), (key1217, 2), (key975, -2), (key1089, -2), (key1179, -2), (key1089, 6), (key975, -2), (key1089, -2), (key1179, -2)]

theorem rawRowCheck14012 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow14012 := by decide +kernel

def row14012 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck14012 : row14012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14012 := by decide +kernel

theorem rowEval14012 (x : Key → ℝ) : Integer.Sparse.eval row14012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14012, Integer.Sparse.eval_collectBalanced, rawRowCheck14012]

def rawRow14013 : Integer.Sparse Key := [(key1089, -2), (key1085, -2), (key1161, -2), (key1089, 6), (key1089, -2), (key1085, -2), (key1161, -2), (key975, 2), (key971, 2), (key1179, 2), (key1085, 2), (key1217, 2), (key1161, 2), (key975, -2), (key1179, -2), (key1089, -2), (key1089, 6), (key975, -2), (key1179, -2), (key1089, -2)]

theorem rawRowCheck14013 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow14013 := by decide +kernel

def row14013 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck14013 : row14013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14013 := by decide +kernel

theorem rowEval14013 (x : Key → ℝ) : Integer.Sparse.eval row14013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14013, Integer.Sparse.eval_collectBalanced, rawRowCheck14013]

def rawRow14014 : Integer.Sparse Key := [(key1085, -2), (key1161, -2), (key1089, -2), (key1089, 6), (key1085, -2), (key1161, -2), (key1089, -2), (key1085, 2), (key1161, 2), (key971, 2), (key1217, 2), (key975, 2), (key1179, 2), (key1089, -2), (key975, -2), (key1179, -2), (key1089, 6), (key1089, -2), (key975, -2), (key1179, -2)]

theorem rawRowCheck14014 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow14014 := by decide +kernel

def row14014 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck14014 : row14014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14014 := by decide +kernel

theorem rowEval14014 (x : Key → ℝ) : Integer.Sparse.eval row14014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14014, Integer.Sparse.eval_collectBalanced, rawRowCheck14014]

def rawRow14015 : Integer.Sparse Key := [(key1161, -2), (key1085, -2), (key1089, -2), (key1089, 6), (key1161, -2), (key1085, -2), (key1089, -2), (key1161, 2), (key1085, 2), (key1217, 2), (key971, 2), (key1179, 2), (key975, 2), (key1089, -2), (key1179, -2), (key975, -2), (key1089, 6), (key1089, -2), (key1179, -2), (key975, -2)]

theorem rawRowCheck14015 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow14015 := by decide +kernel

def row14015 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck14015 : row14015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14015 := by decide +kernel

theorem rowEval14015 (x : Key → ℝ) : Integer.Sparse.eval row14015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14015, Integer.Sparse.eval_collectBalanced, rawRowCheck14015]

def rawRow14016 : Integer.Sparse Key := [(key1089, -2), (key1161, -2), (key1085, -2), (key1089, 6), (key1089, -2), (key1161, -2), (key1085, -2), (key1179, 2), (key1217, 2), (key975, 2), (key1161, 2), (key971, 2), (key1085, 2), (key1179, -2), (key975, -2), (key1089, -2), (key1089, 6), (key1179, -2), (key975, -2), (key1089, -2)]

theorem rawRowCheck14016 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow14016 := by decide +kernel

def row14016 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck14016 : row14016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14016 := by decide +kernel

theorem rowEval14016 (x : Key → ℝ) : Integer.Sparse.eval row14016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14016, Integer.Sparse.eval_collectBalanced, rawRowCheck14016]

def rawRow14017 : Integer.Sparse Key := [(key1161, -2), (key1089, -2), (key1085, -2), (key1089, 6), (key1161, -2), (key1089, -2), (key1085, -2), (key1217, 2), (key1179, 2), (key1161, 2), (key975, 2), (key1085, 2), (key971, 2), (key1179, -2), (key1089, -2), (key975, -2), (key1089, 6), (key1179, -2), (key1089, -2), (key975, -2)]

theorem rawRowCheck14017 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow14017 := by decide +kernel

def row14017 : Integer.Sparse Key := [(key971, 2), (key975, -2), (key1085, -2), (key1089, 4), (key1161, -2), (key1179, -2), (key1217, 2)]

theorem rowCheck14017 : row14017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14017 := by decide +kernel

theorem rowEval14017 (x : Key → ℝ) : Integer.Sparse.eval row14017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14017, Integer.Sparse.eval_collectBalanced, rawRowCheck14017]

def rawRow14018 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1161, -2), (key1085, 6), (key1179, -2), (key1179, -2), (key1217, -2), (key975, 2), (key975, 2), (key1089, 2), (key1089, 2), (key1161, 2), (key1161, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1179, 6), (key975, -2), (key1089, -2), (key1089, -2)]

theorem rawRowCheck14018 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow14018 := by decide +kernel

def row14018 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14018 : row14018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14018 := by decide +kernel

theorem rowEval14018 (x : Key → ℝ) : Integer.Sparse.eval row14018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14018, Integer.Sparse.eval_collectBalanced, rawRowCheck14018]

def rawRow14019 : Integer.Sparse Key := [(key1089, -2), (key1161, -2), (key1089, -2), (key1085, 6), (key1179, -2), (key1217, -2), (key1179, -2), (key1089, 2), (key1161, 2), (key975, 2), (key1161, 2), (key975, 2), (key1089, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1179, 6), (key1089, -2), (key975, -2), (key1089, -2)]

theorem rawRowCheck14019 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow14019 := by decide +kernel

def row14019 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14019 : row14019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14019 := by decide +kernel

theorem rowEval14019 (x : Key → ℝ) : Integer.Sparse.eval row14019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14019, Integer.Sparse.eval_collectBalanced, rawRowCheck14019]

def rawRow14020 : Integer.Sparse Key := [(key1161, -2), (key1089, -2), (key1089, -2), (key1085, 6), (key1217, -2), (key1179, -2), (key1179, -2), (key1161, 2), (key1089, 2), (key1161, 2), (key975, 2), (key1089, 2), (key975, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1179, 6), (key1089, -2), (key1089, -2), (key975, -2)]

theorem rawRowCheck14020 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow14020 := by decide +kernel

def row14020 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14020 : row14020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14020 := by decide +kernel

theorem rowEval14020 (x : Key → ℝ) : Integer.Sparse.eval row14020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14020, Integer.Sparse.eval_collectBalanced, rawRowCheck14020]

def rawRow14021 : Integer.Sparse Key := [(key1179, -2), (key1179, -2), (key1179, -2), (key1217, 6), (key975, -2), (key975, -2), (key975, -2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1089, 2), (key1161, -2), (key1161, -2), (key1161, -2), (key971, 6), (key1085, -2), (key1085, -2), (key1085, -2)]

theorem rawRowCheck14021 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14021 := by decide +kernel

def row14021 : Integer.Sparse Key := [(key971, 6), (key975, -6), (key1085, -6), (key1089, 12), (key1161, -6), (key1179, -6), (key1217, 6)]

theorem rowCheck14021 : row14021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14021 := by decide +kernel

theorem rowEval14021 (x : Key → ℝ) : Integer.Sparse.eval row14021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14021, Integer.Sparse.eval_collectBalanced, rawRowCheck14021]

def rawRow14022 : Integer.Sparse Key := [(key1179, -2), (key1179, -2), (key1217, -2), (key1179, 6), (key1089, -2), (key1089, -2), (key1161, -2), (key975, 2), (key975, 2), (key1089, 2), (key1089, 2), (key1161, 2), (key1161, 2), (key975, -2), (key1089, -2), (key1089, -2), (key1085, 6), (key971, -2), (key1085, -2), (key1085, -2)]

theorem rawRowCheck14022 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4 = rawRow14022 := by decide +kernel

def row14022 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14022 : row14022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14022 := by decide +kernel

theorem rowEval14022 (x : Key → ℝ) : Integer.Sparse.eval row14022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14022, Integer.Sparse.eval_collectBalanced, rawRowCheck14022]

def rawRow14023 : Integer.Sparse Key := [(key1179, -2), (key1217, -2), (key1179, -2), (key1179, 6), (key1089, -2), (key1161, -2), (key1089, -2), (key1089, 2), (key1161, 2), (key975, 2), (key1161, 2), (key975, 2), (key1089, 2), (key1089, -2), (key975, -2), (key1089, -2), (key1085, 6), (key1085, -2), (key971, -2), (key1085, -2)]

theorem rawRowCheck14023 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4 = rawRow14023 := by decide +kernel

def row14023 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14023 : row14023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14023 := by decide +kernel

theorem rowEval14023 (x : Key → ℝ) : Integer.Sparse.eval row14023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14023, Integer.Sparse.eval_collectBalanced, rawRowCheck14023]

def rawRow14024 : Integer.Sparse Key := [(key1217, -2), (key1179, -2), (key1179, -2), (key1179, 6), (key1161, -2), (key1089, -2), (key1089, -2), (key1161, 2), (key1089, 2), (key1161, 2), (key975, 2), (key1089, 2), (key975, 2), (key1089, -2), (key1089, -2), (key975, -2), (key1085, 6), (key1085, -2), (key1085, -2), (key971, -2)]

theorem rawRowCheck14024 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4 = rawRow14024 := by decide +kernel

def row14024 : Integer.Sparse Key := [(key971, -2), (key975, 2), (key1085, 2), (key1089, -4), (key1161, 2), (key1179, 2), (key1217, -2)]

theorem rowCheck14024 : row14024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14024 := by decide +kernel

theorem rowEval14024 (x : Key → ℝ) : Integer.Sparse.eval row14024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14024, Integer.Sparse.eval_collectBalanced, rawRowCheck14024]

def rawRow14025 : Integer.Sparse Key := [(key1095, 4), (key1095, 4), (key1184, 4), (key1095, -2), (key1099, -2), (key1095, -2), (key1184, -2), (key1099, -2), (key1184, -2), (key1166, -2), (key1170, -2), (key1166, -2), (key1221, -2), (key1170, -2), (key1221, -2), (key1170, 4), (key1170, 4), (key1221, 4)]

theorem rawRowCheck14025 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14025 := by decide +kernel

def row14025 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14025 : row14025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14025 := by decide +kernel

theorem rowEval14025 (x : Key → ℝ) : Integer.Sparse.eval row14025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14025, Integer.Sparse.eval_collectBalanced, rawRowCheck14025]

def rawRow14026 : Integer.Sparse Key := [(key1095, 4), (key1184, 4), (key1095, 4), (key1099, -2), (key1095, -2), (key1184, -2), (key1095, -2), (key1184, -2), (key1099, -2), (key1170, -2), (key1166, -2), (key1221, -2), (key1166, -2), (key1221, -2), (key1170, -2), (key1170, 4), (key1221, 4), (key1170, 4)]

theorem rawRowCheck14026 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14026 := by decide +kernel

def row14026 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14026 : row14026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14026 := by decide +kernel

theorem rowEval14026 (x : Key → ℝ) : Integer.Sparse.eval row14026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14026, Integer.Sparse.eval_collectBalanced, rawRowCheck14026]

def rawRow14027 : Integer.Sparse Key := [(key1184, 4), (key1095, 4), (key1095, 4), (key1184, -2), (key1184, -2), (key1099, -2), (key1099, -2), (key1095, -2), (key1095, -2), (key1221, -2), (key1221, -2), (key1170, -2), (key1170, -2), (key1166, -2), (key1166, -2), (key1221, 4), (key1170, 4), (key1170, 4)]

theorem rawRowCheck14027 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14027 := by decide +kernel

def row14027 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14027 : row14027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14027 := by decide +kernel

theorem rowEval14027 (x : Key → ℝ) : Integer.Sparse.eval row14027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14027, Integer.Sparse.eval_collectBalanced, rawRowCheck14027]

def rawRow14028 : Integer.Sparse Key := [(key1099, 4), (key1099, 4), (key1099, 4), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1166, 4), (key1166, 4), (key1166, 4)]

theorem rawRowCheck14028 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14028 := by decide +kernel

def row14028 : Integer.Sparse Key := [(key1095, -12), (key1099, 12), (key1166, 12), (key1170, -12)]

theorem rowCheck14028 : row14028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14028 := by decide +kernel

theorem rowEval14028 (x : Key → ℝ) : Integer.Sparse.eval row14028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14028, Integer.Sparse.eval_collectBalanced, rawRowCheck14028]

def rawRow14029 : Integer.Sparse Key := [(key1095, 4), (key1095, 4), (key1184, 4), (key1166, -2), (key1170, -2), (key1166, -2), (key1221, -2), (key1170, -2), (key1221, -2), (key1095, -2), (key1099, -2), (key1095, -2), (key1184, -2), (key1099, -2), (key1184, -2), (key1170, 4), (key1170, 4), (key1221, 4)]

theorem rawRowCheck14029 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14029 := by decide +kernel

def row14029 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14029 : row14029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14029 := by decide +kernel

theorem rowEval14029 (x : Key → ℝ) : Integer.Sparse.eval row14029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14029, Integer.Sparse.eval_collectBalanced, rawRowCheck14029]

def rawRow14030 : Integer.Sparse Key := [(key1095, 4), (key1184, 4), (key1095, 4), (key1170, -2), (key1166, -2), (key1221, -2), (key1166, -2), (key1221, -2), (key1170, -2), (key1099, -2), (key1095, -2), (key1184, -2), (key1095, -2), (key1184, -2), (key1099, -2), (key1170, 4), (key1221, 4), (key1170, 4)]

theorem rawRowCheck14030 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14030 := by decide +kernel

def row14030 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14030 : row14030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14030 := by decide +kernel

theorem rowEval14030 (x : Key → ℝ) : Integer.Sparse.eval row14030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14030, Integer.Sparse.eval_collectBalanced, rawRowCheck14030]

def rawRow14031 : Integer.Sparse Key := [(key1184, 4), (key1095, 4), (key1095, 4), (key1221, -2), (key1221, -2), (key1170, -2), (key1170, -2), (key1166, -2), (key1166, -2), (key1184, -2), (key1184, -2), (key1099, -2), (key1099, -2), (key1095, -2), (key1095, -2), (key1221, 4), (key1170, 4), (key1170, 4)]

theorem rawRowCheck14031 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14031 := by decide +kernel

def row14031 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14031 : row14031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14031 := by decide +kernel

theorem rowEval14031 (x : Key → ℝ) : Integer.Sparse.eval row14031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14031, Integer.Sparse.eval_collectBalanced, rawRowCheck14031]

def rawRow14032 : Integer.Sparse Key := [(key981, 4), (key1166, 4), (key1221, 4), (key981, -2), (key985, -2), (key1095, -2), (key1184, -2), (key1170, -2), (key1221, -2), (key981, -2), (key985, -2), (key1095, -2), (key1184, -2), (key1170, -2), (key1221, -2), (key985, 4), (key1099, 4), (key1184, 4)]

theorem rawRowCheck14032 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form5 = rawRow14032 := by decide +kernel

def row14032 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

theorem rowCheck14032 : row14032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14032 := by decide +kernel

theorem rowEval14032 (x : Key → ℝ) : Integer.Sparse.eval row14032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14032, Integer.Sparse.eval_collectBalanced, rawRowCheck14032]

def rawRow14033 : Integer.Sparse Key := [(key981, 4), (key1221, 4), (key1166, 4), (key985, -2), (key981, -2), (key1184, -2), (key1095, -2), (key1221, -2), (key1170, -2), (key985, -2), (key981, -2), (key1184, -2), (key1095, -2), (key1221, -2), (key1170, -2), (key985, 4), (key1184, 4), (key1099, 4)]

theorem rawRowCheck14033 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form5 = rawRow14033 := by decide +kernel

def row14033 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

theorem rowCheck14033 : row14033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14033 := by decide +kernel

theorem rowEval14033 (x : Key → ℝ) : Integer.Sparse.eval row14033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14033, Integer.Sparse.eval_collectBalanced, rawRowCheck14033]

def rawRow14034 : Integer.Sparse Key := [(key1166, 4), (key981, 4), (key1221, 4), (key1095, -2), (key1170, -2), (key981, -2), (key1221, -2), (key985, -2), (key1184, -2), (key1095, -2), (key1170, -2), (key981, -2), (key1221, -2), (key985, -2), (key1184, -2), (key1099, 4), (key985, 4), (key1184, 4)]

theorem rawRowCheck14034 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form5 = rawRow14034 := by decide +kernel

def row14034 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

theorem rowCheck14034 : row14034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14034 := by decide +kernel

theorem rowEval14034 (x : Key → ℝ) : Integer.Sparse.eval row14034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14034, Integer.Sparse.eval_collectBalanced, rawRowCheck14034]

def rawRow14035 : Integer.Sparse Key := [(key1166, 4), (key1221, 4), (key981, 4), (key1170, -2), (key1095, -2), (key1221, -2), (key981, -2), (key1184, -2), (key985, -2), (key1170, -2), (key1095, -2), (key1221, -2), (key981, -2), (key1184, -2), (key985, -2), (key1099, 4), (key1184, 4), (key985, 4)]

theorem rawRowCheck14035 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form5 = rawRow14035 := by decide +kernel

def row14035 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

theorem rowCheck14035 : row14035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14035 := by decide +kernel

theorem rowEval14035 (x : Key → ℝ) : Integer.Sparse.eval row14035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14035, Integer.Sparse.eval_collectBalanced, rawRowCheck14035]

def rawRow14036 : Integer.Sparse Key := [(key1221, 4), (key981, 4), (key1166, 4), (key1184, -2), (key1221, -2), (key985, -2), (key1170, -2), (key981, -2), (key1095, -2), (key1184, -2), (key1221, -2), (key985, -2), (key1170, -2), (key981, -2), (key1095, -2), (key1184, 4), (key985, 4), (key1099, 4)]

theorem rawRowCheck14036 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form5 = rawRow14036 := by decide +kernel

def row14036 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

theorem rowCheck14036 : row14036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14036 := by decide +kernel

theorem rowEval14036 (x : Key → ℝ) : Integer.Sparse.eval row14036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14036, Integer.Sparse.eval_collectBalanced, rawRowCheck14036]

def rawRow14037 : Integer.Sparse Key := [(key1221, 4), (key1166, 4), (key981, 4), (key1221, -2), (key1184, -2), (key1170, -2), (key985, -2), (key1095, -2), (key981, -2), (key1221, -2), (key1184, -2), (key1170, -2), (key985, -2), (key1095, -2), (key981, -2), (key1184, 4), (key1099, 4), (key985, 4)]

theorem rawRowCheck14037 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form5 = rawRow14037 := by decide +kernel

def row14037 : Integer.Sparse Key := [(key1095, -4), (key1099, 4), (key1166, 4), (key1170, -4)]

theorem rowCheck14037 : row14037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14037 := by decide +kernel

theorem rowEval14037 (x : Key → ℝ) : Integer.Sparse.eval row14037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14037, Integer.Sparse.eval_collectBalanced, rawRowCheck14037]

def rawRow14038 : Integer.Sparse Key := [(key985, 4), (key1170, 4), (key1170, 4), (key981, -2), (key981, -2), (key1095, -2), (key1095, -2), (key1166, -2), (key1166, -2), (key985, -2), (key985, -2), (key1099, -2), (key1099, -2), (key1170, -2), (key1170, -2), (key981, 4), (key1095, 4), (key1095, 4)]

theorem rawRowCheck14038 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form5 = rawRow14038 := by decide +kernel

def row14038 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14038 : row14038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14038 := by decide +kernel

theorem rowEval14038 (x : Key → ℝ) : Integer.Sparse.eval row14038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14038, Integer.Sparse.eval_collectBalanced, rawRowCheck14038]

def rawRow14039 : Integer.Sparse Key := [(key1170, 4), (key985, 4), (key1170, 4), (key1095, -2), (key1166, -2), (key981, -2), (key1166, -2), (key981, -2), (key1095, -2), (key1099, -2), (key1170, -2), (key985, -2), (key1170, -2), (key985, -2), (key1099, -2), (key1095, 4), (key981, 4), (key1095, 4)]

theorem rawRowCheck14039 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form5 = rawRow14039 := by decide +kernel

def row14039 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14039 : row14039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14039 := by decide +kernel

theorem rowEval14039 (x : Key → ℝ) : Integer.Sparse.eval row14039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14039, Integer.Sparse.eval_collectBalanced, rawRowCheck14039]

def rawRow14040 : Integer.Sparse Key := [(key1170, 4), (key1170, 4), (key985, 4), (key1166, -2), (key1095, -2), (key1166, -2), (key981, -2), (key1095, -2), (key981, -2), (key1170, -2), (key1099, -2), (key1170, -2), (key985, -2), (key1099, -2), (key985, -2), (key1095, 4), (key1095, 4), (key981, 4)]

theorem rawRowCheck14040 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form5 = rawRow14040 := by decide +kernel

def row14040 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14040 : row14040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14040 := by decide +kernel

theorem rowEval14040 (x : Key → ℝ) : Integer.Sparse.eval row14040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14040, Integer.Sparse.eval_collectBalanced, rawRowCheck14040]

def rawRow14041 : Integer.Sparse Key := [(key1099, 4), (key1099, 4), (key1099, 4), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1170, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1095, -2), (key1166, 4), (key1166, 4), (key1166, 4)]

theorem rawRowCheck14041 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14041 := by decide +kernel

def row14041 : Integer.Sparse Key := [(key1095, -12), (key1099, 12), (key1166, 12), (key1170, -12)]

theorem rowCheck14041 : row14041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14041 := by decide +kernel

theorem rowEval14041 (x : Key → ℝ) : Integer.Sparse.eval row14041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14041, Integer.Sparse.eval_collectBalanced, rawRowCheck14041]

def rawRow14042 : Integer.Sparse Key := [(key985, 4), (key1170, 4), (key1170, 4), (key985, -2), (key985, -2), (key1099, -2), (key1099, -2), (key1170, -2), (key1170, -2), (key981, -2), (key981, -2), (key1095, -2), (key1095, -2), (key1166, -2), (key1166, -2), (key981, 4), (key1095, 4), (key1095, 4)]

theorem rawRowCheck14042 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form5 = rawRow14042 := by decide +kernel

def row14042 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14042 : row14042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14042 := by decide +kernel

theorem rowEval14042 (x : Key → ℝ) : Integer.Sparse.eval row14042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14042, Integer.Sparse.eval_collectBalanced, rawRowCheck14042]

def rawRow14043 : Integer.Sparse Key := [(key1170, 4), (key985, 4), (key1170, 4), (key1099, -2), (key1170, -2), (key985, -2), (key1170, -2), (key985, -2), (key1099, -2), (key1095, -2), (key1166, -2), (key981, -2), (key1166, -2), (key981, -2), (key1095, -2), (key1095, 4), (key981, 4), (key1095, 4)]

theorem rawRowCheck14043 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form5 = rawRow14043 := by decide +kernel

def row14043 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14043 : row14043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14043 := by decide +kernel

theorem rowEval14043 (x : Key → ℝ) : Integer.Sparse.eval row14043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14043, Integer.Sparse.eval_collectBalanced, rawRowCheck14043]

def rawRow14044 : Integer.Sparse Key := [(key1170, 4), (key1170, 4), (key985, 4), (key1170, -2), (key1099, -2), (key1170, -2), (key985, -2), (key1099, -2), (key985, -2), (key1166, -2), (key1095, -2), (key1166, -2), (key981, -2), (key1095, -2), (key981, -2), (key1095, 4), (key1095, 4), (key981, 4)]

theorem rawRowCheck14044 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form5 = rawRow14044 := by decide +kernel

def row14044 : Integer.Sparse Key := [(key1095, 4), (key1099, -4), (key1166, -4), (key1170, 4)]

theorem rowCheck14044 : row14044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14044 := by decide +kernel

theorem rowEval14044 (x : Key → ℝ) : Integer.Sparse.eval row14044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14044, Integer.Sparse.eval_collectBalanced, rawRowCheck14044]

def rawRow14045 : Integer.Sparse Key := [(key2763, -1), (key2767, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2930, -1), (key2767, 2), (key2767, 2), (key2930, 2), (key2840, -1), (key2844, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2844, -1), (key2888, -1), (key2844, -1), (key2967, -1), (key2888, -1), (key2967, -1), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, -1), (key2909, -1), (key2875, -1), (key2988, -1), (key2909, -1), (key2988, -1)]

theorem rawRowCheck14045 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form6 = rawRow14045 := by decide +kernel

def row14045 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14045 : row14045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14045 := by decide +kernel

theorem rowEval14045 (x : Key → ℝ) : Integer.Sparse.eval row14045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14045, Integer.Sparse.eval_collectBalanced, rawRowCheck14045]

def rawRow14046 : Integer.Sparse Key := [(key2767, -1), (key2763, -1), (key2930, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2767, 2), (key2930, 2), (key2767, 2), (key2844, -1), (key2840, -1), (key2967, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2888, -1), (key2844, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2888, -1), (key2875, 2), (key2988, 2), (key2875, 2), (key2909, -1), (key2875, -1), (key2988, -1), (key2875, -1), (key2988, -1), (key2909, -1)]

theorem rawRowCheck14046 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form6 = rawRow14046 := by decide +kernel

def row14046 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14046 : row14046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14046 := by decide +kernel

theorem rowEval14046 (x : Key → ℝ) : Integer.Sparse.eval row14046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14046, Integer.Sparse.eval_collectBalanced, rawRowCheck14046]

def rawRow14047 : Integer.Sparse Key := [(key2930, -1), (key2930, -1), (key2767, -1), (key2767, -1), (key2763, -1), (key2763, -1), (key2930, 2), (key2767, 2), (key2767, 2), (key2967, -1), (key2967, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2967, -1), (key2967, -1), (key2888, -1), (key2888, -1), (key2844, -1), (key2844, -1), (key2988, 2), (key2875, 2), (key2875, 2), (key2988, -1), (key2988, -1), (key2909, -1), (key2909, -1), (key2875, -1), (key2875, -1)]

theorem rawRowCheck14047 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form6 = rawRow14047 := by decide +kernel

def row14047 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14047 : row14047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14047 := by decide +kernel

theorem rowEval14047 (x : Key → ℝ) : Integer.Sparse.eval row14047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14047, Integer.Sparse.eval_collectBalanced, rawRowCheck14047]

def rawRow14048 : Integer.Sparse Key := [(key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2763, 2), (key2763, 2), (key2763, 2), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2909, 2), (key2909, 2), (key2909, 2), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1)]

theorem rawRowCheck14048 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form6 = rawRow14048 := by decide +kernel

def row14048 : Integer.Sparse Key := [(key2763, 6), (key2767, -6), (key2840, -6), (key2844, 12), (key2875, -6), (key2888, -6), (key2909, 6)]

theorem rowCheck14048 : row14048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14048 := by decide +kernel

theorem rowEval14048 (x : Key → ℝ) : Integer.Sparse.eval row14048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14048, Integer.Sparse.eval_collectBalanced, rawRowCheck14048]

def rawRow14049 : Integer.Sparse Key := [(key2840, -1), (key2844, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2875, 2), (key2875, 2), (key2988, 2), (key2763, -1), (key2767, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2930, -1), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2875, -1), (key2909, -1), (key2875, -1), (key2988, -1), (key2909, -1), (key2988, -1), (key2767, 2), (key2767, 2), (key2930, 2), (key2844, -1), (key2888, -1), (key2844, -1), (key2967, -1), (key2888, -1), (key2967, -1)]

theorem rawRowCheck14049 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form6 = rawRow14049 := by decide +kernel

def row14049 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14049 : row14049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14049 := by decide +kernel

theorem rowEval14049 (x : Key → ℝ) : Integer.Sparse.eval row14049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14049, Integer.Sparse.eval_collectBalanced, rawRowCheck14049]

def rawRow14050 : Integer.Sparse Key := [(key2844, -1), (key2840, -1), (key2967, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2875, 2), (key2988, 2), (key2875, 2), (key2767, -1), (key2763, -1), (key2930, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2909, -1), (key2875, -1), (key2988, -1), (key2875, -1), (key2988, -1), (key2909, -1), (key2767, 2), (key2930, 2), (key2767, 2), (key2888, -1), (key2844, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2888, -1)]

theorem rawRowCheck14050 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form6 = rawRow14050 := by decide +kernel

def row14050 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14050 : row14050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14050 := by decide +kernel

theorem rowEval14050 (x : Key → ℝ) : Integer.Sparse.eval row14050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14050, Integer.Sparse.eval_collectBalanced, rawRowCheck14050]

def rawRow14051 : Integer.Sparse Key := [(key2967, -1), (key2967, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2988, 2), (key2875, 2), (key2875, 2), (key2930, -1), (key2930, -1), (key2767, -1), (key2767, -1), (key2763, -1), (key2763, -1), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2988, -1), (key2988, -1), (key2909, -1), (key2909, -1), (key2875, -1), (key2875, -1), (key2930, 2), (key2767, 2), (key2767, 2), (key2967, -1), (key2967, -1), (key2888, -1), (key2888, -1), (key2844, -1), (key2844, -1)]

theorem rawRowCheck14051 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form6 = rawRow14051 := by decide +kernel

def row14051 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14051 : row14051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14051 := by decide +kernel

theorem rowEval14051 (x : Key → ℝ) : Integer.Sparse.eval row14051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14051, Integer.Sparse.eval_collectBalanced, rawRowCheck14051]

def rawRow14052 : Integer.Sparse Key := [(key2584, -1), (key2588, -1), (key2840, -1), (key2967, -1), (key2875, -1), (key2988, -1), (key2588, 2), (key2844, 2), (key2967, 2), (key2584, -1), (key2588, -1), (key2840, -1), (key2967, -1), (key2875, -1), (key2988, -1), (key2584, 2), (key2599, 2), (key2763, 2), (key2930, 2), (key2909, 2), (key2988, 2), (key2588, -1), (key2599, -1), (key2767, -1), (key2930, -1), (key2888, -1), (key2967, -1), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, -1), (key2599, -1), (key2767, -1), (key2930, -1), (key2888, -1), (key2967, -1)]

theorem rawRowCheck14052 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form6 = rawRow14052 := by decide +kernel

def row14052 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

theorem rowCheck14052 : row14052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14052 := by decide +kernel

theorem rowEval14052 (x : Key → ℝ) : Integer.Sparse.eval row14052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14052, Integer.Sparse.eval_collectBalanced, rawRowCheck14052]

def rawRow14053 : Integer.Sparse Key := [(key2588, -1), (key2584, -1), (key2967, -1), (key2840, -1), (key2988, -1), (key2875, -1), (key2588, 2), (key2967, 2), (key2844, 2), (key2588, -1), (key2584, -1), (key2967, -1), (key2840, -1), (key2988, -1), (key2875, -1), (key2599, 2), (key2584, 2), (key2930, 2), (key2763, 2), (key2988, 2), (key2909, 2), (key2599, -1), (key2588, -1), (key2930, -1), (key2767, -1), (key2967, -1), (key2888, -1), (key2588, 2), (key2967, 2), (key2844, 2), (key2599, -1), (key2588, -1), (key2930, -1), (key2767, -1), (key2967, -1), (key2888, -1)]

theorem rawRowCheck14053 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form6 = rawRow14053 := by decide +kernel

def row14053 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

theorem rowCheck14053 : row14053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14053 := by decide +kernel

theorem rowEval14053 (x : Key → ℝ) : Integer.Sparse.eval row14053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14053, Integer.Sparse.eval_collectBalanced, rawRowCheck14053]

def rawRow14054 : Integer.Sparse Key := [(key2840, -1), (key2875, -1), (key2584, -1), (key2988, -1), (key2588, -1), (key2967, -1), (key2844, 2), (key2588, 2), (key2967, 2), (key2840, -1), (key2875, -1), (key2584, -1), (key2988, -1), (key2588, -1), (key2967, -1), (key2763, 2), (key2909, 2), (key2584, 2), (key2988, 2), (key2599, 2), (key2930, 2), (key2767, -1), (key2888, -1), (key2588, -1), (key2967, -1), (key2599, -1), (key2930, -1), (key2844, 2), (key2588, 2), (key2967, 2), (key2767, -1), (key2888, -1), (key2588, -1), (key2967, -1), (key2599, -1), (key2930, -1)]

theorem rawRowCheck14054 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form6 = rawRow14054 := by decide +kernel

def row14054 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

theorem rowCheck14054 : row14054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14054 := by decide +kernel

theorem rowEval14054 (x : Key → ℝ) : Integer.Sparse.eval row14054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14054, Integer.Sparse.eval_collectBalanced, rawRowCheck14054]

def rawRow14055 : Integer.Sparse Key := [(key2875, -1), (key2840, -1), (key2988, -1), (key2584, -1), (key2967, -1), (key2588, -1), (key2844, 2), (key2967, 2), (key2588, 2), (key2875, -1), (key2840, -1), (key2988, -1), (key2584, -1), (key2967, -1), (key2588, -1), (key2909, 2), (key2763, 2), (key2988, 2), (key2584, 2), (key2930, 2), (key2599, 2), (key2888, -1), (key2767, -1), (key2967, -1), (key2588, -1), (key2930, -1), (key2599, -1), (key2844, 2), (key2967, 2), (key2588, 2), (key2888, -1), (key2767, -1), (key2967, -1), (key2588, -1), (key2930, -1), (key2599, -1)]

theorem rawRowCheck14055 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form6 = rawRow14055 := by decide +kernel

def row14055 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

theorem rowCheck14055 : row14055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14055 := by decide +kernel

theorem rowEval14055 (x : Key → ℝ) : Integer.Sparse.eval row14055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form6) x := by
  rw [rowCheck14055, Integer.Sparse.eval_collectBalanced, rawRowCheck14055]

def rawRow14056 : Integer.Sparse Key := [(key2967, -1), (key2988, -1), (key2588, -1), (key2875, -1), (key2584, -1), (key2840, -1), (key2967, 2), (key2588, 2), (key2844, 2), (key2967, -1), (key2988, -1), (key2588, -1), (key2875, -1), (key2584, -1), (key2840, -1), (key2930, 2), (key2988, 2), (key2599, 2), (key2909, 2), (key2584, 2), (key2763, 2), (key2930, -1), (key2967, -1), (key2599, -1), (key2888, -1), (key2588, -1), (key2767, -1), (key2967, 2), (key2588, 2), (key2844, 2), (key2930, -1), (key2967, -1), (key2599, -1), (key2888, -1), (key2588, -1), (key2767, -1)]

theorem rawRowCheck14056 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form6 = rawRow14056 := by decide +kernel

def row14056 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

theorem rowCheck14056 : row14056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14056 := by decide +kernel

theorem rowEval14056 (x : Key → ℝ) : Integer.Sparse.eval row14056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14056, Integer.Sparse.eval_collectBalanced, rawRowCheck14056]

def rawRow14057 : Integer.Sparse Key := [(key2988, -1), (key2967, -1), (key2875, -1), (key2588, -1), (key2840, -1), (key2584, -1), (key2967, 2), (key2844, 2), (key2588, 2), (key2988, -1), (key2967, -1), (key2875, -1), (key2588, -1), (key2840, -1), (key2584, -1), (key2988, 2), (key2930, 2), (key2909, 2), (key2599, 2), (key2763, 2), (key2584, 2), (key2967, -1), (key2930, -1), (key2888, -1), (key2599, -1), (key2767, -1), (key2588, -1), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, -1), (key2930, -1), (key2888, -1), (key2599, -1), (key2767, -1), (key2588, -1)]

theorem rawRowCheck14057 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form6 = rawRow14057 := by decide +kernel

def row14057 : Integer.Sparse Key := [(key2763, 2), (key2767, -2), (key2840, -2), (key2844, 4), (key2875, -2), (key2888, -2), (key2909, 2)]

theorem rowCheck14057 : row14057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14057 := by decide +kernel

theorem rowEval14057 (x : Key → ℝ) : Integer.Sparse.eval row14057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form6) x := by
  rw [rowCheck14057, Integer.Sparse.eval_collectBalanced, rawRowCheck14057]

def rawRow14058 : Integer.Sparse Key := [(key2588, -1), (key2588, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2584, 2), (key2840, 2), (key2840, 2), (key2599, -1), (key2599, -1), (key2888, -1), (key2888, -1), (key2909, -1), (key2909, -1), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2584, -1), (key2584, -1), (key2763, -1), (key2763, -1), (key2840, -1), (key2840, -1), (key2599, 2), (key2888, 2), (key2888, 2), (key2588, -1), (key2588, -1), (key2767, -1), (key2767, -1), (key2844, -1), (key2844, -1)]

theorem rawRowCheck14058 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form6 = rawRow14058 := by decide +kernel

def row14058 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14058 : row14058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14058 := by decide +kernel

theorem rowEval14058 (x : Key → ℝ) : Integer.Sparse.eval row14058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14058, Integer.Sparse.eval_collectBalanced, rawRowCheck14058]

def rawRow14059 : Integer.Sparse Key := [(key2844, -1), (key2875, -1), (key2588, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2840, 2), (key2584, 2), (key2840, 2), (key2888, -1), (key2909, -1), (key2599, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2763, -1), (key2840, -1), (key2584, -1), (key2840, -1), (key2584, -1), (key2763, -1), (key2888, 2), (key2599, 2), (key2888, 2), (key2767, -1), (key2844, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2767, -1)]

theorem rawRowCheck14059 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form6 = rawRow14059 := by decide +kernel

def row14059 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14059 : row14059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14059 := by decide +kernel

theorem rowEval14059 (x : Key → ℝ) : Integer.Sparse.eval row14059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14059, Integer.Sparse.eval_collectBalanced, rawRowCheck14059]

def rawRow14060 : Integer.Sparse Key := [(key2875, -1), (key2844, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2840, 2), (key2840, 2), (key2584, 2), (key2909, -1), (key2888, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2599, -1), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2840, -1), (key2763, -1), (key2840, -1), (key2584, -1), (key2763, -1), (key2584, -1), (key2888, 2), (key2888, 2), (key2599, 2), (key2844, -1), (key2767, -1), (key2844, -1), (key2588, -1), (key2767, -1), (key2588, -1)]

theorem rawRowCheck14060 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form6 = rawRow14060 := by decide +kernel

def row14060 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14060 : row14060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14060 := by decide +kernel

theorem rowEval14060 (x : Key → ℝ) : Integer.Sparse.eval row14060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form6) x := by
  rw [rowCheck14060, Integer.Sparse.eval_collectBalanced, rawRowCheck14060]

def rawRow14061 : Integer.Sparse Key := [(key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2909, 2), (key2909, 2), (key2909, 2), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2875, -1), (key2763, 2), (key2763, 2), (key2763, 2), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1), (key2840, -1)]

theorem rawRowCheck14061 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form6 = rawRow14061 := by decide +kernel

def row14061 : Integer.Sparse Key := [(key2763, 6), (key2767, -6), (key2840, -6), (key2844, 12), (key2875, -6), (key2888, -6), (key2909, 6)]

theorem rowCheck14061 : row14061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14061 := by decide +kernel

theorem rowEval14061 (x : Key → ℝ) : Integer.Sparse.eval row14061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14061, Integer.Sparse.eval_collectBalanced, rawRowCheck14061]

def rawRow14062 : Integer.Sparse Key := [(key2599, -1), (key2599, -1), (key2888, -1), (key2888, -1), (key2909, -1), (key2909, -1), (key2599, 2), (key2888, 2), (key2888, 2), (key2588, -1), (key2588, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2588, -1), (key2588, -1), (key2767, -1), (key2767, -1), (key2844, -1), (key2844, -1), (key2584, 2), (key2840, 2), (key2840, 2), (key2584, -1), (key2584, -1), (key2763, -1), (key2763, -1), (key2840, -1), (key2840, -1)]

theorem rawRowCheck14062 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form6 = rawRow14062 := by decide +kernel

def row14062 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14062 : row14062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14062 := by decide +kernel

theorem rowEval14062 (x : Key → ℝ) : Integer.Sparse.eval row14062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14062, Integer.Sparse.eval_collectBalanced, rawRowCheck14062]

def rawRow14063 : Integer.Sparse Key := [(key2888, -1), (key2909, -1), (key2599, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2888, 2), (key2599, 2), (key2888, 2), (key2844, -1), (key2875, -1), (key2588, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2767, -1), (key2844, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2767, -1), (key2840, 2), (key2584, 2), (key2840, 2), (key2763, -1), (key2840, -1), (key2584, -1), (key2840, -1), (key2584, -1), (key2763, -1)]

theorem rawRowCheck14063 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form6 = rawRow14063 := by decide +kernel

def row14063 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14063 : row14063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14063 := by decide +kernel

theorem rowEval14063 (x : Key → ℝ) : Integer.Sparse.eval row14063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14063, Integer.Sparse.eval_collectBalanced, rawRowCheck14063]

def rawRow14064 : Integer.Sparse Key := [(key2909, -1), (key2888, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2599, -1), (key2888, 2), (key2888, 2), (key2599, 2), (key2875, -1), (key2844, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2844, -1), (key2767, -1), (key2844, -1), (key2588, -1), (key2767, -1), (key2588, -1), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, -1), (key2763, -1), (key2840, -1), (key2584, -1), (key2763, -1), (key2584, -1)]

theorem rawRowCheck14064 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form6 = rawRow14064 := by decide +kernel

def row14064 : Integer.Sparse Key := [(key2763, -2), (key2767, 2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, 2), (key2909, -2)]

theorem rowCheck14064 : row14064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14064 := by decide +kernel

theorem rowEval14064 (x : Key → ℝ) : Integer.Sparse.eval row14064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form6) x := by
  rw [rowCheck14064, Integer.Sparse.eval_collectBalanced, rawRowCheck14064]

def rawRow14065 : Integer.Sparse Key := [(key2413, 4), (key2413, 4), (key2422, 4), (key2413, -4), (key2422, -4), (key2422, -4), (key2486, -4), (key2490, -4), (key2490, -4), (key2490, 12)]

theorem rawRowCheck14065 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form7 = rawRow14065 := by decide +kernel

def row14065 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14065 : row14065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14065 := by decide +kernel

theorem rowEval14065 (x : Key → ℝ) : Integer.Sparse.eval row14065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14065, Integer.Sparse.eval_collectBalanced, rawRowCheck14065]

def rawRow14066 : Integer.Sparse Key := [(key2413, 4), (key2422, 4), (key2413, 4), (key2422, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2486, -4), (key2490, -4), (key2490, 12)]

theorem rawRowCheck14066 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form7 = rawRow14066 := by decide +kernel

def row14066 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14066 : row14066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14066 := by decide +kernel

theorem rowEval14066 (x : Key → ℝ) : Integer.Sparse.eval row14066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14066, Integer.Sparse.eval_collectBalanced, rawRowCheck14066]

def rawRow14067 : Integer.Sparse Key := [(key2422, 4), (key2413, 4), (key2413, 4), (key2422, -4), (key2422, -4), (key2413, -4), (key2490, -4), (key2490, -4), (key2486, -4), (key2490, 12)]

theorem rawRowCheck14067 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form7 = rawRow14067 := by decide +kernel

def row14067 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14067 : row14067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14067 := by decide +kernel

theorem rowEval14067 (x : Key → ℝ) : Integer.Sparse.eval row14067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14067, Integer.Sparse.eval_collectBalanced, rawRowCheck14067]

def rawRow14068 : Integer.Sparse Key := [(key2422, 4), (key2422, 4), (key2422, 4), (key2413, -4), (key2413, -4), (key2413, -4), (key2490, -4), (key2490, -4), (key2490, -4), (key2486, 12)]

theorem rawRowCheck14068 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form7 = rawRow14068 := by decide +kernel

def row14068 : Integer.Sparse Key := [(key2413, -12), (key2422, 12), (key2486, 12), (key2490, -12)]

theorem rowCheck14068 : row14068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14068 := by decide +kernel

theorem rowEval14068 (x : Key → ℝ) : Integer.Sparse.eval row14068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14068, Integer.Sparse.eval_collectBalanced, rawRowCheck14068]

def rawRow14069 : Integer.Sparse Key := [(key2413, 4), (key2413, 4), (key2422, 4), (key2486, -4), (key2490, -4), (key2490, -4), (key2413, -4), (key2422, -4), (key2422, -4), (key2490, 12)]

theorem rawRowCheck14069 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form7 = rawRow14069 := by decide +kernel

def row14069 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14069 : row14069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14069 := by decide +kernel

theorem rowEval14069 (x : Key → ℝ) : Integer.Sparse.eval row14069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14069, Integer.Sparse.eval_collectBalanced, rawRowCheck14069]

def rawRow14070 : Integer.Sparse Key := [(key2413, 4), (key2422, 4), (key2413, 4), (key2490, -4), (key2486, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2422, -4), (key2490, 12)]

theorem rawRowCheck14070 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form7 = rawRow14070 := by decide +kernel

def row14070 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14070 : row14070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14070 := by decide +kernel

theorem rowEval14070 (x : Key → ℝ) : Integer.Sparse.eval row14070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14070, Integer.Sparse.eval_collectBalanced, rawRowCheck14070]

def rawRow14071 : Integer.Sparse Key := [(key2422, 4), (key2413, 4), (key2413, 4), (key2490, -4), (key2490, -4), (key2486, -4), (key2422, -4), (key2422, -4), (key2413, -4), (key2490, 12)]

theorem rawRowCheck14071 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form7 = rawRow14071 := by decide +kernel

def row14071 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14071 : row14071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14071 := by decide +kernel

theorem rowEval14071 (x : Key → ℝ) : Integer.Sparse.eval row14071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14071, Integer.Sparse.eval_collectBalanced, rawRowCheck14071]

def rawRow14072 : Integer.Sparse Key := [(key2413, 4), (key2486, 4), (key2490, 4), (key2413, -4), (key2422, -4), (key2490, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2422, 12)]

theorem rawRowCheck14072 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form7 = rawRow14072 := by decide +kernel

def row14072 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

theorem rowCheck14072 : row14072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14072 := by decide +kernel

theorem rowEval14072 (x : Key → ℝ) : Integer.Sparse.eval row14072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14072, Integer.Sparse.eval_collectBalanced, rawRowCheck14072]

def rawRow14073 : Integer.Sparse Key := [(key2413, 4), (key2490, 4), (key2486, 4), (key2422, -4), (key2413, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2490, -4), (key2422, 12)]

theorem rawRowCheck14073 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form7 = rawRow14073 := by decide +kernel

def row14073 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

theorem rowCheck14073 : row14073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14073 := by decide +kernel

theorem rowEval14073 (x : Key → ℝ) : Integer.Sparse.eval row14073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14073, Integer.Sparse.eval_collectBalanced, rawRowCheck14073]

def rawRow14074 : Integer.Sparse Key := [(key2486, 4), (key2413, 4), (key2490, 4), (key2413, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2490, -4), (key2422, -4), (key2422, 12)]

theorem rawRowCheck14074 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form7 = rawRow14074 := by decide +kernel

def row14074 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

theorem rowCheck14074 : row14074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14074 := by decide +kernel

theorem rowEval14074 (x : Key → ℝ) : Integer.Sparse.eval row14074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14074, Integer.Sparse.eval_collectBalanced, rawRowCheck14074]

def rawRow14075 : Integer.Sparse Key := [(key2486, 4), (key2490, 4), (key2413, 4), (key2490, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2413, -4), (key2422, -4), (key2422, 12)]

theorem rawRowCheck14075 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form7 = rawRow14075 := by decide +kernel

def row14075 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

theorem rowCheck14075 : row14075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14075 := by decide +kernel

theorem rowEval14075 (x : Key → ℝ) : Integer.Sparse.eval row14075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14075, Integer.Sparse.eval_collectBalanced, rawRowCheck14075]

def rawRow14076 : Integer.Sparse Key := [(key2490, 4), (key2413, 4), (key2486, 4), (key2422, -4), (key2490, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2413, -4), (key2422, 12)]

theorem rawRowCheck14076 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form7 = rawRow14076 := by decide +kernel

def row14076 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

theorem rowCheck14076 : row14076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14076 := by decide +kernel

theorem rowEval14076 (x : Key → ℝ) : Integer.Sparse.eval row14076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14076, Integer.Sparse.eval_collectBalanced, rawRowCheck14076]

def rawRow14077 : Integer.Sparse Key := [(key2490, 4), (key2486, 4), (key2413, 4), (key2490, -4), (key2422, -4), (key2413, -4), (key2490, -4), (key2422, -4), (key2413, -4), (key2422, 12)]

theorem rawRowCheck14077 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form7 = rawRow14077 := by decide +kernel

def row14077 : Integer.Sparse Key := [(key2413, -4), (key2422, 4), (key2486, 4), (key2490, -4)]

theorem rowCheck14077 : row14077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14077 := by decide +kernel

theorem rowEval14077 (x : Key → ℝ) : Integer.Sparse.eval row14077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck14077, Integer.Sparse.eval_collectBalanced, rawRowCheck14077]

def rawRow14078 : Integer.Sparse Key := [(key2422, 4), (key2490, 4), (key2490, 4), (key2413, -4), (key2413, -4), (key2486, -4), (key2422, -4), (key2422, -4), (key2490, -4), (key2413, 12)]

theorem rawRowCheck14078 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form7 = rawRow14078 := by decide +kernel

def row14078 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14078 : row14078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14078 := by decide +kernel

theorem rowEval14078 (x : Key → ℝ) : Integer.Sparse.eval row14078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14078, Integer.Sparse.eval_collectBalanced, rawRowCheck14078]

def rawRow14079 : Integer.Sparse Key := [(key2490, 4), (key2422, 4), (key2490, 4), (key2413, -4), (key2486, -4), (key2413, -4), (key2422, -4), (key2490, -4), (key2422, -4), (key2413, 12)]

theorem rawRowCheck14079 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form7 = rawRow14079 := by decide +kernel

def row14079 : Integer.Sparse Key := [(key2413, 4), (key2422, -4), (key2486, -4), (key2490, 4)]

theorem rowCheck14079 : row14079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14079 := by decide +kernel

theorem rowEval14079 (x : Key → ℝ) : Integer.Sparse.eval row14079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14079, Integer.Sparse.eval_collectBalanced, rawRowCheck14079]

end MUB6.Certificate.GramRows

end OAI

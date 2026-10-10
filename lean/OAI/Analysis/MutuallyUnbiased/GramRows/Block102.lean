import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9984 : Integer.Sparse Key := [(key88, -6), (key88, -6), (key156, -6), (key94, -6), (key88, 2), (key88, 2), (key156, 2), (key5, 2), (key9, 2), (key153, 2), (key153, 2), (key203, 2), (key203, 2), (key14, 2), (key161, 2), (key161, 2)]

theorem rawRowCheck9984 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2 = rawRow9984 := by decide +kernel

def row9984 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -8), (key94, -6), (key153, 4), (key156, -4), (key161, 4), (key203, 4)]

theorem rowCheck9984 : row9984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9984 := by decide +kernel

theorem rowEval9984 (x : Key → ℝ) : Integer.Sparse.eval row9984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9984, Integer.Sparse.eval_collectBalanced, rawRowCheck9984]

def rawRow9985 : Integer.Sparse Key := [(key88, -6), (key156, -6), (key88, -6), (key94, -6), (key88, 2), (key156, 2), (key88, 2), (key165, 2), (key187, 2), (key5, 2), (key187, 2), (key9, 2), (key153, 2), (key161, 2), (key14, 2), (key161, 2)]

theorem rawRowCheck9985 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2 = rawRow9985 := by decide +kernel

def row9985 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -8), (key94, -6), (key153, 2), (key156, -4), (key161, 4), (key165, 2), (key187, 4)]

theorem rowCheck9985 : row9985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9985 := by decide +kernel

theorem rowEval9985 (x : Key → ℝ) : Integer.Sparse.eval row9985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9985, Integer.Sparse.eval_collectBalanced, rawRowCheck9985]

def rawRow9986 : Integer.Sparse Key := [(key156, -6), (key88, -6), (key88, -6), (key94, -6), (key156, 2), (key88, 2), (key88, 2), (key187, 2), (key165, 2), (key187, 2), (key5, 2), (key153, 2), (key9, 2), (key161, 2), (key161, 2), (key14, 2)]

theorem rawRowCheck9986 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2 = rawRow9986 := by decide +kernel

def row9986 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -8), (key94, -6), (key153, 2), (key156, -4), (key161, 4), (key165, 2), (key187, 4)]

theorem rowCheck9986 : row9986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9986 := by decide +kernel

theorem rowEval9986 (x : Key → ℝ) : Integer.Sparse.eval row9986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9986, Integer.Sparse.eval_collectBalanced, rawRowCheck9986]

def rawRow9987 : Integer.Sparse Key := [(key88, -6), (key94, -6), (key156, -6), (key88, -6), (key165, 2), (key167, 2), (key187, 2), (key5, 2), (key11, 2), (key88, 2), (key167, 2), (key156, 2), (key187, 2), (key9, 2), (key92, 2), (key153, 2)]

theorem rawRowCheck9987 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2 = rawRow9987 := by decide +kernel

def row9987 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

theorem rowCheck9987 : row9987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9987 := by decide +kernel

theorem rowEval9987 (x : Key → ℝ) : Integer.Sparse.eval row9987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9987, Integer.Sparse.eval_collectBalanced, rawRowCheck9987]

def rawRow9988 : Integer.Sparse Key := [(key94, -6), (key88, -6), (key156, -6), (key88, -6), (key167, 2), (key165, 2), (key187, 2), (key11, 2), (key5, 2), (key167, 2), (key88, 2), (key187, 2), (key156, 2), (key9, 2), (key153, 2), (key92, 2)]

theorem rawRowCheck9988 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2 = rawRow9988 := by decide +kernel

def row9988 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

theorem rowCheck9988 : row9988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9988 := by decide +kernel

theorem rowEval9988 (x : Key → ℝ) : Integer.Sparse.eval row9988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9988, Integer.Sparse.eval_collectBalanced, rawRowCheck9988]

def rawRow9989 : Integer.Sparse Key := [(key88, -6), (key156, -6), (key94, -6), (key88, -6), (key165, 2), (key187, 2), (key167, 2), (key88, 2), (key156, 2), (key5, 2), (key187, 2), (key11, 2), (key167, 2), (key92, 2), (key9, 2), (key153, 2)]

theorem rawRowCheck9989 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2 = rawRow9989 := by decide +kernel

def row9989 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

theorem rowCheck9989 : row9989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9989 := by decide +kernel

theorem rowEval9989 (x : Key → ℝ) : Integer.Sparse.eval row9989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9989, Integer.Sparse.eval_collectBalanced, rawRowCheck9989]

def rawRow9990 : Integer.Sparse Key := [(key156, -6), (key88, -6), (key94, -6), (key88, -6), (key187, 2), (key165, 2), (key167, 2), (key156, 2), (key88, 2), (key187, 2), (key5, 2), (key167, 2), (key11, 2), (key92, 2), (key153, 2), (key9, 2)]

theorem rawRowCheck9990 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2 = rawRow9990 := by decide +kernel

def row9990 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

theorem rowCheck9990 : row9990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9990 := by decide +kernel

theorem rowEval9990 (x : Key → ℝ) : Integer.Sparse.eval row9990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9990, Integer.Sparse.eval_collectBalanced, rawRowCheck9990]

def rawRow9991 : Integer.Sparse Key := [(key94, -6), (key156, -6), (key88, -6), (key88, -6), (key167, 2), (key187, 2), (key165, 2), (key167, 2), (key187, 2), (key11, 2), (key156, 2), (key5, 2), (key88, 2), (key153, 2), (key9, 2), (key92, 2)]

theorem rawRowCheck9991 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2 = rawRow9991 := by decide +kernel

def row9991 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

theorem rowCheck9991 : row9991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9991 := by decide +kernel

theorem rowEval9991 (x : Key → ℝ) : Integer.Sparse.eval row9991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9991, Integer.Sparse.eval_collectBalanced, rawRowCheck9991]

def rawRow9992 : Integer.Sparse Key := [(key156, -6), (key94, -6), (key88, -6), (key88, -6), (key187, 2), (key167, 2), (key165, 2), (key187, 2), (key167, 2), (key156, 2), (key11, 2), (key88, 2), (key5, 2), (key153, 2), (key92, 2), (key9, 2)]

theorem rawRowCheck9992 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2 = rawRow9992 := by decide +kernel

def row9992 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

theorem rowCheck9992 : row9992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9992 := by decide +kernel

theorem rowEval9992 (x : Key → ℝ) : Integer.Sparse.eval row9992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9992, Integer.Sparse.eval_collectBalanced, rawRowCheck9992]

def rawRow9993 : Integer.Sparse Key := [(key165, -6), (key167, -6), (key167, -6), (key187, -6), (key5, 2), (key11, 2), (key11, 2), (key88, 2), (key94, 2), (key88, 2), (key167, 2), (key94, 2), (key167, 2), (key156, 2), (key156, 2), (key187, 2)]

theorem rawRowCheck9993 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form2 = rawRow9993 := by decide +kernel

def row9993 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck9993 : row9993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9993 := by decide +kernel

theorem rowEval9993 (x : Key → ℝ) : Integer.Sparse.eval row9993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9993, Integer.Sparse.eval_collectBalanced, rawRowCheck9993]

def rawRow9994 : Integer.Sparse Key := [(key167, -6), (key165, -6), (key167, -6), (key187, -6), (key11, 2), (key5, 2), (key11, 2), (key94, 2), (key88, 2), (key167, 2), (key88, 2), (key167, 2), (key94, 2), (key156, 2), (key187, 2), (key156, 2)]

theorem rawRowCheck9994 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form2 = rawRow9994 := by decide +kernel

def row9994 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck9994 : row9994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9994 := by decide +kernel

theorem rowEval9994 (x : Key → ℝ) : Integer.Sparse.eval row9994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9994, Integer.Sparse.eval_collectBalanced, rawRowCheck9994]

def rawRow9995 : Integer.Sparse Key := [(key167, -6), (key167, -6), (key165, -6), (key187, -6), (key11, 2), (key11, 2), (key5, 2), (key167, 2), (key167, 2), (key94, 2), (key94, 2), (key88, 2), (key88, 2), (key187, 2), (key156, 2), (key156, 2)]

theorem rawRowCheck9995 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form2 = rawRow9995 := by decide +kernel

def row9995 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck9995 : row9995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9995 := by decide +kernel

theorem rowEval9995 (x : Key → ℝ) : Integer.Sparse.eval row9995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9995, Integer.Sparse.eval_collectBalanced, rawRowCheck9995]

def rawRow9996 : Integer.Sparse Key := [(key165, -6), (key167, -6), (key187, -6), (key167, -6), (key88, 2), (key94, 2), (key156, 2), (key5, 2), (key11, 2), (key88, 2), (key167, 2), (key156, 2), (key187, 2), (key11, 2), (key94, 2), (key167, 2)]

theorem rawRowCheck9996 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form2 = rawRow9996 := by decide +kernel

def row9996 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck9996 : row9996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9996 := by decide +kernel

theorem rowEval9996 (x : Key → ℝ) : Integer.Sparse.eval row9996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9996, Integer.Sparse.eval_collectBalanced, rawRowCheck9996]

def rawRow9997 : Integer.Sparse Key := [(key167, -6), (key165, -6), (key187, -6), (key167, -6), (key94, 2), (key88, 2), (key156, 2), (key11, 2), (key5, 2), (key167, 2), (key88, 2), (key187, 2), (key156, 2), (key11, 2), (key167, 2), (key94, 2)]

theorem rawRowCheck9997 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form2 = rawRow9997 := by decide +kernel

def row9997 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck9997 : row9997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9997 := by decide +kernel

theorem rowEval9997 (x : Key → ℝ) : Integer.Sparse.eval row9997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9997, Integer.Sparse.eval_collectBalanced, rawRowCheck9997]

def rawRow9998 : Integer.Sparse Key := [(key165, -6), (key187, -6), (key167, -6), (key167, -6), (key88, 2), (key156, 2), (key94, 2), (key88, 2), (key156, 2), (key5, 2), (key187, 2), (key11, 2), (key167, 2), (key94, 2), (key11, 2), (key167, 2)]

theorem rawRowCheck9998 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form2 = rawRow9998 := by decide +kernel

def row9998 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck9998 : row9998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9998 := by decide +kernel

theorem rowEval9998 (x : Key → ℝ) : Integer.Sparse.eval row9998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9998, Integer.Sparse.eval_collectBalanced, rawRowCheck9998]

def rawRow9999 : Integer.Sparse Key := [(key187, -6), (key165, -6), (key167, -6), (key167, -6), (key156, 2), (key88, 2), (key94, 2), (key156, 2), (key88, 2), (key187, 2), (key5, 2), (key167, 2), (key11, 2), (key94, 2), (key167, 2), (key11, 2)]

theorem rawRowCheck9999 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form2 = rawRow9999 := by decide +kernel

def row9999 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck9999 : row9999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9999 := by decide +kernel

theorem rowEval9999 (x : Key → ℝ) : Integer.Sparse.eval row9999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck9999, Integer.Sparse.eval_collectBalanced, rawRowCheck9999]

def rawRow10000 : Integer.Sparse Key := [(key167, -6), (key187, -6), (key165, -6), (key167, -6), (key94, 2), (key156, 2), (key88, 2), (key167, 2), (key187, 2), (key11, 2), (key156, 2), (key5, 2), (key88, 2), (key167, 2), (key11, 2), (key94, 2)]

theorem rawRowCheck10000 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form2 = rawRow10000 := by decide +kernel

def row10000 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck10000 : row10000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10000 := by decide +kernel

theorem rowEval10000 (x : Key → ℝ) : Integer.Sparse.eval row10000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10000, Integer.Sparse.eval_collectBalanced, rawRowCheck10000]

def rawRow10001 : Integer.Sparse Key := [(key187, -6), (key167, -6), (key165, -6), (key167, -6), (key156, 2), (key94, 2), (key88, 2), (key187, 2), (key167, 2), (key156, 2), (key11, 2), (key88, 2), (key5, 2), (key167, 2), (key94, 2), (key11, 2)]

theorem rawRowCheck10001 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form2 = rawRow10001 := by decide +kernel

def row10001 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck10001 : row10001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10001 := by decide +kernel

theorem rowEval10001 (x : Key → ℝ) : Integer.Sparse.eval row10001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck10001, Integer.Sparse.eval_collectBalanced, rawRowCheck10001]

def rawRow10002 : Integer.Sparse Key := [(key167, -6), (key167, -6), (key187, -6), (key165, -6), (key167, 2), (key167, 2), (key187, 2), (key11, 2), (key11, 2), (key94, 2), (key94, 2), (key156, 2), (key156, 2), (key5, 2), (key88, 2), (key88, 2)]

theorem rawRowCheck10002 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form2 = rawRow10002 := by decide +kernel

def row10002 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck10002 : row10002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10002 := by decide +kernel

theorem rowEval10002 (x : Key → ℝ) : Integer.Sparse.eval row10002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10002, Integer.Sparse.eval_collectBalanced, rawRowCheck10002]

def rawRow10003 : Integer.Sparse Key := [(key167, -6), (key187, -6), (key167, -6), (key165, -6), (key167, 2), (key187, 2), (key167, 2), (key94, 2), (key156, 2), (key11, 2), (key156, 2), (key11, 2), (key94, 2), (key88, 2), (key5, 2), (key88, 2)]

theorem rawRowCheck10003 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form2 = rawRow10003 := by decide +kernel

def row10003 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck10003 : row10003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10003 := by decide +kernel

theorem rowEval10003 (x : Key → ℝ) : Integer.Sparse.eval row10003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10003, Integer.Sparse.eval_collectBalanced, rawRowCheck10003]

def rawRow10004 : Integer.Sparse Key := [(key187, -6), (key167, -6), (key167, -6), (key165, -6), (key187, 2), (key167, 2), (key167, 2), (key156, 2), (key94, 2), (key156, 2), (key11, 2), (key94, 2), (key11, 2), (key88, 2), (key88, 2), (key5, 2)]

theorem rawRowCheck10004 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form2 = rawRow10004 := by decide +kernel

def row10004 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

theorem rowCheck10004 : row10004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10004 := by decide +kernel

theorem rowEval10004 (x : Key → ℝ) : Integer.Sparse.eval row10004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck10004, Integer.Sparse.eval_collectBalanced, rawRowCheck10004]

def rawRow10005 : Integer.Sparse Key := [(key1002, -6), (key1115, -6), (key1151, -6), (key1151, -6), (key1002, 2), (key1016, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1072, 2), (key1124, 2), (key1124, 2), (key1151, 2), (key1151, 2), (key1167, 2), (key1167, 2)]

theorem rawRowCheck10005 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form3 = rawRow10005 := by decide +kernel

def row10005 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10005 : row10005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10005 := by decide +kernel

theorem rowEval10005 (x : Key → ℝ) : Integer.Sparse.eval row10005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10005, Integer.Sparse.eval_collectBalanced, rawRowCheck10005]

def rawRow10006 : Integer.Sparse Key := [(key1002, -6), (key1151, -6), (key1115, -6), (key1151, -6), (key1016, 2), (key1002, 2), (key1016, 2), (key1072, 2), (key1037, 2), (key1072, 2), (key1151, 2), (key1167, 2), (key1124, 2), (key1167, 2), (key1124, 2), (key1151, 2)]

theorem rawRowCheck10006 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form3 = rawRow10006 := by decide +kernel

def row10006 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10006 : row10006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10006 := by decide +kernel

theorem rowEval10006 (x : Key → ℝ) : Integer.Sparse.eval row10006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10006, Integer.Sparse.eval_collectBalanced, rawRowCheck10006]

def rawRow10007 : Integer.Sparse Key := [(key1002, -6), (key1151, -6), (key1151, -6), (key1115, -6), (key1016, 2), (key1016, 2), (key1002, 2), (key1072, 2), (key1072, 2), (key1037, 2), (key1167, 2), (key1151, 2), (key1167, 2), (key1124, 2), (key1151, 2), (key1124, 2)]

theorem rawRowCheck10007 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form3 = rawRow10007 := by decide +kernel

def row10007 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10007 : row10007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10007 := by decide +kernel

theorem rowEval10007 (x : Key → ℝ) : Integer.Sparse.eval row10007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10007, Integer.Sparse.eval_collectBalanced, rawRowCheck10007]

def rawRow10008 : Integer.Sparse Key := [(key1115, -6), (key1002, -6), (key1151, -6), (key1151, -6), (key1037, 2), (key1124, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1151, 2), (key1016, 2), (key1016, 2), (key1072, 2), (key1072, 2), (key1167, 2), (key1167, 2)]

theorem rawRowCheck10008 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form3 = rawRow10008 := by decide +kernel

def row10008 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10008 : row10008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10008 := by decide +kernel

theorem rowEval10008 (x : Key → ℝ) : Integer.Sparse.eval row10008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10008, Integer.Sparse.eval_collectBalanced, rawRowCheck10008]

def rawRow10009 : Integer.Sparse Key := [(key1115, -6), (key1151, -6), (key1002, -6), (key1151, -6), (key1124, 2), (key1037, 2), (key1124, 2), (key1151, 2), (key1002, 2), (key1151, 2), (key1072, 2), (key1167, 2), (key1016, 2), (key1167, 2), (key1016, 2), (key1072, 2)]

theorem rawRowCheck10009 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form3 = rawRow10009 := by decide +kernel

def row10009 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10009 : row10009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10009 := by decide +kernel

theorem rowEval10009 (x : Key → ℝ) : Integer.Sparse.eval row10009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10009, Integer.Sparse.eval_collectBalanced, rawRowCheck10009]

def rawRow10010 : Integer.Sparse Key := [(key1115, -6), (key1151, -6), (key1151, -6), (key1002, -6), (key1124, 2), (key1124, 2), (key1037, 2), (key1151, 2), (key1151, 2), (key1002, 2), (key1167, 2), (key1072, 2), (key1167, 2), (key1016, 2), (key1072, 2), (key1016, 2)]

theorem rawRowCheck10010 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form3 = rawRow10010 := by decide +kernel

def row10010 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10010 : row10010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10010 := by decide +kernel

theorem rowEval10010 (x : Key → ℝ) : Integer.Sparse.eval row10010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck10010, Integer.Sparse.eval_collectBalanced, rawRowCheck10010]

def rawRow10011 : Integer.Sparse Key := [(key1151, -6), (key1002, -6), (key1115, -6), (key1151, -6), (key1072, 2), (key1151, 2), (key1167, 2), (key1016, 2), (key1124, 2), (key1167, 2), (key1002, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1124, 2), (key1151, 2)]

theorem rawRowCheck10011 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form3 = rawRow10011 := by decide +kernel

def row10011 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10011 : row10011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10011 := by decide +kernel

theorem rowEval10011 (x : Key → ℝ) : Integer.Sparse.eval row10011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10011, Integer.Sparse.eval_collectBalanced, rawRowCheck10011]

def rawRow10012 : Integer.Sparse Key := [(key1151, -6), (key1002, -6), (key1151, -6), (key1115, -6), (key1072, 2), (key1167, 2), (key1151, 2), (key1016, 2), (key1167, 2), (key1124, 2), (key1016, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1151, 2), (key1124, 2)]

theorem rawRowCheck10012 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form3 = rawRow10012 := by decide +kernel

def row10012 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10012 : row10012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10012 := by decide +kernel

theorem rowEval10012 (x : Key → ℝ) : Integer.Sparse.eval row10012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10012, Integer.Sparse.eval_collectBalanced, rawRowCheck10012]

def rawRow10013 : Integer.Sparse Key := [(key1151, -6), (key1115, -6), (key1002, -6), (key1151, -6), (key1151, 2), (key1072, 2), (key1167, 2), (key1124, 2), (key1016, 2), (key1167, 2), (key1037, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1016, 2), (key1072, 2)]

theorem rawRowCheck10013 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form3 = rawRow10013 := by decide +kernel

def row10013 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10013 : row10013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10013 := by decide +kernel

theorem rowEval10013 (x : Key → ℝ) : Integer.Sparse.eval row10013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10013, Integer.Sparse.eval_collectBalanced, rawRowCheck10013]

def rawRow10014 : Integer.Sparse Key := [(key1151, -6), (key1115, -6), (key1151, -6), (key1002, -6), (key1151, 2), (key1167, 2), (key1072, 2), (key1124, 2), (key1167, 2), (key1016, 2), (key1124, 2), (key1037, 2), (key1151, 2), (key1002, 2), (key1072, 2), (key1016, 2)]

theorem rawRowCheck10014 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form3 = rawRow10014 := by decide +kernel

def row10014 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10014 : row10014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10014 := by decide +kernel

theorem rowEval10014 (x : Key → ℝ) : Integer.Sparse.eval row10014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck10014, Integer.Sparse.eval_collectBalanced, rawRowCheck10014]

def rawRow10015 : Integer.Sparse Key := [(key1151, -6), (key1151, -6), (key1002, -6), (key1115, -6), (key1167, 2), (key1072, 2), (key1151, 2), (key1167, 2), (key1016, 2), (key1124, 2), (key1072, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1002, 2), (key1037, 2)]

theorem rawRowCheck10015 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form3 = rawRow10015 := by decide +kernel

def row10015 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10015 : row10015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10015 := by decide +kernel

theorem rowEval10015 (x : Key → ℝ) : Integer.Sparse.eval row10015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10015, Integer.Sparse.eval_collectBalanced, rawRowCheck10015]

def rawRow10016 : Integer.Sparse Key := [(key1151, -6), (key1151, -6), (key1115, -6), (key1002, -6), (key1167, 2), (key1151, 2), (key1072, 2), (key1167, 2), (key1124, 2), (key1016, 2), (key1151, 2), (key1072, 2), (key1124, 2), (key1016, 2), (key1037, 2), (key1002, 2)]

theorem rawRowCheck10016 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form3 = rawRow10016 := by decide +kernel

def row10016 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

theorem rowCheck10016 : row10016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10016 := by decide +kernel

theorem rowEval10016 (x : Key → ℝ) : Integer.Sparse.eval row10016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck10016, Integer.Sparse.eval_collectBalanced, rawRowCheck10016]

def rawRow10017 : Integer.Sparse Key := [(key1016, -6), (key1124, -6), (key1124, -6), (key1167, -6), (key1002, 2), (key1002, 2), (key1016, 2), (key1037, 2), (key1037, 2), (key1072, 2), (key1115, 2), (key1124, 2), (key1115, 2), (key1151, 2), (key1124, 2), (key1151, 2)]

theorem rawRowCheck10017 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form3 = rawRow10017 := by decide +kernel

def row10017 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10017 : row10017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10017 := by decide +kernel

theorem rowEval10017 (x : Key → ℝ) : Integer.Sparse.eval row10017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10017, Integer.Sparse.eval_collectBalanced, rawRowCheck10017]

def rawRow10018 : Integer.Sparse Key := [(key1016, -6), (key1124, -6), (key1167, -6), (key1124, -6), (key1002, 2), (key1016, 2), (key1002, 2), (key1037, 2), (key1072, 2), (key1037, 2), (key1124, 2), (key1115, 2), (key1151, 2), (key1115, 2), (key1151, 2), (key1124, 2)]

theorem rawRowCheck10018 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form3 = rawRow10018 := by decide +kernel

def row10018 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10018 : row10018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10018 := by decide +kernel

theorem rowEval10018 (x : Key → ℝ) : Integer.Sparse.eval row10018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10018, Integer.Sparse.eval_collectBalanced, rawRowCheck10018]

def rawRow10019 : Integer.Sparse Key := [(key1016, -6), (key1167, -6), (key1124, -6), (key1124, -6), (key1016, 2), (key1002, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1037, 2), (key1151, 2), (key1151, 2), (key1124, 2), (key1124, 2), (key1115, 2), (key1115, 2)]

theorem rawRowCheck10019 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form3 = rawRow10019 := by decide +kernel

def row10019 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10019 : row10019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10019 := by decide +kernel

theorem rowEval10019 (x : Key → ℝ) : Integer.Sparse.eval row10019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10019, Integer.Sparse.eval_collectBalanced, rawRowCheck10019]

def rawRow10020 : Integer.Sparse Key := [(key1124, -6), (key1016, -6), (key1124, -6), (key1167, -6), (key1037, 2), (key1115, 2), (key1124, 2), (key1002, 2), (key1115, 2), (key1151, 2), (key1002, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1124, 2), (key1151, 2)]

theorem rawRowCheck10020 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form3 = rawRow10020 := by decide +kernel

def row10020 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10020 : row10020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10020 := by decide +kernel

theorem rowEval10020 (x : Key → ℝ) : Integer.Sparse.eval row10020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10020, Integer.Sparse.eval_collectBalanced, rawRowCheck10020]

def rawRow10021 : Integer.Sparse Key := [(key1124, -6), (key1016, -6), (key1167, -6), (key1124, -6), (key1037, 2), (key1124, 2), (key1115, 2), (key1002, 2), (key1151, 2), (key1115, 2), (key1016, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1151, 2), (key1124, 2)]

theorem rawRowCheck10021 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form3 = rawRow10021 := by decide +kernel

def row10021 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10021 : row10021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10021 := by decide +kernel

theorem rowEval10021 (x : Key → ℝ) : Integer.Sparse.eval row10021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10021, Integer.Sparse.eval_collectBalanced, rawRowCheck10021]

def rawRow10022 : Integer.Sparse Key := [(key1124, -6), (key1124, -6), (key1016, -6), (key1167, -6), (key1115, 2), (key1037, 2), (key1124, 2), (key1115, 2), (key1002, 2), (key1151, 2), (key1037, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1016, 2), (key1072, 2)]

theorem rawRowCheck10022 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form3 = rawRow10022 := by decide +kernel

def row10022 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10022 : row10022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10022 := by decide +kernel

theorem rowEval10022 (x : Key → ℝ) : Integer.Sparse.eval row10022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10022, Integer.Sparse.eval_collectBalanced, rawRowCheck10022]

def rawRow10023 : Integer.Sparse Key := [(key1124, -6), (key1124, -6), (key1167, -6), (key1016, -6), (key1115, 2), (key1124, 2), (key1037, 2), (key1115, 2), (key1151, 2), (key1002, 2), (key1124, 2), (key1037, 2), (key1151, 2), (key1002, 2), (key1072, 2), (key1016, 2)]

theorem rawRowCheck10023 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form3 = rawRow10023 := by decide +kernel

def row10023 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10023 : row10023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10023 := by decide +kernel

theorem rowEval10023 (x : Key → ℝ) : Integer.Sparse.eval row10023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck10023, Integer.Sparse.eval_collectBalanced, rawRowCheck10023]

def rawRow10024 : Integer.Sparse Key := [(key1124, -6), (key1167, -6), (key1016, -6), (key1124, -6), (key1124, 2), (key1037, 2), (key1115, 2), (key1151, 2), (key1002, 2), (key1115, 2), (key1072, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1002, 2), (key1037, 2)]

theorem rawRowCheck10024 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form3 = rawRow10024 := by decide +kernel

def row10024 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10024 : row10024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10024 := by decide +kernel

theorem rowEval10024 (x : Key → ℝ) : Integer.Sparse.eval row10024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10024, Integer.Sparse.eval_collectBalanced, rawRowCheck10024]

def rawRow10025 : Integer.Sparse Key := [(key1124, -6), (key1167, -6), (key1124, -6), (key1016, -6), (key1124, 2), (key1115, 2), (key1037, 2), (key1151, 2), (key1115, 2), (key1002, 2), (key1151, 2), (key1072, 2), (key1124, 2), (key1016, 2), (key1037, 2), (key1002, 2)]

theorem rawRowCheck10025 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form3 = rawRow10025 := by decide +kernel

def row10025 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10025 : row10025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10025 := by decide +kernel

theorem rowEval10025 (x : Key → ℝ) : Integer.Sparse.eval row10025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck10025, Integer.Sparse.eval_collectBalanced, rawRowCheck10025]

def rawRow10026 : Integer.Sparse Key := [(key1167, -6), (key1016, -6), (key1124, -6), (key1124, -6), (key1072, 2), (key1151, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1124, 2), (key1002, 2), (key1002, 2), (key1037, 2), (key1037, 2), (key1115, 2), (key1115, 2)]

theorem rawRowCheck10026 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form3 = rawRow10026 := by decide +kernel

def row10026 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10026 : row10026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10026 := by decide +kernel

theorem rowEval10026 (x : Key → ℝ) : Integer.Sparse.eval row10026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10026, Integer.Sparse.eval_collectBalanced, rawRowCheck10026]

def rawRow10027 : Integer.Sparse Key := [(key1167, -6), (key1124, -6), (key1016, -6), (key1124, -6), (key1151, 2), (key1072, 2), (key1151, 2), (key1124, 2), (key1016, 2), (key1124, 2), (key1037, 2), (key1115, 2), (key1002, 2), (key1115, 2), (key1002, 2), (key1037, 2)]

theorem rawRowCheck10027 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form3 = rawRow10027 := by decide +kernel

def row10027 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10027 : row10027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10027 := by decide +kernel

theorem rowEval10027 (x : Key → ℝ) : Integer.Sparse.eval row10027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10027, Integer.Sparse.eval_collectBalanced, rawRowCheck10027]

def rawRow10028 : Integer.Sparse Key := [(key1167, -6), (key1124, -6), (key1124, -6), (key1016, -6), (key1151, 2), (key1151, 2), (key1072, 2), (key1124, 2), (key1124, 2), (key1016, 2), (key1115, 2), (key1037, 2), (key1115, 2), (key1002, 2), (key1037, 2), (key1002, 2)]

theorem rawRowCheck10028 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form3 = rawRow10028 := by decide +kernel

def row10028 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

theorem rowCheck10028 : row10028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10028 := by decide +kernel

theorem rowEval10028 (x : Key → ℝ) : Integer.Sparse.eval row10028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck10028, Integer.Sparse.eval_collectBalanced, rawRowCheck10028]

def rawRow10029 : Integer.Sparse Key := [(key1095, -6), (key1095, -6), (key1101, -6), (key1229, -6), (key981, 2), (key981, 2), (key987, 2), (key1095, 2), (key1095, 2), (key1166, 2), (key1166, 2), (key1173, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key1246, 2)]

theorem rawRowCheck10029 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4 = rawRow10029 := by decide +kernel

def row10029 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10029 : row10029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10029 := by decide +kernel

theorem rowEval10029 (x : Key → ℝ) : Integer.Sparse.eval row10029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10029, Integer.Sparse.eval_collectBalanced, rawRowCheck10029]

def rawRow10030 : Integer.Sparse Key := [(key1095, -6), (key1101, -6), (key1095, -6), (key1229, -6), (key981, 2), (key987, 2), (key981, 2), (key1166, 2), (key1173, 2), (key1095, 2), (key1173, 2), (key1095, 2), (key1166, 2), (key1246, 2), (key1229, 2), (key1246, 2)]

theorem rawRowCheck10030 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4 = rawRow10030 := by decide +kernel

def row10030 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10030 : row10030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10030 := by decide +kernel

theorem rowEval10030 (x : Key → ℝ) : Integer.Sparse.eval row10030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10030, Integer.Sparse.eval_collectBalanced, rawRowCheck10030]

def rawRow10031 : Integer.Sparse Key := [(key1101, -6), (key1095, -6), (key1095, -6), (key1229, -6), (key987, 2), (key981, 2), (key981, 2), (key1173, 2), (key1166, 2), (key1173, 2), (key1095, 2), (key1166, 2), (key1095, 2), (key1246, 2), (key1246, 2), (key1229, 2)]

theorem rawRowCheck10031 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4 = rawRow10031 := by decide +kernel

def row10031 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10031 : row10031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10031 := by decide +kernel

theorem rowEval10031 (x : Key → ℝ) : Integer.Sparse.eval row10031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10031, Integer.Sparse.eval_collectBalanced, rawRowCheck10031]

def rawRow10032 : Integer.Sparse Key := [(key1095, -6), (key1095, -6), (key1229, -6), (key1101, -6), (key1095, 2), (key1095, 2), (key1229, 2), (key981, 2), (key981, 2), (key1166, 2), (key1166, 2), (key1246, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1173, 2)]

theorem rawRowCheck10032 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4 = rawRow10032 := by decide +kernel

def row10032 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10032 : row10032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10032 := by decide +kernel

theorem rowEval10032 (x : Key → ℝ) : Integer.Sparse.eval row10032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10032, Integer.Sparse.eval_collectBalanced, rawRowCheck10032]

def rawRow10033 : Integer.Sparse Key := [(key1095, -6), (key1229, -6), (key1095, -6), (key1101, -6), (key1095, 2), (key1229, 2), (key1095, 2), (key1166, 2), (key1246, 2), (key981, 2), (key1246, 2), (key981, 2), (key1166, 2), (key1173, 2), (key987, 2), (key1173, 2)]

theorem rawRowCheck10033 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4 = rawRow10033 := by decide +kernel

def row10033 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10033 : row10033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10033 := by decide +kernel

theorem rowEval10033 (x : Key → ℝ) : Integer.Sparse.eval row10033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10033, Integer.Sparse.eval_collectBalanced, rawRowCheck10033]

def rawRow10034 : Integer.Sparse Key := [(key1229, -6), (key1095, -6), (key1095, -6), (key1101, -6), (key1229, 2), (key1095, 2), (key1095, 2), (key1246, 2), (key1166, 2), (key1246, 2), (key981, 2), (key1166, 2), (key981, 2), (key1173, 2), (key1173, 2), (key987, 2)]

theorem rawRowCheck10034 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4 = rawRow10034 := by decide +kernel

def row10034 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10034 : row10034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10034 := by decide +kernel

theorem rowEval10034 (x : Key → ℝ) : Integer.Sparse.eval row10034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10034, Integer.Sparse.eval_collectBalanced, rawRowCheck10034]

def rawRow10035 : Integer.Sparse Key := [(key1095, -6), (key1101, -6), (key1229, -6), (key1095, -6), (key1166, 2), (key1173, 2), (key1246, 2), (key981, 2), (key987, 2), (key1095, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key981, 2), (key1095, 2), (key1166, 2)]

theorem rawRowCheck10035 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4 = rawRow10035 := by decide +kernel

def row10035 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10035 : row10035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10035 := by decide +kernel

theorem rowEval10035 (x : Key → ℝ) : Integer.Sparse.eval row10035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10035, Integer.Sparse.eval_collectBalanced, rawRowCheck10035]

def rawRow10036 : Integer.Sparse Key := [(key1101, -6), (key1095, -6), (key1229, -6), (key1095, -6), (key1173, 2), (key1166, 2), (key1246, 2), (key987, 2), (key981, 2), (key1173, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key981, 2), (key1166, 2), (key1095, 2)]

theorem rawRowCheck10036 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4 = rawRow10036 := by decide +kernel

def row10036 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10036 : row10036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10036 := by decide +kernel

theorem rowEval10036 (x : Key → ℝ) : Integer.Sparse.eval row10036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10036, Integer.Sparse.eval_collectBalanced, rawRowCheck10036]

def rawRow10037 : Integer.Sparse Key := [(key1095, -6), (key1229, -6), (key1101, -6), (key1095, -6), (key1166, 2), (key1246, 2), (key1173, 2), (key1095, 2), (key1229, 2), (key981, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1095, 2), (key981, 2), (key1166, 2)]

theorem rawRowCheck10037 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4 = rawRow10037 := by decide +kernel

def row10037 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10037 : row10037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10037 := by decide +kernel

theorem rowEval10037 (x : Key → ℝ) : Integer.Sparse.eval row10037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10037, Integer.Sparse.eval_collectBalanced, rawRowCheck10037]

def rawRow10038 : Integer.Sparse Key := [(key1229, -6), (key1095, -6), (key1101, -6), (key1095, -6), (key1246, 2), (key1166, 2), (key1173, 2), (key1229, 2), (key1095, 2), (key1246, 2), (key981, 2), (key1173, 2), (key987, 2), (key1095, 2), (key1166, 2), (key981, 2)]

theorem rawRowCheck10038 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4 = rawRow10038 := by decide +kernel

def row10038 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10038 : row10038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10038 := by decide +kernel

theorem rowEval10038 (x : Key → ℝ) : Integer.Sparse.eval row10038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10038, Integer.Sparse.eval_collectBalanced, rawRowCheck10038]

def rawRow10039 : Integer.Sparse Key := [(key1101, -6), (key1229, -6), (key1095, -6), (key1095, -6), (key1173, 2), (key1246, 2), (key1166, 2), (key1173, 2), (key1246, 2), (key987, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1166, 2), (key981, 2), (key1095, 2)]

theorem rawRowCheck10039 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4 = rawRow10039 := by decide +kernel

def row10039 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10039 : row10039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10039 := by decide +kernel

theorem rowEval10039 (x : Key → ℝ) : Integer.Sparse.eval row10039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10039, Integer.Sparse.eval_collectBalanced, rawRowCheck10039]

def rawRow10040 : Integer.Sparse Key := [(key1229, -6), (key1101, -6), (key1095, -6), (key1095, -6), (key1246, 2), (key1173, 2), (key1166, 2), (key1246, 2), (key1173, 2), (key1229, 2), (key987, 2), (key1095, 2), (key981, 2), (key1166, 2), (key1095, 2), (key981, 2)]

theorem rawRowCheck10040 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4 = rawRow10040 := by decide +kernel

def row10040 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

theorem rowCheck10040 : row10040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10040 := by decide +kernel

theorem rowEval10040 (x : Key → ℝ) : Integer.Sparse.eval row10040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10040, Integer.Sparse.eval_collectBalanced, rawRowCheck10040]

def rawRow10041 : Integer.Sparse Key := [(key1166, -6), (key1173, -6), (key1173, -6), (key1246, -6), (key981, 2), (key987, 2), (key987, 2), (key1095, 2), (key1101, 2), (key1095, 2), (key1173, 2), (key1101, 2), (key1173, 2), (key1229, 2), (key1229, 2), (key1246, 2)]

theorem rawRowCheck10041 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form4 = rawRow10041 := by decide +kernel

def row10041 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10041 : row10041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10041 := by decide +kernel

theorem rowEval10041 (x : Key → ℝ) : Integer.Sparse.eval row10041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10041, Integer.Sparse.eval_collectBalanced, rawRowCheck10041]

def rawRow10042 : Integer.Sparse Key := [(key1173, -6), (key1166, -6), (key1173, -6), (key1246, -6), (key987, 2), (key981, 2), (key987, 2), (key1101, 2), (key1095, 2), (key1173, 2), (key1095, 2), (key1173, 2), (key1101, 2), (key1229, 2), (key1246, 2), (key1229, 2)]

theorem rawRowCheck10042 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form4 = rawRow10042 := by decide +kernel

def row10042 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10042 : row10042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10042 := by decide +kernel

theorem rowEval10042 (x : Key → ℝ) : Integer.Sparse.eval row10042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10042, Integer.Sparse.eval_collectBalanced, rawRowCheck10042]

def rawRow10043 : Integer.Sparse Key := [(key1173, -6), (key1173, -6), (key1166, -6), (key1246, -6), (key987, 2), (key987, 2), (key981, 2), (key1173, 2), (key1173, 2), (key1101, 2), (key1101, 2), (key1095, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key1229, 2)]

theorem rawRowCheck10043 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form4 = rawRow10043 := by decide +kernel

def row10043 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10043 : row10043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10043 := by decide +kernel

theorem rowEval10043 (x : Key → ℝ) : Integer.Sparse.eval row10043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10043, Integer.Sparse.eval_collectBalanced, rawRowCheck10043]

def rawRow10044 : Integer.Sparse Key := [(key1166, -6), (key1173, -6), (key1246, -6), (key1173, -6), (key1095, 2), (key1101, 2), (key1229, 2), (key981, 2), (key987, 2), (key1095, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key987, 2), (key1101, 2), (key1173, 2)]

theorem rawRowCheck10044 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form4 = rawRow10044 := by decide +kernel

def row10044 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10044 : row10044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10044 := by decide +kernel

theorem rowEval10044 (x : Key → ℝ) : Integer.Sparse.eval row10044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10044, Integer.Sparse.eval_collectBalanced, rawRowCheck10044]

def rawRow10045 : Integer.Sparse Key := [(key1173, -6), (key1166, -6), (key1246, -6), (key1173, -6), (key1101, 2), (key1095, 2), (key1229, 2), (key987, 2), (key981, 2), (key1173, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key987, 2), (key1173, 2), (key1101, 2)]

theorem rawRowCheck10045 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form4 = rawRow10045 := by decide +kernel

def row10045 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10045 : row10045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10045 := by decide +kernel

theorem rowEval10045 (x : Key → ℝ) : Integer.Sparse.eval row10045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10045, Integer.Sparse.eval_collectBalanced, rawRowCheck10045]

def rawRow10046 : Integer.Sparse Key := [(key1166, -6), (key1246, -6), (key1173, -6), (key1173, -6), (key1095, 2), (key1229, 2), (key1101, 2), (key1095, 2), (key1229, 2), (key981, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1101, 2), (key987, 2), (key1173, 2)]

theorem rawRowCheck10046 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form4 = rawRow10046 := by decide +kernel

def row10046 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10046 : row10046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10046 := by decide +kernel

theorem rowEval10046 (x : Key → ℝ) : Integer.Sparse.eval row10046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10046, Integer.Sparse.eval_collectBalanced, rawRowCheck10046]

def rawRow10047 : Integer.Sparse Key := [(key1246, -6), (key1166, -6), (key1173, -6), (key1173, -6), (key1229, 2), (key1095, 2), (key1101, 2), (key1229, 2), (key1095, 2), (key1246, 2), (key981, 2), (key1173, 2), (key987, 2), (key1101, 2), (key1173, 2), (key987, 2)]

theorem rawRowCheck10047 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form4 = rawRow10047 := by decide +kernel

def row10047 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10047 : row10047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10047 := by decide +kernel

theorem rowEval10047 (x : Key → ℝ) : Integer.Sparse.eval row10047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10047, Integer.Sparse.eval_collectBalanced, rawRowCheck10047]

def rawRow10048 : Integer.Sparse Key := [(key1173, -6), (key1246, -6), (key1166, -6), (key1173, -6), (key1101, 2), (key1229, 2), (key1095, 2), (key1173, 2), (key1246, 2), (key987, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1173, 2), (key987, 2), (key1101, 2)]

theorem rawRowCheck10048 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form4 = rawRow10048 := by decide +kernel

def row10048 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10048 : row10048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10048 := by decide +kernel

theorem rowEval10048 (x : Key → ℝ) : Integer.Sparse.eval row10048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10048, Integer.Sparse.eval_collectBalanced, rawRowCheck10048]

def rawRow10049 : Integer.Sparse Key := [(key1246, -6), (key1173, -6), (key1166, -6), (key1173, -6), (key1229, 2), (key1101, 2), (key1095, 2), (key1246, 2), (key1173, 2), (key1229, 2), (key987, 2), (key1095, 2), (key981, 2), (key1173, 2), (key1101, 2), (key987, 2)]

theorem rawRowCheck10049 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form4 = rawRow10049 := by decide +kernel

def row10049 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10049 : row10049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10049 := by decide +kernel

theorem rowEval10049 (x : Key → ℝ) : Integer.Sparse.eval row10049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10049, Integer.Sparse.eval_collectBalanced, rawRowCheck10049]

def rawRow10050 : Integer.Sparse Key := [(key1173, -6), (key1173, -6), (key1246, -6), (key1166, -6), (key1173, 2), (key1173, 2), (key1246, 2), (key987, 2), (key987, 2), (key1101, 2), (key1101, 2), (key1229, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1095, 2)]

theorem rawRowCheck10050 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form4 = rawRow10050 := by decide +kernel

def row10050 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10050 : row10050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10050 := by decide +kernel

theorem rowEval10050 (x : Key → ℝ) : Integer.Sparse.eval row10050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10050, Integer.Sparse.eval_collectBalanced, rawRowCheck10050]

def rawRow10051 : Integer.Sparse Key := [(key1173, -6), (key1246, -6), (key1173, -6), (key1166, -6), (key1173, 2), (key1246, 2), (key1173, 2), (key1101, 2), (key1229, 2), (key987, 2), (key1229, 2), (key987, 2), (key1101, 2), (key1095, 2), (key981, 2), (key1095, 2)]

theorem rawRowCheck10051 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form4 = rawRow10051 := by decide +kernel

def row10051 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10051 : row10051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10051 := by decide +kernel

theorem rowEval10051 (x : Key → ℝ) : Integer.Sparse.eval row10051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10051, Integer.Sparse.eval_collectBalanced, rawRowCheck10051]

def rawRow10052 : Integer.Sparse Key := [(key1246, -6), (key1173, -6), (key1173, -6), (key1166, -6), (key1246, 2), (key1173, 2), (key1173, 2), (key1229, 2), (key1101, 2), (key1229, 2), (key987, 2), (key1101, 2), (key987, 2), (key1095, 2), (key1095, 2), (key981, 2)]

theorem rawRowCheck10052 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form4 = rawRow10052 := by decide +kernel

def row10052 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

theorem rowCheck10052 : row10052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10052 := by decide +kernel

theorem rowEval10052 (x : Key → ℝ) : Integer.Sparse.eval row10052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck10052, Integer.Sparse.eval_collectBalanced, rawRowCheck10052]

def rawRow10053 : Integer.Sparse Key := [(key1003, -2), (key1003, -2), (key1009, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1159, -2), (key1159, -2), (key1233, -2), (key1243, -2), (key1243, -2), (key1003, 1), (key1003, 1), (key1017, 1), (key1017, 1), (key1022, 1), (key1022, 1), (key1038, 1), (key1038, 1), (key1073, 1), (key1073, 1), (key1080, 1), (key1080, 1), (key1125, 1), (key1125, 1), (key1152, 1), (key1152, 1), (key1174, 1), (key1174, 1), (key1236, 1), (key1236, 1), (key1243, 1), (key1243, 1), (key1247, 1), (key1247, 1)]

theorem rawRowCheck10053 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form5 = rawRow10053 := by decide +kernel

def row10053 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10053 : row10053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10053 := by decide +kernel

theorem rowEval10053 (x : Key → ℝ) : Integer.Sparse.eval row10053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10053, Integer.Sparse.eval_collectBalanced, rawRowCheck10053]

def rawRow10054 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1003, -2), (key1152, -2), (key1159, -2), (key1116, -2), (key1159, -2), (key1116, -2), (key1152, -2), (key1243, -2), (key1233, -2), (key1243, -2), (key1017, 1), (key1022, 1), (key1003, 1), (key1022, 1), (key1003, 1), (key1017, 1), (key1073, 1), (key1080, 1), (key1038, 1), (key1080, 1), (key1038, 1), (key1073, 1), (key1152, 1), (key1174, 1), (key1125, 1), (key1174, 1), (key1125, 1), (key1152, 1), (key1243, 1), (key1247, 1), (key1236, 1), (key1247, 1), (key1236, 1), (key1243, 1)]

theorem rawRowCheck10054 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form5 = rawRow10054 := by decide +kernel

def row10054 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10054 : row10054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10054 := by decide +kernel

theorem rowEval10054 (x : Key → ℝ) : Integer.Sparse.eval row10054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10054, Integer.Sparse.eval_collectBalanced, rawRowCheck10054]

def rawRow10055 : Integer.Sparse Key := [(key1009, -2), (key1003, -2), (key1003, -2), (key1159, -2), (key1152, -2), (key1159, -2), (key1116, -2), (key1152, -2), (key1116, -2), (key1243, -2), (key1243, -2), (key1233, -2), (key1022, 1), (key1017, 1), (key1022, 1), (key1003, 1), (key1017, 1), (key1003, 1), (key1080, 1), (key1073, 1), (key1080, 1), (key1038, 1), (key1073, 1), (key1038, 1), (key1174, 1), (key1152, 1), (key1174, 1), (key1125, 1), (key1152, 1), (key1125, 1), (key1247, 1), (key1243, 1), (key1247, 1), (key1236, 1), (key1243, 1), (key1236, 1)]

theorem rawRowCheck10055 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form5 = rawRow10055 := by decide +kernel

def row10055 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10055 : row10055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10055 := by decide +kernel

theorem rowEval10055 (x : Key → ℝ) : Integer.Sparse.eval row10055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10055, Integer.Sparse.eval_collectBalanced, rawRowCheck10055]

def rawRow10056 : Integer.Sparse Key := [(key1116, -2), (key1116, -2), (key1233, -2), (key1003, -2), (key1003, -2), (key1152, -2), (key1152, -2), (key1243, -2), (key1243, -2), (key1009, -2), (key1159, -2), (key1159, -2), (key1038, 1), (key1038, 1), (key1125, 1), (key1125, 1), (key1236, 1), (key1236, 1), (key1003, 1), (key1003, 1), (key1152, 1), (key1152, 1), (key1243, 1), (key1243, 1), (key1017, 1), (key1017, 1), (key1073, 1), (key1073, 1), (key1247, 1), (key1247, 1), (key1022, 1), (key1022, 1), (key1080, 1), (key1080, 1), (key1174, 1), (key1174, 1)]

theorem rawRowCheck10056 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form5 = rawRow10056 := by decide +kernel

def row10056 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10056 : row10056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10056 := by decide +kernel

theorem rowEval10056 (x : Key → ℝ) : Integer.Sparse.eval row10056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10056, Integer.Sparse.eval_collectBalanced, rawRowCheck10056]

def rawRow10057 : Integer.Sparse Key := [(key1116, -2), (key1233, -2), (key1116, -2), (key1152, -2), (key1243, -2), (key1003, -2), (key1243, -2), (key1003, -2), (key1152, -2), (key1159, -2), (key1009, -2), (key1159, -2), (key1125, 1), (key1236, 1), (key1038, 1), (key1236, 1), (key1038, 1), (key1125, 1), (key1152, 1), (key1243, 1), (key1003, 1), (key1243, 1), (key1003, 1), (key1152, 1), (key1073, 1), (key1247, 1), (key1017, 1), (key1247, 1), (key1017, 1), (key1073, 1), (key1080, 1), (key1174, 1), (key1022, 1), (key1174, 1), (key1022, 1), (key1080, 1)]

theorem rawRowCheck10057 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form5 = rawRow10057 := by decide +kernel

def row10057 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10057 : row10057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10057 := by decide +kernel

theorem rowEval10057 (x : Key → ℝ) : Integer.Sparse.eval row10057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10057, Integer.Sparse.eval_collectBalanced, rawRowCheck10057]

def rawRow10058 : Integer.Sparse Key := [(key1233, -2), (key1116, -2), (key1116, -2), (key1243, -2), (key1152, -2), (key1243, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1159, -2), (key1159, -2), (key1009, -2), (key1236, 1), (key1125, 1), (key1236, 1), (key1038, 1), (key1125, 1), (key1038, 1), (key1243, 1), (key1152, 1), (key1243, 1), (key1003, 1), (key1152, 1), (key1003, 1), (key1247, 1), (key1073, 1), (key1247, 1), (key1017, 1), (key1073, 1), (key1017, 1), (key1174, 1), (key1080, 1), (key1174, 1), (key1022, 1), (key1080, 1), (key1022, 1)]

theorem rawRowCheck10058 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form5 = rawRow10058 := by decide +kernel

def row10058 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10058 : row10058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10058 := by decide +kernel

theorem rowEval10058 (x : Key → ℝ) : Integer.Sparse.eval row10058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck10058, Integer.Sparse.eval_collectBalanced, rawRowCheck10058]

def rawRow10059 : Integer.Sparse Key := [(key1152, -2), (key1159, -2), (key1243, -2), (key1003, -2), (key1009, -2), (key1116, -2), (key1159, -2), (key1233, -2), (key1243, -2), (key1003, -2), (key1116, -2), (key1152, -2), (key1073, 1), (key1080, 1), (key1152, 1), (key1174, 1), (key1243, 1), (key1247, 1), (key1017, 1), (key1022, 1), (key1125, 1), (key1174, 1), (key1236, 1), (key1247, 1), (key1003, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1236, 1), (key1243, 1), (key1003, 1), (key1017, 1), (key1038, 1), (key1073, 1), (key1125, 1), (key1152, 1)]

theorem rawRowCheck10059 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form5 = rawRow10059 := by decide +kernel

def row10059 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10059 : row10059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10059 := by decide +kernel

theorem rowEval10059 (x : Key → ℝ) : Integer.Sparse.eval row10059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10059, Integer.Sparse.eval_collectBalanced, rawRowCheck10059]

def rawRow10060 : Integer.Sparse Key := [(key1159, -2), (key1152, -2), (key1243, -2), (key1009, -2), (key1003, -2), (key1159, -2), (key1116, -2), (key1243, -2), (key1233, -2), (key1003, -2), (key1152, -2), (key1116, -2), (key1080, 1), (key1073, 1), (key1174, 1), (key1152, 1), (key1247, 1), (key1243, 1), (key1022, 1), (key1017, 1), (key1174, 1), (key1125, 1), (key1247, 1), (key1236, 1), (key1022, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1243, 1), (key1236, 1), (key1017, 1), (key1003, 1), (key1073, 1), (key1038, 1), (key1152, 1), (key1125, 1)]

theorem rawRowCheck10060 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form5 = rawRow10060 := by decide +kernel

def row10060 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10060 : row10060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10060 := by decide +kernel

theorem rowEval10060 (x : Key → ℝ) : Integer.Sparse.eval row10060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10060, Integer.Sparse.eval_collectBalanced, rawRowCheck10060]

def rawRow10061 : Integer.Sparse Key := [(key1152, -2), (key1243, -2), (key1159, -2), (key1116, -2), (key1233, -2), (key1003, -2), (key1243, -2), (key1009, -2), (key1159, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1152, 1), (key1243, 1), (key1073, 1), (key1247, 1), (key1080, 1), (key1174, 1), (key1125, 1), (key1236, 1), (key1017, 1), (key1247, 1), (key1022, 1), (key1174, 1), (key1038, 1), (key1236, 1), (key1003, 1), (key1243, 1), (key1022, 1), (key1080, 1), (key1038, 1), (key1125, 1), (key1003, 1), (key1152, 1), (key1017, 1), (key1073, 1)]

theorem rawRowCheck10061 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form5 = rawRow10061 := by decide +kernel

def row10061 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10061 : row10061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10061 := by decide +kernel

theorem rowEval10061 (x : Key → ℝ) : Integer.Sparse.eval row10061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10061, Integer.Sparse.eval_collectBalanced, rawRowCheck10061]

def rawRow10062 : Integer.Sparse Key := [(key1243, -2), (key1152, -2), (key1159, -2), (key1233, -2), (key1116, -2), (key1243, -2), (key1003, -2), (key1159, -2), (key1009, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1243, 1), (key1152, 1), (key1247, 1), (key1073, 1), (key1174, 1), (key1080, 1), (key1236, 1), (key1125, 1), (key1247, 1), (key1017, 1), (key1174, 1), (key1022, 1), (key1236, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1080, 1), (key1022, 1), (key1125, 1), (key1038, 1), (key1152, 1), (key1003, 1), (key1073, 1), (key1017, 1)]

theorem rawRowCheck10062 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form5 = rawRow10062 := by decide +kernel

def row10062 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10062 : row10062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10062 := by decide +kernel

theorem rowEval10062 (x : Key → ℝ) : Integer.Sparse.eval row10062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck10062, Integer.Sparse.eval_collectBalanced, rawRowCheck10062]

def rawRow10063 : Integer.Sparse Key := [(key1159, -2), (key1243, -2), (key1152, -2), (key1159, -2), (key1243, -2), (key1009, -2), (key1233, -2), (key1003, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1174, 1), (key1247, 1), (key1080, 1), (key1243, 1), (key1073, 1), (key1152, 1), (key1174, 1), (key1247, 1), (key1022, 1), (key1236, 1), (key1017, 1), (key1125, 1), (key1080, 1), (key1243, 1), (key1022, 1), (key1236, 1), (key1003, 1), (key1038, 1), (key1073, 1), (key1152, 1), (key1017, 1), (key1125, 1), (key1003, 1), (key1038, 1)]

theorem rawRowCheck10063 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form5 = rawRow10063 := by decide +kernel

def row10063 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10063 : row10063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10063 := by decide +kernel

theorem rowEval10063 (x : Key → ℝ) : Integer.Sparse.eval row10063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10063, Integer.Sparse.eval_collectBalanced, rawRowCheck10063]

def rawRow10064 : Integer.Sparse Key := [(key1243, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1233, -2), (key1009, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1116, -2), (key1003, -2), (key1247, 1), (key1174, 1), (key1243, 1), (key1080, 1), (key1152, 1), (key1073, 1), (key1247, 1), (key1174, 1), (key1236, 1), (key1022, 1), (key1125, 1), (key1017, 1), (key1243, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1038, 1), (key1003, 1), (key1152, 1), (key1073, 1), (key1125, 1), (key1017, 1), (key1038, 1), (key1003, 1)]

theorem rawRowCheck10064 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form5 = rawRow10064 := by decide +kernel

def row10064 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

theorem rowCheck10064 : row10064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10064 := by decide +kernel

theorem rowEval10064 (x : Key → ℝ) : Integer.Sparse.eval row10064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck10064, Integer.Sparse.eval_collectBalanced, rawRowCheck10064]

def rawRow10065 : Integer.Sparse Key := [(key1017, -2), (key1022, -2), (key1022, -2), (key1125, -2), (key1130, -2), (key1125, -2), (key1174, -2), (key1130, -2), (key1174, -2), (key1236, -2), (key1236, -2), (key1247, -2), (key1003, 1), (key1009, 1), (key1003, 1), (key1022, 1), (key1009, 1), (key1022, 1), (key1038, 1), (key1044, 1), (key1038, 1), (key1080, 1), (key1044, 1), (key1080, 1), (key1116, 1), (key1130, 1), (key1116, 1), (key1159, 1), (key1130, 1), (key1159, 1), (key1233, 1), (key1236, 1), (key1233, 1), (key1243, 1), (key1236, 1), (key1243, 1)]

theorem rawRowCheck10065 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form5 = rawRow10065 := by decide +kernel

def row10065 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10065 : row10065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10065 := by decide +kernel

theorem rowEval10065 (x : Key → ℝ) : Integer.Sparse.eval row10065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10065, Integer.Sparse.eval_collectBalanced, rawRowCheck10065]

def rawRow10066 : Integer.Sparse Key := [(key1022, -2), (key1017, -2), (key1022, -2), (key1130, -2), (key1125, -2), (key1174, -2), (key1125, -2), (key1174, -2), (key1130, -2), (key1236, -2), (key1247, -2), (key1236, -2), (key1009, 1), (key1003, 1), (key1022, 1), (key1003, 1), (key1022, 1), (key1009, 1), (key1044, 1), (key1038, 1), (key1080, 1), (key1038, 1), (key1080, 1), (key1044, 1), (key1130, 1), (key1116, 1), (key1159, 1), (key1116, 1), (key1159, 1), (key1130, 1), (key1236, 1), (key1233, 1), (key1243, 1), (key1233, 1), (key1243, 1), (key1236, 1)]

theorem rawRowCheck10066 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form5 = rawRow10066 := by decide +kernel

def row10066 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10066 : row10066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10066 := by decide +kernel

theorem rowEval10066 (x : Key → ℝ) : Integer.Sparse.eval row10066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10066, Integer.Sparse.eval_collectBalanced, rawRowCheck10066]

def rawRow10067 : Integer.Sparse Key := [(key1022, -2), (key1022, -2), (key1017, -2), (key1174, -2), (key1174, -2), (key1130, -2), (key1130, -2), (key1125, -2), (key1125, -2), (key1247, -2), (key1236, -2), (key1236, -2), (key1022, 1), (key1022, 1), (key1009, 1), (key1009, 1), (key1003, 1), (key1003, 1), (key1080, 1), (key1080, 1), (key1044, 1), (key1044, 1), (key1038, 1), (key1038, 1), (key1159, 1), (key1159, 1), (key1130, 1), (key1130, 1), (key1116, 1), (key1116, 1), (key1243, 1), (key1243, 1), (key1236, 1), (key1236, 1), (key1233, 1), (key1233, 1)]

theorem rawRowCheck10067 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form5 = rawRow10067 := by decide +kernel

def row10067 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10067 : row10067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10067 := by decide +kernel

theorem rowEval10067 (x : Key → ℝ) : Integer.Sparse.eval row10067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10067, Integer.Sparse.eval_collectBalanced, rawRowCheck10067]

def rawRow10068 : Integer.Sparse Key := [(key1125, -2), (key1130, -2), (key1236, -2), (key1017, -2), (key1022, -2), (key1125, -2), (key1174, -2), (key1236, -2), (key1247, -2), (key1022, -2), (key1130, -2), (key1174, -2), (key1038, 1), (key1044, 1), (key1116, 1), (key1130, 1), (key1233, 1), (key1236, 1), (key1003, 1), (key1009, 1), (key1116, 1), (key1159, 1), (key1233, 1), (key1243, 1), (key1003, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1236, 1), (key1243, 1), (key1009, 1), (key1022, 1), (key1044, 1), (key1080, 1), (key1130, 1), (key1159, 1)]

theorem rawRowCheck10068 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form5 = rawRow10068 := by decide +kernel

def row10068 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10068 : row10068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10068 := by decide +kernel

theorem rowEval10068 (x : Key → ℝ) : Integer.Sparse.eval row10068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10068, Integer.Sparse.eval_collectBalanced, rawRowCheck10068]

def rawRow10069 : Integer.Sparse Key := [(key1130, -2), (key1125, -2), (key1236, -2), (key1022, -2), (key1017, -2), (key1174, -2), (key1125, -2), (key1247, -2), (key1236, -2), (key1022, -2), (key1174, -2), (key1130, -2), (key1044, 1), (key1038, 1), (key1130, 1), (key1116, 1), (key1236, 1), (key1233, 1), (key1009, 1), (key1003, 1), (key1159, 1), (key1116, 1), (key1243, 1), (key1233, 1), (key1022, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1243, 1), (key1236, 1), (key1022, 1), (key1009, 1), (key1080, 1), (key1044, 1), (key1159, 1), (key1130, 1)]

theorem rawRowCheck10069 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form5 = rawRow10069 := by decide +kernel

def row10069 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10069 : row10069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10069 := by decide +kernel

theorem rowEval10069 (x : Key → ℝ) : Integer.Sparse.eval row10069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10069, Integer.Sparse.eval_collectBalanced, rawRowCheck10069]

def rawRow10070 : Integer.Sparse Key := [(key1125, -2), (key1236, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1017, -2), (key1247, -2), (key1022, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1174, -2), (key1116, 1), (key1233, 1), (key1038, 1), (key1236, 1), (key1044, 1), (key1130, 1), (key1116, 1), (key1233, 1), (key1003, 1), (key1243, 1), (key1009, 1), (key1159, 1), (key1038, 1), (key1236, 1), (key1003, 1), (key1243, 1), (key1022, 1), (key1080, 1), (key1044, 1), (key1130, 1), (key1009, 1), (key1159, 1), (key1022, 1), (key1080, 1)]

theorem rawRowCheck10070 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form5 = rawRow10070 := by decide +kernel

def row10070 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10070 : row10070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10070 := by decide +kernel

theorem rowEval10070 (x : Key → ℝ) : Integer.Sparse.eval row10070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10070, Integer.Sparse.eval_collectBalanced, rawRowCheck10070]

def rawRow10071 : Integer.Sparse Key := [(key1236, -2), (key1125, -2), (key1130, -2), (key1236, -2), (key1125, -2), (key1247, -2), (key1017, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1233, 1), (key1116, 1), (key1236, 1), (key1038, 1), (key1130, 1), (key1044, 1), (key1233, 1), (key1116, 1), (key1243, 1), (key1003, 1), (key1159, 1), (key1009, 1), (key1236, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1080, 1), (key1022, 1), (key1130, 1), (key1044, 1), (key1159, 1), (key1009, 1), (key1080, 1), (key1022, 1)]

theorem rawRowCheck10071 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form5 = rawRow10071 := by decide +kernel

def row10071 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10071 : row10071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10071 := by decide +kernel

theorem rowEval10071 (x : Key → ℝ) : Integer.Sparse.eval row10071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck10071, Integer.Sparse.eval_collectBalanced, rawRowCheck10071]

def rawRow10072 : Integer.Sparse Key := [(key1130, -2), (key1236, -2), (key1125, -2), (key1174, -2), (key1247, -2), (key1022, -2), (key1236, -2), (key1017, -2), (key1125, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1130, 1), (key1236, 1), (key1044, 1), (key1233, 1), (key1038, 1), (key1116, 1), (key1159, 1), (key1243, 1), (key1009, 1), (key1233, 1), (key1003, 1), (key1116, 1), (key1080, 1), (key1243, 1), (key1022, 1), (key1236, 1), (key1003, 1), (key1038, 1), (key1080, 1), (key1159, 1), (key1022, 1), (key1130, 1), (key1009, 1), (key1044, 1)]

theorem rawRowCheck10072 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form5 = rawRow10072 := by decide +kernel

def row10072 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10072 : row10072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10072 := by decide +kernel

theorem rowEval10072 (x : Key → ℝ) : Integer.Sparse.eval row10072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10072, Integer.Sparse.eval_collectBalanced, rawRowCheck10072]

def rawRow10073 : Integer.Sparse Key := [(key1236, -2), (key1130, -2), (key1125, -2), (key1247, -2), (key1174, -2), (key1236, -2), (key1022, -2), (key1125, -2), (key1017, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1236, 1), (key1130, 1), (key1233, 1), (key1044, 1), (key1116, 1), (key1038, 1), (key1243, 1), (key1159, 1), (key1233, 1), (key1009, 1), (key1116, 1), (key1003, 1), (key1243, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1038, 1), (key1003, 1), (key1159, 1), (key1080, 1), (key1130, 1), (key1022, 1), (key1044, 1), (key1009, 1)]

theorem rawRowCheck10073 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form5 = rawRow10073 := by decide +kernel

def row10073 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10073 : row10073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10073 := by decide +kernel

theorem rowEval10073 (x : Key → ℝ) : Integer.Sparse.eval row10073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck10073, Integer.Sparse.eval_collectBalanced, rawRowCheck10073]

def rawRow10074 : Integer.Sparse Key := [(key1174, -2), (key1174, -2), (key1247, -2), (key1022, -2), (key1022, -2), (key1130, -2), (key1130, -2), (key1236, -2), (key1236, -2), (key1017, -2), (key1125, -2), (key1125, -2), (key1080, 1), (key1080, 1), (key1159, 1), (key1159, 1), (key1243, 1), (key1243, 1), (key1022, 1), (key1022, 1), (key1130, 1), (key1130, 1), (key1236, 1), (key1236, 1), (key1009, 1), (key1009, 1), (key1044, 1), (key1044, 1), (key1233, 1), (key1233, 1), (key1003, 1), (key1003, 1), (key1038, 1), (key1038, 1), (key1116, 1), (key1116, 1)]

theorem rawRowCheck10074 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form5 = rawRow10074 := by decide +kernel

def row10074 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10074 : row10074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10074 := by decide +kernel

theorem rowEval10074 (x : Key → ℝ) : Integer.Sparse.eval row10074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10074, Integer.Sparse.eval_collectBalanced, rawRowCheck10074]

def rawRow10075 : Integer.Sparse Key := [(key1174, -2), (key1247, -2), (key1174, -2), (key1130, -2), (key1236, -2), (key1022, -2), (key1236, -2), (key1022, -2), (key1130, -2), (key1125, -2), (key1017, -2), (key1125, -2), (key1159, 1), (key1243, 1), (key1080, 1), (key1243, 1), (key1080, 1), (key1159, 1), (key1130, 1), (key1236, 1), (key1022, 1), (key1236, 1), (key1022, 1), (key1130, 1), (key1044, 1), (key1233, 1), (key1009, 1), (key1233, 1), (key1009, 1), (key1044, 1), (key1038, 1), (key1116, 1), (key1003, 1), (key1116, 1), (key1003, 1), (key1038, 1)]

theorem rawRowCheck10075 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form5 = rawRow10075 := by decide +kernel

def row10075 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10075 : row10075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10075 := by decide +kernel

theorem rowEval10075 (x : Key → ℝ) : Integer.Sparse.eval row10075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10075, Integer.Sparse.eval_collectBalanced, rawRowCheck10075]

def rawRow10076 : Integer.Sparse Key := [(key1247, -2), (key1174, -2), (key1174, -2), (key1236, -2), (key1130, -2), (key1236, -2), (key1022, -2), (key1130, -2), (key1022, -2), (key1125, -2), (key1125, -2), (key1017, -2), (key1243, 1), (key1159, 1), (key1243, 1), (key1080, 1), (key1159, 1), (key1080, 1), (key1236, 1), (key1130, 1), (key1236, 1), (key1022, 1), (key1130, 1), (key1022, 1), (key1233, 1), (key1044, 1), (key1233, 1), (key1009, 1), (key1044, 1), (key1009, 1), (key1116, 1), (key1038, 1), (key1116, 1), (key1003, 1), (key1038, 1), (key1003, 1)]

theorem rawRowCheck10076 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form5 = rawRow10076 := by decide +kernel

def row10076 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

theorem rowCheck10076 : row10076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10076 := by decide +kernel

theorem rowEval10076 (x : Key → ℝ) : Integer.Sparse.eval row10076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck10076, Integer.Sparse.eval_collectBalanced, rawRowCheck10076]

def rawRow10077 : Integer.Sparse Key := [(key1094, -24), (key980, 6), (key1094, 6), (key1165, 6), (key1165, 6)]

theorem rawRowCheck10077 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6 = rawRow10077 := by decide +kernel

def row10077 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10077 : row10077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10077 := by decide +kernel

theorem rowEval10077 (x : Key → ℝ) : Integer.Sparse.eval row10077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10077, Integer.Sparse.eval_collectBalanced, rawRowCheck10077]

def rawRow10078 : Integer.Sparse Key := [(key1094, -24), (key980, 6), (key1165, 6), (key1094, 6), (key1165, 6)]

theorem rawRowCheck10078 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6 = rawRow10078 := by decide +kernel

def row10078 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10078 : row10078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10078 := by decide +kernel

theorem rowEval10078 (x : Key → ℝ) : Integer.Sparse.eval row10078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10078, Integer.Sparse.eval_collectBalanced, rawRowCheck10078]

def rawRow10079 : Integer.Sparse Key := [(key1094, -24), (key980, 6), (key1165, 6), (key1165, 6), (key1094, 6)]

theorem rawRowCheck10079 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6 = rawRow10079 := by decide +kernel

def row10079 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10079 : row10079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10079 := by decide +kernel

theorem rowEval10079 (x : Key → ℝ) : Integer.Sparse.eval row10079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10079, Integer.Sparse.eval_collectBalanced, rawRowCheck10079]

def rawRow10080 : Integer.Sparse Key := [(key1094, -24), (key1094, 6), (key980, 6), (key1165, 6), (key1165, 6)]

theorem rawRowCheck10080 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6 = rawRow10080 := by decide +kernel

def row10080 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10080 : row10080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10080 := by decide +kernel

theorem rowEval10080 (x : Key → ℝ) : Integer.Sparse.eval row10080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10080, Integer.Sparse.eval_collectBalanced, rawRowCheck10080]

def rawRow10081 : Integer.Sparse Key := [(key1094, -24), (key1094, 6), (key1165, 6), (key980, 6), (key1165, 6)]

theorem rawRowCheck10081 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6 = rawRow10081 := by decide +kernel

def row10081 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10081 : row10081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10081 := by decide +kernel

theorem rowEval10081 (x : Key → ℝ) : Integer.Sparse.eval row10081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10081, Integer.Sparse.eval_collectBalanced, rawRowCheck10081]

def rawRow10082 : Integer.Sparse Key := [(key1094, -24), (key1094, 6), (key1165, 6), (key1165, 6), (key980, 6)]

theorem rawRowCheck10082 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6 = rawRow10082 := by decide +kernel

def row10082 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10082 : row10082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10082 := by decide +kernel

theorem rowEval10082 (x : Key → ℝ) : Integer.Sparse.eval row10082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10082, Integer.Sparse.eval_collectBalanced, rawRowCheck10082]

def rawRow10083 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key980, 6), (key1094, 6), (key1165, 6)]

theorem rawRowCheck10083 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6 = rawRow10083 := by decide +kernel

def row10083 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10083 : row10083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10083 := by decide +kernel

theorem rowEval10083 (x : Key → ℝ) : Integer.Sparse.eval row10083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10083, Integer.Sparse.eval_collectBalanced, rawRowCheck10083]

def rawRow10084 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key980, 6), (key1165, 6), (key1094, 6)]

theorem rawRowCheck10084 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6 = rawRow10084 := by decide +kernel

def row10084 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10084 : row10084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10084 := by decide +kernel

theorem rowEval10084 (x : Key → ℝ) : Integer.Sparse.eval row10084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10084, Integer.Sparse.eval_collectBalanced, rawRowCheck10084]

def rawRow10085 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key1094, 6), (key980, 6), (key1165, 6)]

theorem rawRowCheck10085 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6 = rawRow10085 := by decide +kernel

def row10085 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10085 : row10085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10085 := by decide +kernel

theorem rowEval10085 (x : Key → ℝ) : Integer.Sparse.eval row10085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10085, Integer.Sparse.eval_collectBalanced, rawRowCheck10085]

def rawRow10086 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key1094, 6), (key1165, 6), (key980, 6)]

theorem rawRowCheck10086 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6 = rawRow10086 := by decide +kernel

def row10086 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10086 : row10086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10086 := by decide +kernel

theorem rowEval10086 (x : Key → ℝ) : Integer.Sparse.eval row10086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10086, Integer.Sparse.eval_collectBalanced, rawRowCheck10086]

def rawRow10087 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key1165, 6), (key980, 6), (key1094, 6)]

theorem rawRowCheck10087 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6 = rawRow10087 := by decide +kernel

def row10087 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10087 : row10087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10087 := by decide +kernel

theorem rowEval10087 (x : Key → ℝ) : Integer.Sparse.eval row10087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10087, Integer.Sparse.eval_collectBalanced, rawRowCheck10087]

def rawRow10088 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key1165, 6), (key1094, 6), (key980, 6)]

theorem rawRowCheck10088 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6 = rawRow10088 := by decide +kernel

def row10088 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

theorem rowCheck10088 : row10088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10088 := by decide +kernel

theorem rowEval10088 (x : Key → ℝ) : Integer.Sparse.eval row10088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10088, Integer.Sparse.eval_collectBalanced, rawRowCheck10088]

def rawRow10089 : Integer.Sparse Key := [(key1165, -24), (key980, 6), (key1094, 6), (key1094, 6), (key1165, 6)]

theorem rawRowCheck10089 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form6 = rawRow10089 := by decide +kernel

def row10089 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10089 : row10089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10089 := by decide +kernel

theorem rowEval10089 (x : Key → ℝ) : Integer.Sparse.eval row10089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10089, Integer.Sparse.eval_collectBalanced, rawRowCheck10089]

def rawRow10090 : Integer.Sparse Key := [(key1165, -24), (key980, 6), (key1094, 6), (key1165, 6), (key1094, 6)]

theorem rawRowCheck10090 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form6 = rawRow10090 := by decide +kernel

def row10090 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10090 : row10090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10090 := by decide +kernel

theorem rowEval10090 (x : Key → ℝ) : Integer.Sparse.eval row10090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10090, Integer.Sparse.eval_collectBalanced, rawRowCheck10090]

def rawRow10091 : Integer.Sparse Key := [(key1165, -24), (key980, 6), (key1165, 6), (key1094, 6), (key1094, 6)]

theorem rawRowCheck10091 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form6 = rawRow10091 := by decide +kernel

def row10091 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10091 : row10091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10091 := by decide +kernel

theorem rowEval10091 (x : Key → ℝ) : Integer.Sparse.eval row10091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10091, Integer.Sparse.eval_collectBalanced, rawRowCheck10091]

def rawRow10092 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key980, 6), (key1094, 6), (key1165, 6)]

theorem rawRowCheck10092 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form6 = rawRow10092 := by decide +kernel

def row10092 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10092 : row10092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10092 := by decide +kernel

theorem rowEval10092 (x : Key → ℝ) : Integer.Sparse.eval row10092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10092, Integer.Sparse.eval_collectBalanced, rawRowCheck10092]

def rawRow10093 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key980, 6), (key1165, 6), (key1094, 6)]

theorem rawRowCheck10093 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form6 = rawRow10093 := by decide +kernel

def row10093 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10093 : row10093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10093 := by decide +kernel

theorem rowEval10093 (x : Key → ℝ) : Integer.Sparse.eval row10093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10093, Integer.Sparse.eval_collectBalanced, rawRowCheck10093]

def rawRow10094 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key1094, 6), (key980, 6), (key1165, 6)]

theorem rawRowCheck10094 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form6 = rawRow10094 := by decide +kernel

def row10094 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10094 : row10094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10094 := by decide +kernel

theorem rowEval10094 (x : Key → ℝ) : Integer.Sparse.eval row10094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10094, Integer.Sparse.eval_collectBalanced, rawRowCheck10094]

def rawRow10095 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key1094, 6), (key1165, 6), (key980, 6)]

theorem rawRowCheck10095 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form6 = rawRow10095 := by decide +kernel

def row10095 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10095 : row10095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10095 := by decide +kernel

theorem rowEval10095 (x : Key → ℝ) : Integer.Sparse.eval row10095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10095, Integer.Sparse.eval_collectBalanced, rawRowCheck10095]

def rawRow10096 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key1165, 6), (key980, 6), (key1094, 6)]

theorem rawRowCheck10096 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form6 = rawRow10096 := by decide +kernel

def row10096 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10096 : row10096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10096 := by decide +kernel

theorem rowEval10096 (x : Key → ℝ) : Integer.Sparse.eval row10096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10096, Integer.Sparse.eval_collectBalanced, rawRowCheck10096]

def rawRow10097 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key1165, 6), (key1094, 6), (key980, 6)]

theorem rawRowCheck10097 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form6 = rawRow10097 := by decide +kernel

def row10097 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10097 : row10097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10097 := by decide +kernel

theorem rowEval10097 (x : Key → ℝ) : Integer.Sparse.eval row10097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10097, Integer.Sparse.eval_collectBalanced, rawRowCheck10097]

def rawRow10098 : Integer.Sparse Key := [(key1165, -24), (key1165, 6), (key980, 6), (key1094, 6), (key1094, 6)]

theorem rawRowCheck10098 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form6 = rawRow10098 := by decide +kernel

def row10098 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10098 : row10098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10098 := by decide +kernel

theorem rowEval10098 (x : Key → ℝ) : Integer.Sparse.eval row10098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10098, Integer.Sparse.eval_collectBalanced, rawRowCheck10098]

def rawRow10099 : Integer.Sparse Key := [(key1165, -24), (key1165, 6), (key1094, 6), (key980, 6), (key1094, 6)]

theorem rawRowCheck10099 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form6 = rawRow10099 := by decide +kernel

def row10099 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10099 : row10099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10099 := by decide +kernel

theorem rowEval10099 (x : Key → ℝ) : Integer.Sparse.eval row10099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10099, Integer.Sparse.eval_collectBalanced, rawRowCheck10099]

def rawRow10100 : Integer.Sparse Key := [(key1165, -24), (key1165, 6), (key1094, 6), (key1094, 6), (key980, 6)]

theorem rawRowCheck10100 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form6 = rawRow10100 := by decide +kernel

def row10100 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

theorem rowCheck10100 : row10100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10100 := by decide +kernel

theorem rowEval10100 (x : Key → ℝ) : Integer.Sparse.eval row10100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck10100, Integer.Sparse.eval_collectBalanced, rawRowCheck10100]

def rawRow10101 : Integer.Sparse Key := [(key1038, -2), (key1038, -2), (key1044, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1130, -2), (key1130, -2), (key1233, -2), (key1236, -2), (key1236, -2), (key1003, 2), (key1003, 2), (key1009, 2), (key1116, 2), (key1116, 2), (key1152, 2), (key1152, 2), (key1159, 2), (key1159, 2), (key1233, 2), (key1243, 2), (key1243, 2)]

theorem rawRowCheck10101 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form7 = rawRow10101 := by decide +kernel

def row10101 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10101 : row10101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10101 := by decide +kernel

theorem rowEval10101 (x : Key → ℝ) : Integer.Sparse.eval row10101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10101, Integer.Sparse.eval_collectBalanced, rawRowCheck10101]

def rawRow10102 : Integer.Sparse Key := [(key1038, -2), (key1044, -2), (key1038, -2), (key1125, -2), (key1130, -2), (key1116, -2), (key1130, -2), (key1116, -2), (key1125, -2), (key1236, -2), (key1233, -2), (key1236, -2), (key1003, 2), (key1009, 2), (key1003, 2), (key1152, 2), (key1159, 2), (key1116, 2), (key1159, 2), (key1116, 2), (key1152, 2), (key1243, 2), (key1233, 2), (key1243, 2)]

theorem rawRowCheck10102 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form7 = rawRow10102 := by decide +kernel

def row10102 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10102 : row10102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10102 := by decide +kernel

theorem rowEval10102 (x : Key → ℝ) : Integer.Sparse.eval row10102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10102, Integer.Sparse.eval_collectBalanced, rawRowCheck10102]

def rawRow10103 : Integer.Sparse Key := [(key1044, -2), (key1038, -2), (key1038, -2), (key1130, -2), (key1125, -2), (key1130, -2), (key1116, -2), (key1125, -2), (key1116, -2), (key1236, -2), (key1236, -2), (key1233, -2), (key1009, 2), (key1003, 2), (key1003, 2), (key1159, 2), (key1152, 2), (key1159, 2), (key1116, 2), (key1152, 2), (key1116, 2), (key1243, 2), (key1243, 2), (key1233, 2)]

theorem rawRowCheck10103 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form7 = rawRow10103 := by decide +kernel

def row10103 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10103 : row10103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10103 := by decide +kernel

theorem rowEval10103 (x : Key → ℝ) : Integer.Sparse.eval row10103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10103, Integer.Sparse.eval_collectBalanced, rawRowCheck10103]

def rawRow10104 : Integer.Sparse Key := [(key1116, -2), (key1116, -2), (key1233, -2), (key1038, -2), (key1038, -2), (key1125, -2), (key1125, -2), (key1236, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1130, -2), (key1116, 2), (key1116, 2), (key1233, 2), (key1003, 2), (key1003, 2), (key1152, 2), (key1152, 2), (key1243, 2), (key1243, 2), (key1009, 2), (key1159, 2), (key1159, 2)]

theorem rawRowCheck10104 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form7 = rawRow10104 := by decide +kernel

def row10104 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10104 : row10104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10104 := by decide +kernel

theorem rowEval10104 (x : Key → ℝ) : Integer.Sparse.eval row10104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10104, Integer.Sparse.eval_collectBalanced, rawRowCheck10104]

def rawRow10105 : Integer.Sparse Key := [(key1116, -2), (key1233, -2), (key1116, -2), (key1125, -2), (key1236, -2), (key1038, -2), (key1236, -2), (key1038, -2), (key1125, -2), (key1130, -2), (key1044, -2), (key1130, -2), (key1116, 2), (key1233, 2), (key1116, 2), (key1152, 2), (key1243, 2), (key1003, 2), (key1243, 2), (key1003, 2), (key1152, 2), (key1159, 2), (key1009, 2), (key1159, 2)]

theorem rawRowCheck10105 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form7 = rawRow10105 := by decide +kernel

def row10105 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10105 : row10105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10105 := by decide +kernel

theorem rowEval10105 (x : Key → ℝ) : Integer.Sparse.eval row10105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10105, Integer.Sparse.eval_collectBalanced, rawRowCheck10105]

def rawRow10106 : Integer.Sparse Key := [(key1233, -2), (key1116, -2), (key1116, -2), (key1236, -2), (key1125, -2), (key1236, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1130, -2), (key1130, -2), (key1044, -2), (key1233, 2), (key1116, 2), (key1116, 2), (key1243, 2), (key1152, 2), (key1243, 2), (key1003, 2), (key1152, 2), (key1003, 2), (key1159, 2), (key1159, 2), (key1009, 2)]

theorem rawRowCheck10106 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form7 = rawRow10106 := by decide +kernel

def row10106 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10106 : row10106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10106 := by decide +kernel

theorem rowEval10106 (x : Key → ℝ) : Integer.Sparse.eval row10106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck10106, Integer.Sparse.eval_collectBalanced, rawRowCheck10106]

def rawRow10107 : Integer.Sparse Key := [(key1125, -2), (key1130, -2), (key1236, -2), (key1038, -2), (key1044, -2), (key1116, -2), (key1130, -2), (key1233, -2), (key1236, -2), (key1038, -2), (key1116, -2), (key1125, -2), (key1152, 2), (key1159, 2), (key1243, 2), (key1003, 2), (key1009, 2), (key1116, 2), (key1159, 2), (key1233, 2), (key1243, 2), (key1003, 2), (key1116, 2), (key1152, 2)]

theorem rawRowCheck10107 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form7 = rawRow10107 := by decide +kernel

def row10107 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10107 : row10107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10107 := by decide +kernel

theorem rowEval10107 (x : Key → ℝ) : Integer.Sparse.eval row10107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10107, Integer.Sparse.eval_collectBalanced, rawRowCheck10107]

def rawRow10108 : Integer.Sparse Key := [(key1130, -2), (key1125, -2), (key1236, -2), (key1044, -2), (key1038, -2), (key1130, -2), (key1116, -2), (key1236, -2), (key1233, -2), (key1038, -2), (key1125, -2), (key1116, -2), (key1159, 2), (key1152, 2), (key1243, 2), (key1009, 2), (key1003, 2), (key1159, 2), (key1116, 2), (key1243, 2), (key1233, 2), (key1003, 2), (key1152, 2), (key1116, 2)]

theorem rawRowCheck10108 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form7 = rawRow10108 := by decide +kernel

def row10108 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10108 : row10108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10108 := by decide +kernel

theorem rowEval10108 (x : Key → ℝ) : Integer.Sparse.eval row10108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10108, Integer.Sparse.eval_collectBalanced, rawRowCheck10108]

def rawRow10109 : Integer.Sparse Key := [(key1125, -2), (key1236, -2), (key1130, -2), (key1116, -2), (key1233, -2), (key1038, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1116, -2), (key1038, -2), (key1125, -2), (key1152, 2), (key1243, 2), (key1159, 2), (key1116, 2), (key1233, 2), (key1003, 2), (key1243, 2), (key1009, 2), (key1159, 2), (key1116, 2), (key1003, 2), (key1152, 2)]

theorem rawRowCheck10109 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form7 = rawRow10109 := by decide +kernel

def row10109 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10109 : row10109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10109 := by decide +kernel

theorem rowEval10109 (x : Key → ℝ) : Integer.Sparse.eval row10109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10109, Integer.Sparse.eval_collectBalanced, rawRowCheck10109]

def rawRow10110 : Integer.Sparse Key := [(key1236, -2), (key1125, -2), (key1130, -2), (key1233, -2), (key1116, -2), (key1236, -2), (key1038, -2), (key1130, -2), (key1044, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1243, 2), (key1152, 2), (key1159, 2), (key1233, 2), (key1116, 2), (key1243, 2), (key1003, 2), (key1159, 2), (key1009, 2), (key1116, 2), (key1152, 2), (key1003, 2)]

theorem rawRowCheck10110 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form7 = rawRow10110 := by decide +kernel

def row10110 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10110 : row10110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10110 := by decide +kernel

theorem rowEval10110 (x : Key → ℝ) : Integer.Sparse.eval row10110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck10110, Integer.Sparse.eval_collectBalanced, rawRowCheck10110]

def rawRow10111 : Integer.Sparse Key := [(key1130, -2), (key1236, -2), (key1125, -2), (key1130, -2), (key1236, -2), (key1044, -2), (key1233, -2), (key1038, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1159, 2), (key1243, 2), (key1152, 2), (key1159, 2), (key1243, 2), (key1009, 2), (key1233, 2), (key1003, 2), (key1116, 2), (key1152, 2), (key1003, 2), (key1116, 2)]

theorem rawRowCheck10111 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form7 = rawRow10111 := by decide +kernel

def row10111 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

theorem rowCheck10111 : row10111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10111 := by decide +kernel

theorem rowEval10111 (x : Key → ℝ) : Integer.Sparse.eval row10111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10111, Integer.Sparse.eval_collectBalanced, rawRowCheck10111]

end MUB6.Certificate.GramRows

end OAI

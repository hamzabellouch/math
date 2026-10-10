import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
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

def rawRow12032 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key984, -6), (key1098, -6), (key1183, -6), (key1183, -6)]

theorem rawRowCheck12032 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14 = rawRow12032 := by decide +kernel

def row12032 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12032 : row12032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12032 := by decide +kernel

theorem rowEval12032 (x : Key → ℝ) : Integer.Sparse.eval row12032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12032, Integer.Sparse.eval_collectBalanced, rawRowCheck12032]

def rawRow12033 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key984, -6), (key1183, -6), (key1098, -6), (key1183, -6)]

theorem rawRowCheck12033 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14 = rawRow12033 := by decide +kernel

def row12033 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12033 : row12033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12033 := by decide +kernel

theorem rowEval12033 (x : Key → ℝ) : Integer.Sparse.eval row12033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12033, Integer.Sparse.eval_collectBalanced, rawRowCheck12033]

def rawRow12034 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1090, 6), (key1169, 6), (key984, -6), (key1183, -6), (key1183, -6), (key1098, -6)]

theorem rawRowCheck12034 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14 = rawRow12034 := by decide +kernel

def row12034 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12034 : row12034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12034 := by decide +kernel

theorem rowEval12034 (x : Key → ℝ) : Integer.Sparse.eval row12034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12034, Integer.Sparse.eval_collectBalanced, rawRowCheck12034]

def rawRow12035 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1169, 6), (key1098, 6), (key1098, -6), (key984, -6), (key1183, -6), (key1183, -6)]

theorem rawRowCheck12035 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14 = rawRow12035 := by decide +kernel

def row12035 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12035 : row12035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12035 := by decide +kernel

theorem rowEval12035 (x : Key → ℝ) : Integer.Sparse.eval row12035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12035, Integer.Sparse.eval_collectBalanced, rawRowCheck12035]

def rawRow12036 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1090, 6), (key1098, 6), (key1098, -6), (key1183, -6), (key984, -6), (key1183, -6)]

theorem rawRowCheck12036 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14 = rawRow12036 := by decide +kernel

def row12036 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12036 : row12036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12036 := by decide +kernel

theorem rowEval12036 (x : Key → ℝ) : Integer.Sparse.eval row12036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12036, Integer.Sparse.eval_collectBalanced, rawRowCheck12036]

def rawRow12037 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1090, 6), (key1098, 6), (key1098, -6), (key1183, -6), (key1183, -6), (key984, -6)]

theorem rawRowCheck12037 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14 = rawRow12037 := by decide +kernel

def row12037 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12037 : row12037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12037 := by decide +kernel

theorem rowEval12037 (x : Key → ℝ) : Integer.Sparse.eval row12037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck12037, Integer.Sparse.eval_collectBalanced, rawRowCheck12037]

def rawRow12038 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1183, -6), (key984, -6), (key1098, -6), (key1183, -6)]

theorem rawRowCheck12038 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14 = rawRow12038 := by decide +kernel

def row12038 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12038 : row12038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12038 := by decide +kernel

theorem rowEval12038 (x : Key → ℝ) : Integer.Sparse.eval row12038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12038, Integer.Sparse.eval_collectBalanced, rawRowCheck12038]

def rawRow12039 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1169, 6), (key1090, 6), (key1183, -6), (key984, -6), (key1183, -6), (key1098, -6)]

theorem rawRowCheck12039 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14 = rawRow12039 := by decide +kernel

def row12039 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12039 : row12039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12039 := by decide +kernel

theorem rowEval12039 (x : Key → ℝ) : Integer.Sparse.eval row12039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12039, Integer.Sparse.eval_collectBalanced, rawRowCheck12039]

def rawRow12040 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1183, -6), (key1098, -6), (key984, -6), (key1183, -6)]

theorem rawRowCheck12040 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14 = rawRow12040 := by decide +kernel

def row12040 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12040 : row12040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12040 := by decide +kernel

theorem rowEval12040 (x : Key → ℝ) : Integer.Sparse.eval row12040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck12040, Integer.Sparse.eval_collectBalanced, rawRowCheck12040]

def rawRow12041 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1183, -6), (key1098, -6), (key1183, -6), (key984, -6)]

theorem rawRowCheck12041 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14 = rawRow12041 := by decide +kernel

def row12041 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12041 : row12041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12041 := by decide +kernel

theorem rowEval12041 (x : Key → ℝ) : Integer.Sparse.eval row12041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck12041, Integer.Sparse.eval_collectBalanced, rawRowCheck12041]

def rawRow12042 : Integer.Sparse Key := [(key1098, 6), (key1169, 6), (key1090, 6), (key1090, 6), (key1183, -6), (key1183, -6), (key984, -6), (key1098, -6)]

theorem rawRowCheck12042 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14 = rawRow12042 := by decide +kernel

def row12042 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12042 : row12042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12042 := by decide +kernel

theorem rowEval12042 (x : Key → ℝ) : Integer.Sparse.eval row12042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12042, Integer.Sparse.eval_collectBalanced, rawRowCheck12042]

def rawRow12043 : Integer.Sparse Key := [(key1169, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1183, -6), (key1183, -6), (key1098, -6), (key984, -6)]

theorem rawRowCheck12043 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14 = rawRow12043 := by decide +kernel

def row12043 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

theorem rowCheck12043 : row12043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12043 := by decide +kernel

theorem rowEval12043 (x : Key → ℝ) : Integer.Sparse.eval row12043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form14) x := by
  rw [rowCheck12043, Integer.Sparse.eval_collectBalanced, rawRowCheck12043]

def rawRow12044 : Integer.Sparse Key := [(key2361, -6), (key2361, -6), (key2364, -6), (key2364, -6), (key2456, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2520, 2)]

theorem rawRowCheck12044 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form15 = rawRow12044 := by decide +kernel

def row12044 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

theorem rowCheck12044 : row12044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12044 := by decide +kernel

theorem rowEval12044 (x : Key → ℝ) : Integer.Sparse.eval row12044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12044, Integer.Sparse.eval_collectBalanced, rawRowCheck12044]

def rawRow12045 : Integer.Sparse Key := [(key2361, -6), (key2364, -6), (key2361, -6), (key2364, -6), (key2456, 2), (key2459, 2), (key2456, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2520, 2), (key2459, 2), (key2520, 2)]

theorem rawRowCheck12045 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form15 = rawRow12045 := by decide +kernel

def row12045 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

theorem rowCheck12045 : row12045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12045 := by decide +kernel

theorem rowEval12045 (x : Key → ℝ) : Integer.Sparse.eval row12045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12045, Integer.Sparse.eval_collectBalanced, rawRowCheck12045]

def rawRow12046 : Integer.Sparse Key := [(key2364, -6), (key2361, -6), (key2361, -6), (key2364, -6), (key2459, 2), (key2456, 2), (key2456, 2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2520, 2), (key2520, 2), (key2459, 2)]

theorem rawRowCheck12046 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form15 = rawRow12046 := by decide +kernel

def row12046 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

theorem rowCheck12046 : row12046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12046 := by decide +kernel

theorem rowEval12046 (x : Key → ℝ) : Integer.Sparse.eval row12046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12046, Integer.Sparse.eval_collectBalanced, rawRowCheck12046]

def rawRow12047 : Integer.Sparse Key := [(key2361, -6), (key2364, -6), (key2364, -6), (key2361, -6), (key2517, 2), (key2520, 2), (key2520, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2456, 2), (key2456, 2), (key2517, 2)]

theorem rawRowCheck12047 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form15 = rawRow12047 := by decide +kernel

def row12047 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

theorem rowCheck12047 : row12047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12047 := by decide +kernel

theorem rowEval12047 (x : Key → ℝ) : Integer.Sparse.eval row12047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12047, Integer.Sparse.eval_collectBalanced, rawRowCheck12047]

def rawRow12048 : Integer.Sparse Key := [(key2364, -6), (key2361, -6), (key2364, -6), (key2361, -6), (key2520, 2), (key2517, 2), (key2520, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2456, 2), (key2517, 2), (key2456, 2)]

theorem rawRowCheck12048 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form15 = rawRow12048 := by decide +kernel

def row12048 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

theorem rowCheck12048 : row12048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12048 := by decide +kernel

theorem rowEval12048 (x : Key → ℝ) : Integer.Sparse.eval row12048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12048, Integer.Sparse.eval_collectBalanced, rawRowCheck12048]

def rawRow12049 : Integer.Sparse Key := [(key2364, -6), (key2364, -6), (key2361, -6), (key2361, -6), (key2520, 2), (key2520, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2456, 2)]

theorem rawRowCheck12049 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form15 = rawRow12049 := by decide +kernel

def row12049 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

theorem rowCheck12049 : row12049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12049 := by decide +kernel

theorem rowEval12049 (x : Key → ℝ) : Integer.Sparse.eval row12049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12049, Integer.Sparse.eval_collectBalanced, rawRowCheck12049]

def rawRow12050 : Integer.Sparse Key := [(key2456, -6), (key2456, -6), (key2459, -6), (key2531, -6), (key2361, 2), (key2361, 2), (key2364, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2561, 2)]

theorem rawRowCheck12050 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15 = rawRow12050 := by decide +kernel

def row12050 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12050 : row12050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12050 := by decide +kernel

theorem rowEval12050 (x : Key → ℝ) : Integer.Sparse.eval row12050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12050, Integer.Sparse.eval_collectBalanced, rawRowCheck12050]

def rawRow12051 : Integer.Sparse Key := [(key2456, -6), (key2459, -6), (key2456, -6), (key2531, -6), (key2361, 2), (key2364, 2), (key2361, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2561, 2), (key2531, 2), (key2561, 2)]

theorem rawRowCheck12051 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15 = rawRow12051 := by decide +kernel

def row12051 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12051 : row12051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12051 := by decide +kernel

theorem rowEval12051 (x : Key → ℝ) : Integer.Sparse.eval row12051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12051, Integer.Sparse.eval_collectBalanced, rawRowCheck12051]

def rawRow12052 : Integer.Sparse Key := [(key2459, -6), (key2456, -6), (key2456, -6), (key2531, -6), (key2364, 2), (key2361, 2), (key2361, 2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2561, 2), (key2561, 2), (key2531, 2)]

theorem rawRowCheck12052 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15 = rawRow12052 := by decide +kernel

def row12052 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12052 : row12052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12052 := by decide +kernel

theorem rowEval12052 (x : Key → ℝ) : Integer.Sparse.eval row12052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12052, Integer.Sparse.eval_collectBalanced, rawRowCheck12052]

def rawRow12053 : Integer.Sparse Key := [(key2456, -6), (key2456, -6), (key2531, -6), (key2459, -6), (key2456, 2), (key2456, 2), (key2531, 2), (key2361, 2), (key2361, 2), (key2517, 2), (key2517, 2), (key2561, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2520, 2)]

theorem rawRowCheck12053 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15 = rawRow12053 := by decide +kernel

def row12053 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12053 : row12053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12053 := by decide +kernel

theorem rowEval12053 (x : Key → ℝ) : Integer.Sparse.eval row12053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12053, Integer.Sparse.eval_collectBalanced, rawRowCheck12053]

def rawRow12054 : Integer.Sparse Key := [(key2456, -6), (key2531, -6), (key2456, -6), (key2459, -6), (key2456, 2), (key2531, 2), (key2456, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2561, 2), (key2361, 2), (key2517, 2), (key2520, 2), (key2364, 2), (key2520, 2)]

theorem rawRowCheck12054 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15 = rawRow12054 := by decide +kernel

def row12054 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12054 : row12054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12054 := by decide +kernel

theorem rowEval12054 (x : Key → ℝ) : Integer.Sparse.eval row12054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12054, Integer.Sparse.eval_collectBalanced, rawRowCheck12054]

def rawRow12055 : Integer.Sparse Key := [(key2531, -6), (key2456, -6), (key2456, -6), (key2459, -6), (key2531, 2), (key2456, 2), (key2456, 2), (key2561, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2517, 2), (key2361, 2), (key2520, 2), (key2520, 2), (key2364, 2)]

theorem rawRowCheck12055 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15 = rawRow12055 := by decide +kernel

def row12055 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12055 : row12055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12055 := by decide +kernel

theorem rowEval12055 (x : Key → ℝ) : Integer.Sparse.eval row12055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck12055, Integer.Sparse.eval_collectBalanced, rawRowCheck12055]

def rawRow12056 : Integer.Sparse Key := [(key2456, -6), (key2459, -6), (key2531, -6), (key2456, -6), (key2517, 2), (key2520, 2), (key2561, 2), (key2361, 2), (key2364, 2), (key2456, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2361, 2), (key2456, 2), (key2517, 2)]

theorem rawRowCheck12056 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15 = rawRow12056 := by decide +kernel

def row12056 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12056 : row12056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12056 := by decide +kernel

theorem rowEval12056 (x : Key → ℝ) : Integer.Sparse.eval row12056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12056, Integer.Sparse.eval_collectBalanced, rawRowCheck12056]

def rawRow12057 : Integer.Sparse Key := [(key2459, -6), (key2456, -6), (key2531, -6), (key2456, -6), (key2520, 2), (key2517, 2), (key2561, 2), (key2364, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2531, 2), (key2361, 2), (key2517, 2), (key2456, 2)]

theorem rawRowCheck12057 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15 = rawRow12057 := by decide +kernel

def row12057 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12057 : row12057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12057 := by decide +kernel

theorem rowEval12057 (x : Key → ℝ) : Integer.Sparse.eval row12057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12057, Integer.Sparse.eval_collectBalanced, rawRowCheck12057]

def rawRow12058 : Integer.Sparse Key := [(key2456, -6), (key2531, -6), (key2459, -6), (key2456, -6), (key2517, 2), (key2561, 2), (key2520, 2), (key2456, 2), (key2531, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2456, 2), (key2361, 2), (key2517, 2)]

theorem rawRowCheck12058 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15 = rawRow12058 := by decide +kernel

def row12058 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12058 : row12058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12058 := by decide +kernel

theorem rowEval12058 (x : Key → ℝ) : Integer.Sparse.eval row12058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form15) x := by
  rw [rowCheck12058, Integer.Sparse.eval_collectBalanced, rawRowCheck12058]

def rawRow12059 : Integer.Sparse Key := [(key2531, -6), (key2456, -6), (key2459, -6), (key2456, -6), (key2561, 2), (key2517, 2), (key2520, 2), (key2531, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2364, 2), (key2456, 2), (key2517, 2), (key2361, 2)]

theorem rawRowCheck12059 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15 = rawRow12059 := by decide +kernel

def row12059 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12059 : row12059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12059 := by decide +kernel

theorem rowEval12059 (x : Key → ℝ) : Integer.Sparse.eval row12059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck12059, Integer.Sparse.eval_collectBalanced, rawRowCheck12059]

def rawRow12060 : Integer.Sparse Key := [(key2459, -6), (key2531, -6), (key2456, -6), (key2456, -6), (key2520, 2), (key2561, 2), (key2517, 2), (key2520, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2361, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2456, 2)]

theorem rawRowCheck12060 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15 = rawRow12060 := by decide +kernel

def row12060 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12060 : row12060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12060 := by decide +kernel

theorem rowEval12060 (x : Key → ℝ) : Integer.Sparse.eval row12060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12060, Integer.Sparse.eval_collectBalanced, rawRowCheck12060]

def rawRow12061 : Integer.Sparse Key := [(key2531, -6), (key2459, -6), (key2456, -6), (key2456, -6), (key2561, 2), (key2520, 2), (key2517, 2), (key2561, 2), (key2520, 2), (key2531, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2517, 2), (key2456, 2), (key2361, 2)]

theorem rawRowCheck12061 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15 = rawRow12061 := by decide +kernel

def row12061 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

theorem rowCheck12061 : row12061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12061 := by decide +kernel

theorem rowEval12061 (x : Key → ℝ) : Integer.Sparse.eval row12061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form15) x := by
  rw [rowCheck12061, Integer.Sparse.eval_collectBalanced, rawRowCheck12061]

def rawRow12062 : Integer.Sparse Key := [(key2377, -6), (key2377, -6), (key2389, -6), (key2389, -6), (key2405, 6), (key2405, 6), (key2436, 6), (key2436, 6)]

theorem rawRowCheck12062 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form16 = rawRow12062 := by decide +kernel

def row12062 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

theorem rowCheck12062 : row12062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12062 := by decide +kernel

theorem rowEval12062 (x : Key → ℝ) : Integer.Sparse.eval row12062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12062, Integer.Sparse.eval_collectBalanced, rawRowCheck12062]

def rawRow12063 : Integer.Sparse Key := [(key2377, -6), (key2389, -6), (key2377, -6), (key2389, -6), (key2405, 6), (key2436, 6), (key2405, 6), (key2436, 6)]

theorem rawRowCheck12063 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form16 = rawRow12063 := by decide +kernel

def row12063 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

theorem rowCheck12063 : row12063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12063 := by decide +kernel

theorem rowEval12063 (x : Key → ℝ) : Integer.Sparse.eval row12063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12063, Integer.Sparse.eval_collectBalanced, rawRowCheck12063]

def rawRow12064 : Integer.Sparse Key := [(key2377, -6), (key2389, -6), (key2389, -6), (key2377, -6), (key2405, 6), (key2436, 6), (key2436, 6), (key2405, 6)]

theorem rawRowCheck12064 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form16 = rawRow12064 := by decide +kernel

def row12064 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

theorem rowCheck12064 : row12064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12064 := by decide +kernel

theorem rowEval12064 (x : Key → ℝ) : Integer.Sparse.eval row12064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12064, Integer.Sparse.eval_collectBalanced, rawRowCheck12064]

def rawRow12065 : Integer.Sparse Key := [(key2389, -6), (key2377, -6), (key2377, -6), (key2389, -6), (key2436, 6), (key2405, 6), (key2405, 6), (key2436, 6)]

theorem rawRowCheck12065 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form16 = rawRow12065 := by decide +kernel

def row12065 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

theorem rowCheck12065 : row12065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12065 := by decide +kernel

theorem rowEval12065 (x : Key → ℝ) : Integer.Sparse.eval row12065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12065, Integer.Sparse.eval_collectBalanced, rawRowCheck12065]

def rawRow12066 : Integer.Sparse Key := [(key2389, -6), (key2377, -6), (key2389, -6), (key2377, -6), (key2436, 6), (key2405, 6), (key2436, 6), (key2405, 6)]

theorem rawRowCheck12066 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form16 = rawRow12066 := by decide +kernel

def row12066 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

theorem rowCheck12066 : row12066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12066 := by decide +kernel

theorem rowEval12066 (x : Key → ℝ) : Integer.Sparse.eval row12066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12066, Integer.Sparse.eval_collectBalanced, rawRowCheck12066]

def rawRow12067 : Integer.Sparse Key := [(key2389, -6), (key2389, -6), (key2377, -6), (key2377, -6), (key2436, 6), (key2436, 6), (key2405, 6), (key2405, 6)]

theorem rawRowCheck12067 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form16 = rawRow12067 := by decide +kernel

def row12067 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

theorem rowCheck12067 : row12067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12067 := by decide +kernel

theorem rowEval12067 (x : Key → ℝ) : Integer.Sparse.eval row12067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12067, Integer.Sparse.eval_collectBalanced, rawRowCheck12067]

def rawRow12068 : Integer.Sparse Key := [(key2405, -6), (key2471, -6), (key2479, -6), (key2479, -6), (key2377, 6), (key2471, 6), (key2502, 6), (key2502, 6)]

theorem rawRowCheck12068 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16 = rawRow12068 := by decide +kernel

def row12068 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12068 : row12068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12068 := by decide +kernel

theorem rowEval12068 (x : Key → ℝ) : Integer.Sparse.eval row12068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12068, Integer.Sparse.eval_collectBalanced, rawRowCheck12068]

def rawRow12069 : Integer.Sparse Key := [(key2405, -6), (key2479, -6), (key2471, -6), (key2479, -6), (key2377, 6), (key2502, 6), (key2471, 6), (key2502, 6)]

theorem rawRowCheck12069 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16 = rawRow12069 := by decide +kernel

def row12069 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12069 : row12069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12069 := by decide +kernel

theorem rowEval12069 (x : Key → ℝ) : Integer.Sparse.eval row12069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12069, Integer.Sparse.eval_collectBalanced, rawRowCheck12069]

def rawRow12070 : Integer.Sparse Key := [(key2405, -6), (key2479, -6), (key2479, -6), (key2471, -6), (key2377, 6), (key2502, 6), (key2502, 6), (key2471, 6)]

theorem rawRowCheck12070 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16 = rawRow12070 := by decide +kernel

def row12070 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12070 : row12070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12070 := by decide +kernel

theorem rowEval12070 (x : Key → ℝ) : Integer.Sparse.eval row12070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12070, Integer.Sparse.eval_collectBalanced, rawRowCheck12070]

def rawRow12071 : Integer.Sparse Key := [(key2471, -6), (key2405, -6), (key2479, -6), (key2479, -6), (key2471, 6), (key2377, 6), (key2502, 6), (key2502, 6)]

theorem rawRowCheck12071 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16 = rawRow12071 := by decide +kernel

def row12071 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12071 : row12071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12071 := by decide +kernel

theorem rowEval12071 (x : Key → ℝ) : Integer.Sparse.eval row12071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12071, Integer.Sparse.eval_collectBalanced, rawRowCheck12071]

def rawRow12072 : Integer.Sparse Key := [(key2471, -6), (key2479, -6), (key2405, -6), (key2479, -6), (key2471, 6), (key2502, 6), (key2377, 6), (key2502, 6)]

theorem rawRowCheck12072 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16 = rawRow12072 := by decide +kernel

def row12072 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12072 : row12072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12072 := by decide +kernel

theorem rowEval12072 (x : Key → ℝ) : Integer.Sparse.eval row12072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12072, Integer.Sparse.eval_collectBalanced, rawRowCheck12072]

def rawRow12073 : Integer.Sparse Key := [(key2471, -6), (key2479, -6), (key2479, -6), (key2405, -6), (key2471, 6), (key2502, 6), (key2502, 6), (key2377, 6)]

theorem rawRowCheck12073 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16 = rawRow12073 := by decide +kernel

def row12073 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12073 : row12073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12073 := by decide +kernel

theorem rowEval12073 (x : Key → ℝ) : Integer.Sparse.eval row12073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck12073, Integer.Sparse.eval_collectBalanced, rawRowCheck12073]

def rawRow12074 : Integer.Sparse Key := [(key2479, -6), (key2405, -6), (key2471, -6), (key2479, -6), (key2502, 6), (key2377, 6), (key2471, 6), (key2502, 6)]

theorem rawRowCheck12074 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16 = rawRow12074 := by decide +kernel

def row12074 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12074 : row12074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12074 := by decide +kernel

theorem rowEval12074 (x : Key → ℝ) : Integer.Sparse.eval row12074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12074, Integer.Sparse.eval_collectBalanced, rawRowCheck12074]

def rawRow12075 : Integer.Sparse Key := [(key2479, -6), (key2405, -6), (key2479, -6), (key2471, -6), (key2502, 6), (key2377, 6), (key2502, 6), (key2471, 6)]

theorem rawRowCheck12075 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16 = rawRow12075 := by decide +kernel

def row12075 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12075 : row12075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12075 := by decide +kernel

theorem rowEval12075 (x : Key → ℝ) : Integer.Sparse.eval row12075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12075, Integer.Sparse.eval_collectBalanced, rawRowCheck12075]

def rawRow12076 : Integer.Sparse Key := [(key2479, -6), (key2471, -6), (key2405, -6), (key2479, -6), (key2502, 6), (key2471, 6), (key2377, 6), (key2502, 6)]

theorem rawRowCheck12076 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16 = rawRow12076 := by decide +kernel

def row12076 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12076 : row12076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12076 := by decide +kernel

theorem rowEval12076 (x : Key → ℝ) : Integer.Sparse.eval row12076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12076, Integer.Sparse.eval_collectBalanced, rawRowCheck12076]

def rawRow12077 : Integer.Sparse Key := [(key2479, -6), (key2471, -6), (key2479, -6), (key2405, -6), (key2502, 6), (key2471, 6), (key2502, 6), (key2377, 6)]

theorem rawRowCheck12077 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16 = rawRow12077 := by decide +kernel

def row12077 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12077 : row12077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12077 := by decide +kernel

theorem rowEval12077 (x : Key → ℝ) : Integer.Sparse.eval row12077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck12077, Integer.Sparse.eval_collectBalanced, rawRowCheck12077]

def rawRow12078 : Integer.Sparse Key := [(key2479, -6), (key2479, -6), (key2405, -6), (key2471, -6), (key2502, 6), (key2502, 6), (key2377, 6), (key2471, 6)]

theorem rawRowCheck12078 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16 = rawRow12078 := by decide +kernel

def row12078 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12078 : row12078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12078 := by decide +kernel

theorem rowEval12078 (x : Key → ℝ) : Integer.Sparse.eval row12078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12078, Integer.Sparse.eval_collectBalanced, rawRowCheck12078]

def rawRow12079 : Integer.Sparse Key := [(key2479, -6), (key2479, -6), (key2471, -6), (key2405, -6), (key2502, 6), (key2502, 6), (key2471, 6), (key2377, 6)]

theorem rawRowCheck12079 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16 = rawRow12079 := by decide +kernel

def row12079 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

theorem rowCheck12079 : row12079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12079 := by decide +kernel

theorem rowEval12079 (x : Key → ℝ) : Integer.Sparse.eval row12079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form16) x := by
  rw [rowCheck12079, Integer.Sparse.eval_collectBalanced, rawRowCheck12079]

def rawRow12080 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2441, -2), (key2410, -2), (key2410, -2), (key2441, -2), (key2441, -2), (key2445, -2), (key2445, -2), (key2473, 2), (key2483, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2507, 2), (key2483, 2), (key2483, 2), (key2507, 2), (key2507, 2), (key2526, 2), (key2526, 2)]

theorem rawRowCheck12080 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form17 = rawRow12080 := by decide +kernel

def row12080 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

theorem rowCheck12080 : row12080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12080 := by decide +kernel

theorem rowEval12080 (x : Key → ℝ) : Integer.Sparse.eval row12080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12080, Integer.Sparse.eval_collectBalanced, rawRowCheck12080]

def rawRow12081 : Integer.Sparse Key := [(key2410, -2), (key2407, -2), (key2410, -2), (key2441, -2), (key2407, -2), (key2441, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2445, -2), (key2410, -2), (key2441, -2), (key2483, 2), (key2473, 2), (key2483, 2), (key2507, 2), (key2473, 2), (key2507, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2526, 2), (key2483, 2), (key2507, 2)]

theorem rawRowCheck12081 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form17 = rawRow12081 := by decide +kernel

def row12081 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

theorem rowCheck12081 : row12081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12081 := by decide +kernel

theorem rowEval12081 (x : Key → ℝ) : Integer.Sparse.eval row12081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12081, Integer.Sparse.eval_collectBalanced, rawRowCheck12081]

def rawRow12082 : Integer.Sparse Key := [(key2410, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2441, -2), (key2407, -2), (key2445, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2441, -2), (key2410, -2), (key2483, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2507, 2), (key2473, 2), (key2526, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2507, 2), (key2483, 2)]

theorem rawRowCheck12082 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form17 = rawRow12082 := by decide +kernel

def row12082 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

theorem rowCheck12082 : row12082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12082 := by decide +kernel

theorem rowEval12082 (x : Key → ℝ) : Integer.Sparse.eval row12082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12082, Integer.Sparse.eval_collectBalanced, rawRowCheck12082]

def rawRow12083 : Integer.Sparse Key := [(key2441, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2410, -2), (key2445, -2), (key2407, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2410, -2), (key2441, -2), (key2507, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2483, 2), (key2526, 2), (key2473, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2483, 2), (key2507, 2)]

theorem rawRowCheck12083 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form17 = rawRow12083 := by decide +kernel

def row12083 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

theorem rowCheck12083 : row12083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12083 := by decide +kernel

theorem rowEval12083 (x : Key → ℝ) : Integer.Sparse.eval row12083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12083, Integer.Sparse.eval_collectBalanced, rawRowCheck12083]

def rawRow12084 : Integer.Sparse Key := [(key2441, -2), (key2445, -2), (key2441, -2), (key2410, -2), (key2445, -2), (key2410, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2407, -2), (key2441, -2), (key2410, -2), (key2507, 2), (key2526, 2), (key2507, 2), (key2483, 2), (key2526, 2), (key2483, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2473, 2), (key2507, 2), (key2483, 2)]

theorem rawRowCheck12084 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form17 = rawRow12084 := by decide +kernel

def row12084 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

theorem rowCheck12084 : row12084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12084 := by decide +kernel

theorem rowEval12084 (x : Key → ℝ) : Integer.Sparse.eval row12084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12084, Integer.Sparse.eval_collectBalanced, rawRowCheck12084]

def rawRow12085 : Integer.Sparse Key := [(key2445, -2), (key2441, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2410, -2), (key2441, -2), (key2441, -2), (key2410, -2), (key2410, -2), (key2407, -2), (key2407, -2), (key2526, 2), (key2507, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2483, 2), (key2507, 2), (key2507, 2), (key2483, 2), (key2483, 2), (key2473, 2), (key2473, 2)]

theorem rawRowCheck12085 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form17 = rawRow12085 := by decide +kernel

def row12085 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

theorem rowCheck12085 : row12085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12085 := by decide +kernel

theorem rowEval12085 (x : Key → ℝ) : Integer.Sparse.eval row12085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12085, Integer.Sparse.eval_collectBalanced, rawRowCheck12085]

def rawRow12086 : Integer.Sparse Key := [(key2592, -2), (key2595, -2), (key2595, -2), (key2848, -2), (key2970, -2), (key2970, -2), (key2882, -2), (key2882, -2), (key2991, -2), (key2991, -2), (key2993, -2), (key2993, -2), (key2379, 2), (key2393, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2441, 2), (key2544, 2), (key2544, 2), (key2555, 2), (key2555, 2), (key2565, 2), (key2565, 2)]

theorem rawRowCheck12086 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17 = rawRow12086 := by decide +kernel

def row12086 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, -2), (key2595, -4), (key2848, -2), (key2882, -4), (key2970, -4), (key2991, -4), (key2993, -4)]

theorem rowCheck12086 : row12086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12086 := by decide +kernel

theorem rowEval12086 (x : Key → ℝ) : Integer.Sparse.eval row12086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12086, Integer.Sparse.eval_collectBalanced, rawRowCheck12086]

def rawRow12087 : Integer.Sparse Key := [(key2595, -2), (key2592, -2), (key2595, -2), (key2970, -2), (key2848, -2), (key2970, -2), (key2991, -2), (key2993, -2), (key2882, -2), (key2993, -2), (key2882, -2), (key2991, -2), (key2393, 2), (key2379, 2), (key2393, 2), (key2441, 2), (key2407, 2), (key2441, 2), (key2555, 2), (key2565, 2), (key2544, 2), (key2565, 2), (key2544, 2), (key2555, 2)]

theorem rawRowCheck12087 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17 = rawRow12087 := by decide +kernel

def row12087 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, -2), (key2595, -4), (key2848, -2), (key2882, -4), (key2970, -4), (key2991, -4), (key2993, -4)]

theorem rowCheck12087 : row12087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12087 := by decide +kernel

theorem rowEval12087 (x : Key → ℝ) : Integer.Sparse.eval row12087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12087, Integer.Sparse.eval_collectBalanced, rawRowCheck12087]

def rawRow12088 : Integer.Sparse Key := [(key2595, -2), (key2595, -2), (key2592, -2), (key2970, -2), (key2970, -2), (key2848, -2), (key2993, -2), (key2991, -2), (key2993, -2), (key2882, -2), (key2991, -2), (key2882, -2), (key2393, 2), (key2393, 2), (key2379, 2), (key2441, 2), (key2441, 2), (key2407, 2), (key2565, 2), (key2555, 2), (key2565, 2), (key2544, 2), (key2555, 2), (key2544, 2)]

theorem rawRowCheck12088 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17 = rawRow12088 := by decide +kernel

def row12088 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, -2), (key2595, -4), (key2848, -2), (key2882, -4), (key2970, -4), (key2991, -4), (key2993, -4)]

theorem rowCheck12088 : row12088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12088 := by decide +kernel

theorem rowEval12088 (x : Key → ℝ) : Integer.Sparse.eval row12088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12088, Integer.Sparse.eval_collectBalanced, rawRowCheck12088]

def rawRow12089 : Integer.Sparse Key := [(key2848, -2), (key2882, -2), (key2882, -2), (key2592, -2), (key2991, -2), (key2991, -2), (key2595, -2), (key2595, -2), (key2970, -2), (key2970, -2), (key2993, -2), (key2993, -2), (key2771, 2), (key2912, 2), (key2912, 2), (key2592, 2), (key2991, 2), (key2991, 2), (key2393, 2), (key2393, 2), (key2441, 2), (key2441, 2), (key2565, 2), (key2565, 2)]

theorem rawRowCheck12089 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17 = rawRow12089 := by decide +kernel

def row12089 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2595, -4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2970, -4), (key2993, -4)]

theorem rowCheck12089 : row12089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12089 := by decide +kernel

theorem rowEval12089 (x : Key → ℝ) : Integer.Sparse.eval row12089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12089, Integer.Sparse.eval_collectBalanced, rawRowCheck12089]

def rawRow12090 : Integer.Sparse Key := [(key2882, -2), (key2848, -2), (key2882, -2), (key2991, -2), (key2592, -2), (key2991, -2), (key2970, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2970, -2), (key2912, 2), (key2771, 2), (key2912, 2), (key2991, 2), (key2592, 2), (key2991, 2), (key2441, 2), (key2565, 2), (key2393, 2), (key2565, 2), (key2393, 2), (key2441, 2)]

theorem rawRowCheck12090 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17 = rawRow12090 := by decide +kernel

def row12090 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2595, -4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2970, -4), (key2993, -4)]

theorem rowCheck12090 : row12090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12090 := by decide +kernel

theorem rowEval12090 (x : Key → ℝ) : Integer.Sparse.eval row12090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12090, Integer.Sparse.eval_collectBalanced, rawRowCheck12090]

def rawRow12091 : Integer.Sparse Key := [(key2882, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2991, -2), (key2592, -2), (key2993, -2), (key2970, -2), (key2993, -2), (key2595, -2), (key2970, -2), (key2595, -2), (key2912, 2), (key2912, 2), (key2771, 2), (key2991, 2), (key2991, 2), (key2592, 2), (key2565, 2), (key2441, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2393, 2)]

theorem rawRowCheck12091 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17 = rawRow12091 := by decide +kernel

def row12091 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2595, -4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2970, -4), (key2993, -4)]

theorem rowCheck12091 : row12091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12091 := by decide +kernel

theorem rowEval12091 (x : Key → ℝ) : Integer.Sparse.eval row12091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck12091, Integer.Sparse.eval_collectBalanced, rawRowCheck12091]

def rawRow12092 : Integer.Sparse Key := [(key2970, -2), (key2991, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2993, -2), (key2592, -2), (key2595, -2), (key2848, -2), (key2970, -2), (key2882, -2), (key2991, -2), (key2933, 2), (key2991, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key3003, 2), (key2379, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2544, 2), (key2555, 2)]

theorem rawRowCheck12092 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17 = rawRow12092 := by decide +kernel

def row12092 : Integer.Sparse Key := [(key2379, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2544, 2), (key2555, 2), (key2592, -2), (key2595, -4), (key2602, 2), (key2848, -2), (key2882, -4), (key2912, 2), (key2933, 2), (key2970, -4), (key2991, -2), (key2993, -4), (key3003, 4)]

theorem rowCheck12092 : row12092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12092 := by decide +kernel

theorem rowEval12092 (x : Key → ℝ) : Integer.Sparse.eval row12092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12092, Integer.Sparse.eval_collectBalanced, rawRowCheck12092]

def rawRow12093 : Integer.Sparse Key := [(key2970, -2), (key2993, -2), (key2991, -2), (key2595, -2), (key2993, -2), (key2882, -2), (key2595, -2), (key2592, -2), (key2970, -2), (key2848, -2), (key2991, -2), (key2882, -2), (key2933, 2), (key3003, 2), (key2991, 2), (key2602, 2), (key3003, 2), (key2912, 2), (key2393, 2), (key2379, 2), (key2441, 2), (key2407, 2), (key2555, 2), (key2544, 2)]

theorem rawRowCheck12093 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17 = rawRow12093 := by decide +kernel

def row12093 : Integer.Sparse Key := [(key2379, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2544, 2), (key2555, 2), (key2592, -2), (key2595, -4), (key2602, 2), (key2848, -2), (key2882, -4), (key2912, 2), (key2933, 2), (key2970, -4), (key2991, -2), (key2993, -4), (key3003, 4)]

theorem rowCheck12093 : row12093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12093 := by decide +kernel

theorem rowEval12093 (x : Key → ℝ) : Integer.Sparse.eval row12093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12093, Integer.Sparse.eval_collectBalanced, rawRowCheck12093]

def rawRow12094 : Integer.Sparse Key := [(key2991, -2), (key2970, -2), (key2993, -2), (key2882, -2), (key2595, -2), (key2993, -2), (key2848, -2), (key2882, -2), (key2592, -2), (key2991, -2), (key2595, -2), (key2970, -2), (key2991, 2), (key2933, 2), (key3003, 2), (key2912, 2), (key2602, 2), (key3003, 2), (key2771, 2), (key2912, 2), (key2592, 2), (key2991, 2), (key2393, 2), (key2441, 2)]

theorem rawRowCheck12094 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17 = rawRow12094 := by decide +kernel

def row12094 : Integer.Sparse Key := [(key2393, 2), (key2441, 2), (key2595, -4), (key2602, 2), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 2), (key2970, -4), (key2993, -4), (key3003, 4)]

theorem rowCheck12094 : row12094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12094 := by decide +kernel

theorem rowEval12094 (x : Key → ℝ) : Integer.Sparse.eval row12094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12094, Integer.Sparse.eval_collectBalanced, rawRowCheck12094]

def rawRow12095 : Integer.Sparse Key := [(key2991, -2), (key2993, -2), (key2970, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2592, -2), (key2970, -2), (key2595, -2), (key2991, 2), (key3003, 2), (key2933, 2), (key2912, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2771, 2), (key2991, 2), (key2592, 2), (key2441, 2), (key2393, 2)]

theorem rawRowCheck12095 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17 = rawRow12095 := by decide +kernel

def row12095 : Integer.Sparse Key := [(key2393, 2), (key2441, 2), (key2595, -4), (key2602, 2), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 2), (key2970, -4), (key2993, -4), (key3003, 4)]

theorem rowCheck12095 : row12095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12095 := by decide +kernel

theorem rowEval12095 (x : Key → ℝ) : Integer.Sparse.eval row12095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck12095, Integer.Sparse.eval_collectBalanced, rawRowCheck12095]

def rawRow12096 : Integer.Sparse Key := [(key2993, -2), (key2970, -2), (key2991, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2970, -2), (key2991, -2), (key2595, -2), (key2882, -2), (key2592, -2), (key2848, -2), (key3003, 2), (key2933, 2), (key2991, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2933, 2), (key2991, 2), (key2602, 2), (key2912, 2), (key2379, 2), (key2407, 2)]

theorem rawRowCheck12096 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17 = rawRow12096 := by decide +kernel

def row12096 : Integer.Sparse Key := [(key2379, 2), (key2407, 2), (key2592, -2), (key2595, -4), (key2602, 4), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 4), (key2970, -4), (key2993, -4), (key3003, 4)]

theorem rowCheck12096 : row12096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12096 := by decide +kernel

theorem rowEval12096 (x : Key → ℝ) : Integer.Sparse.eval row12096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12096, Integer.Sparse.eval_collectBalanced, rawRowCheck12096]

def rawRow12097 : Integer.Sparse Key := [(key2993, -2), (key2991, -2), (key2970, -2), (key2993, -2), (key2882, -2), (key2595, -2), (key2991, -2), (key2970, -2), (key2882, -2), (key2595, -2), (key2848, -2), (key2592, -2), (key3003, 2), (key2991, 2), (key2933, 2), (key3003, 2), (key2912, 2), (key2602, 2), (key2991, 2), (key2933, 2), (key2912, 2), (key2602, 2), (key2771, 2), (key2592, 2)]

theorem rawRowCheck12097 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17 = rawRow12097 := by decide +kernel

def row12097 : Integer.Sparse Key := [(key2595, -4), (key2602, 4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 4), (key2970, -4), (key2993, -4), (key3003, 4)]

theorem rowCheck12097 : row12097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12097 := by decide +kernel

theorem rowEval12097 (x : Key → ℝ) : Integer.Sparse.eval row12097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form17) x := by
  rw [rowCheck12097, Integer.Sparse.eval_collectBalanced, rawRowCheck12097]

def rawRow12098 : Integer.Sparse Key := [(key1096, 2), (key1100, 2), (key1100, 2), (key1096, 2), (key1185, 2), (key1185, 2), (key1100, 2), (key1100, 2), (key1185, 2), (key1185, 2), (key1186, 2), (key1186, 2), (key1171, -2), (key1171, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1222, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1224, -2)]

theorem rawRowCheck12098 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form18 = rawRow12098 := by decide +kernel

def row12098 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

theorem rowCheck12098 : row12098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12098 := by decide +kernel

theorem rowEval12098 (x : Key → ℝ) : Integer.Sparse.eval row12098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12098, Integer.Sparse.eval_collectBalanced, rawRowCheck12098]

def rawRow12099 : Integer.Sparse Key := [(key1100, 2), (key1096, 2), (key1100, 2), (key1185, 2), (key1096, 2), (key1185, 2), (key1185, 2), (key1186, 2), (key1100, 2), (key1186, 2), (key1100, 2), (key1185, 2), (key1171, -2), (key1175, -2), (key1171, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1224, -2), (key1175, -2), (key1224, -2)]

theorem rawRowCheck12099 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form18 = rawRow12099 := by decide +kernel

def row12099 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

theorem rowCheck12099 : row12099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12099 := by decide +kernel

theorem rowEval12099 (x : Key → ℝ) : Integer.Sparse.eval row12099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12099, Integer.Sparse.eval_collectBalanced, rawRowCheck12099]

def rawRow12100 : Integer.Sparse Key := [(key1100, 2), (key1100, 2), (key1096, 2), (key1185, 2), (key1185, 2), (key1096, 2), (key1186, 2), (key1185, 2), (key1186, 2), (key1100, 2), (key1185, 2), (key1100, 2), (key1175, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1224, -2), (key1224, -2), (key1175, -2)]

theorem rawRowCheck12100 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form18 = rawRow12100 := by decide +kernel

def row12100 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

theorem rowCheck12100 : row12100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12100 := by decide +kernel

theorem rowEval12100 (x : Key → ℝ) : Integer.Sparse.eval row12100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12100, Integer.Sparse.eval_collectBalanced, rawRowCheck12100]

def rawRow12101 : Integer.Sparse Key := [(key1185, 2), (key1185, 2), (key1186, 2), (key1100, 2), (key1100, 2), (key1186, 2), (key1096, 2), (key1100, 2), (key1096, 2), (key1185, 2), (key1100, 2), (key1185, 2), (key1222, -2), (key1224, -2), (key1224, -2), (key1171, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1171, -2), (key1171, -2), (key1222, -2)]

theorem rawRowCheck12101 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form18 = rawRow12101 := by decide +kernel

def row12101 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

theorem rowCheck12101 : row12101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12101 := by decide +kernel

theorem rowEval12101 (x : Key → ℝ) : Integer.Sparse.eval row12101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12101, Integer.Sparse.eval_collectBalanced, rawRowCheck12101]

def rawRow12102 : Integer.Sparse Key := [(key1185, 2), (key1186, 2), (key1185, 2), (key1100, 2), (key1186, 2), (key1100, 2), (key1100, 2), (key1096, 2), (key1185, 2), (key1096, 2), (key1185, 2), (key1100, 2), (key1224, -2), (key1222, -2), (key1224, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1171, -2), (key1222, -2), (key1171, -2)]

theorem rawRowCheck12102 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form18 = rawRow12102 := by decide +kernel

def row12102 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

theorem rowCheck12102 : row12102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12102 := by decide +kernel

theorem rowEval12102 (x : Key → ℝ) : Integer.Sparse.eval row12102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12102, Integer.Sparse.eval_collectBalanced, rawRowCheck12102]

def rawRow12103 : Integer.Sparse Key := [(key1186, 2), (key1185, 2), (key1185, 2), (key1186, 2), (key1100, 2), (key1100, 2), (key1185, 2), (key1185, 2), (key1100, 2), (key1100, 2), (key1096, 2), (key1096, 2), (key1224, -2), (key1224, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1175, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1171, -2)]

theorem rawRowCheck12103 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form18 = rawRow12103 := by decide +kernel

def row12103 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

theorem rowCheck12103 : row12103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12103 := by decide +kernel

theorem rowEval12103 (x : Key → ℝ) : Integer.Sparse.eval row12103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12103, Integer.Sparse.eval_collectBalanced, rawRowCheck12103]

def rawRow12104 : Integer.Sparse Key := [(key982, 2), (key986, 2), (key986, 2), (key1096, 2), (key1185, 2), (key1185, 2), (key1171, 2), (key1171, 2), (key1222, 2), (key1222, 2), (key1224, 2), (key1224, 2), (key986, -2), (key986, -2), (key988, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key1186, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key1224, -2)]

theorem rawRowCheck12104 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form18 = rawRow12104 := by decide +kernel

def row12104 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12104 : row12104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12104 := by decide +kernel

theorem rowEval12104 (x : Key → ℝ) : Integer.Sparse.eval row12104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12104, Integer.Sparse.eval_collectBalanced, rawRowCheck12104]

def rawRow12105 : Integer.Sparse Key := [(key986, 2), (key982, 2), (key986, 2), (key1185, 2), (key1096, 2), (key1185, 2), (key1222, 2), (key1224, 2), (key1171, 2), (key1224, 2), (key1171, 2), (key1222, 2), (key986, -2), (key988, -2), (key986, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1224, -2), (key1175, -2), (key1224, -2)]

theorem rawRowCheck12105 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form18 = rawRow12105 := by decide +kernel

def row12105 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12105 : row12105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12105 := by decide +kernel

theorem rowEval12105 (x : Key → ℝ) : Integer.Sparse.eval row12105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12105, Integer.Sparse.eval_collectBalanced, rawRowCheck12105]

def rawRow12106 : Integer.Sparse Key := [(key986, 2), (key986, 2), (key982, 2), (key1185, 2), (key1185, 2), (key1096, 2), (key1224, 2), (key1222, 2), (key1224, 2), (key1171, 2), (key1222, 2), (key1171, 2), (key988, -2), (key986, -2), (key986, -2), (key1186, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1100, -2), (key1224, -2), (key1224, -2), (key1175, -2)]

theorem rawRowCheck12106 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form18 = rawRow12106 := by decide +kernel

def row12106 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12106 : row12106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12106 := by decide +kernel

theorem rowEval12106 (x : Key → ℝ) : Integer.Sparse.eval row12106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12106, Integer.Sparse.eval_collectBalanced, rawRowCheck12106]

def rawRow12107 : Integer.Sparse Key := [(key1096, 2), (key1171, 2), (key1171, 2), (key982, 2), (key1222, 2), (key1222, 2), (key986, 2), (key986, 2), (key1185, 2), (key1185, 2), (key1224, 2), (key1224, 2), (key1100, -2), (key1100, -2), (key1175, -2), (key986, -2), (key986, -2), (key1185, -2), (key1185, -2), (key1224, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1186, -2)]

theorem rawRowCheck12107 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form18 = rawRow12107 := by decide +kernel

def row12107 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12107 : row12107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12107 := by decide +kernel

theorem rowEval12107 (x : Key → ℝ) : Integer.Sparse.eval row12107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12107, Integer.Sparse.eval_collectBalanced, rawRowCheck12107]

def rawRow12108 : Integer.Sparse Key := [(key1171, 2), (key1096, 2), (key1171, 2), (key1222, 2), (key982, 2), (key1222, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1100, -2), (key1175, -2), (key1100, -2), (key1185, -2), (key1224, -2), (key986, -2), (key1224, -2), (key986, -2), (key1185, -2), (key1186, -2), (key988, -2), (key1186, -2)]

theorem rawRowCheck12108 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form18 = rawRow12108 := by decide +kernel

def row12108 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12108 : row12108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12108 := by decide +kernel

theorem rowEval12108 (x : Key → ℝ) : Integer.Sparse.eval row12108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12108, Integer.Sparse.eval_collectBalanced, rawRowCheck12108]

def rawRow12109 : Integer.Sparse Key := [(key1171, 2), (key1171, 2), (key1096, 2), (key1222, 2), (key1222, 2), (key982, 2), (key1224, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1185, 2), (key986, 2), (key1175, -2), (key1100, -2), (key1100, -2), (key1224, -2), (key1185, -2), (key1224, -2), (key986, -2), (key1185, -2), (key986, -2), (key1186, -2), (key1186, -2), (key988, -2)]

theorem rawRowCheck12109 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form18 = rawRow12109 := by decide +kernel

def row12109 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12109 : row12109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12109 := by decide +kernel

theorem rowEval12109 (x : Key → ℝ) : Integer.Sparse.eval row12109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck12109, Integer.Sparse.eval_collectBalanced, rawRowCheck12109]

def rawRow12110 : Integer.Sparse Key := [(key1185, 2), (key1222, 2), (key1224, 2), (key986, 2), (key1171, 2), (key1224, 2), (key982, 2), (key986, 2), (key1096, 2), (key1185, 2), (key1171, 2), (key1222, 2), (key1185, -2), (key1186, -2), (key1224, -2), (key986, -2), (key988, -2), (key1100, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key986, -2), (key1100, -2), (key1185, -2)]

theorem rawRowCheck12110 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form18 = rawRow12110 := by decide +kernel

def row12110 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12110 : row12110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12110 := by decide +kernel

theorem rowEval12110 (x : Key → ℝ) : Integer.Sparse.eval row12110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12110, Integer.Sparse.eval_collectBalanced, rawRowCheck12110]

def rawRow12111 : Integer.Sparse Key := [(key1185, 2), (key1224, 2), (key1222, 2), (key986, 2), (key1224, 2), (key1171, 2), (key986, 2), (key982, 2), (key1185, 2), (key1096, 2), (key1222, 2), (key1171, 2), (key1186, -2), (key1185, -2), (key1224, -2), (key988, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key1175, -2), (key986, -2), (key1185, -2), (key1100, -2)]

theorem rawRowCheck12111 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form18 = rawRow12111 := by decide +kernel

def row12111 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12111 : row12111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12111 := by decide +kernel

theorem rowEval12111 (x : Key → ℝ) : Integer.Sparse.eval row12111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12111, Integer.Sparse.eval_collectBalanced, rawRowCheck12111]

def rawRow12112 : Integer.Sparse Key := [(key1222, 2), (key1185, 2), (key1224, 2), (key1171, 2), (key986, 2), (key1224, 2), (key1096, 2), (key1171, 2), (key982, 2), (key1222, 2), (key986, 2), (key1185, 2), (key1185, -2), (key1224, -2), (key1186, -2), (key1100, -2), (key1175, -2), (key986, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1100, -2), (key986, -2), (key1185, -2)]

theorem rawRowCheck12112 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form18 = rawRow12112 := by decide +kernel

def row12112 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12112 : row12112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12112 := by decide +kernel

theorem rowEval12112 (x : Key → ℝ) : Integer.Sparse.eval row12112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12112, Integer.Sparse.eval_collectBalanced, rawRowCheck12112]

def rawRow12113 : Integer.Sparse Key := [(key1222, 2), (key1224, 2), (key1185, 2), (key1171, 2), (key1224, 2), (key986, 2), (key1171, 2), (key1096, 2), (key1222, 2), (key982, 2), (key1185, 2), (key986, 2), (key1224, -2), (key1185, -2), (key1186, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1186, -2), (key988, -2), (key1100, -2), (key1185, -2), (key986, -2)]

theorem rawRowCheck12113 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form18 = rawRow12113 := by decide +kernel

def row12113 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12113 : row12113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12113 := by decide +kernel

theorem rowEval12113 (x : Key → ℝ) : Integer.Sparse.eval row12113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck12113, Integer.Sparse.eval_collectBalanced, rawRowCheck12113]

def rawRow12114 : Integer.Sparse Key := [(key1224, 2), (key1185, 2), (key1222, 2), (key1224, 2), (key986, 2), (key1171, 2), (key1185, 2), (key1222, 2), (key986, 2), (key1171, 2), (key982, 2), (key1096, 2), (key1186, -2), (key1224, -2), (key1185, -2), (key1186, -2), (key1224, -2), (key988, -2), (key1175, -2), (key986, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1100, -2)]

theorem rawRowCheck12114 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form18 = rawRow12114 := by decide +kernel

def row12114 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12114 : row12114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12114 := by decide +kernel

theorem rowEval12114 (x : Key → ℝ) : Integer.Sparse.eval row12114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12114, Integer.Sparse.eval_collectBalanced, rawRowCheck12114]

def rawRow12115 : Integer.Sparse Key := [(key1224, 2), (key1222, 2), (key1185, 2), (key1224, 2), (key1171, 2), (key986, 2), (key1222, 2), (key1185, 2), (key1171, 2), (key986, 2), (key1096, 2), (key982, 2), (key1224, -2), (key1186, -2), (key1185, -2), (key1224, -2), (key1186, -2), (key1175, -2), (key988, -2), (key1100, -2), (key986, -2), (key1185, -2), (key1100, -2), (key986, -2)]

theorem rawRowCheck12115 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form18 = rawRow12115 := by decide +kernel

def row12115 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

theorem rowCheck12115 : row12115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12115 := by decide +kernel

theorem rowEval12115 (x : Key → ℝ) : Integer.Sparse.eval row12115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck12115, Integer.Sparse.eval_collectBalanced, rawRowCheck12115]

def rawRow12116 : Integer.Sparse Key := [(key2420, -4), (key2427, -4), (key2427, -4), (key2427, -4), (key2427, -4), (key2438, -4), (key2495, 6), (key2495, 6), (key2504, 6), (key2504, 6)]

theorem rawRowCheck12116 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form19 = rawRow12116 := by decide +kernel

def row12116 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

theorem rowCheck12116 : row12116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12116 := by decide +kernel

theorem rowEval12116 (x : Key → ℝ) : Integer.Sparse.eval row12116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12116, Integer.Sparse.eval_collectBalanced, rawRowCheck12116]

def rawRow12117 : Integer.Sparse Key := [(key2427, -4), (key2420, -4), (key2427, -4), (key2427, -4), (key2438, -4), (key2427, -4), (key2495, 6), (key2504, 6), (key2495, 6), (key2504, 6)]

theorem rawRowCheck12117 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form19 = rawRow12117 := by decide +kernel

def row12117 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

theorem rowCheck12117 : row12117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12117 := by decide +kernel

theorem rowEval12117 (x : Key → ℝ) : Integer.Sparse.eval row12117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12117, Integer.Sparse.eval_collectBalanced, rawRowCheck12117]

def rawRow12118 : Integer.Sparse Key := [(key2427, -4), (key2427, -4), (key2420, -4), (key2438, -4), (key2427, -4), (key2427, -4), (key2504, 6), (key2495, 6), (key2495, 6), (key2504, 6)]

theorem rawRowCheck12118 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form19 = rawRow12118 := by decide +kernel

def row12118 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

theorem rowCheck12118 : row12118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12118 := by decide +kernel

theorem rowEval12118 (x : Key → ℝ) : Integer.Sparse.eval row12118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12118, Integer.Sparse.eval_collectBalanced, rawRowCheck12118]

def rawRow12119 : Integer.Sparse Key := [(key2427, -4), (key2427, -4), (key2438, -4), (key2420, -4), (key2427, -4), (key2427, -4), (key2495, 6), (key2504, 6), (key2504, 6), (key2495, 6)]

theorem rawRowCheck12119 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form19 = rawRow12119 := by decide +kernel

def row12119 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

theorem rowCheck12119 : row12119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12119 := by decide +kernel

theorem rowEval12119 (x : Key → ℝ) : Integer.Sparse.eval row12119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12119, Integer.Sparse.eval_collectBalanced, rawRowCheck12119]

def rawRow12120 : Integer.Sparse Key := [(key2427, -4), (key2438, -4), (key2427, -4), (key2427, -4), (key2420, -4), (key2427, -4), (key2504, 6), (key2495, 6), (key2504, 6), (key2495, 6)]

theorem rawRowCheck12120 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form19 = rawRow12120 := by decide +kernel

def row12120 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

theorem rowCheck12120 : row12120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12120 := by decide +kernel

theorem rowEval12120 (x : Key → ℝ) : Integer.Sparse.eval row12120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12120, Integer.Sparse.eval_collectBalanced, rawRowCheck12120]

def rawRow12121 : Integer.Sparse Key := [(key2438, -4), (key2427, -4), (key2427, -4), (key2427, -4), (key2427, -4), (key2420, -4), (key2504, 6), (key2504, 6), (key2495, 6), (key2495, 6)]

theorem rawRowCheck12121 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form19 = rawRow12121 := by decide +kernel

def row12121 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

theorem rowCheck12121 : row12121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12121 := by decide +kernel

theorem rowEval12121 (x : Key → ℝ) : Integer.Sparse.eval row12121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12121, Integer.Sparse.eval_collectBalanced, rawRowCheck12121]

def rawRow12122 : Integer.Sparse Key := [(key2420, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2495, -4), (key2504, -4), (key2427, 6), (key2427, 6), (key2438, 6), (key2504, 6)]

theorem rawRowCheck12122 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form19 = rawRow12122 := by decide +kernel

def row12122 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12122 : row12122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12122 := by decide +kernel

theorem rowEval12122 (x : Key → ℝ) : Integer.Sparse.eval row12122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12122, Integer.Sparse.eval_collectBalanced, rawRowCheck12122]

def rawRow12123 : Integer.Sparse Key := [(key2427, -4), (key2420, -4), (key2427, -4), (key2495, -4), (key2504, -4), (key2495, -4), (key2427, 6), (key2438, 6), (key2427, 6), (key2504, 6)]

theorem rawRowCheck12123 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form19 = rawRow12123 := by decide +kernel

def row12123 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12123 : row12123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12123 := by decide +kernel

theorem rowEval12123 (x : Key → ℝ) : Integer.Sparse.eval row12123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12123, Integer.Sparse.eval_collectBalanced, rawRowCheck12123]

def rawRow12124 : Integer.Sparse Key := [(key2427, -4), (key2427, -4), (key2420, -4), (key2504, -4), (key2495, -4), (key2495, -4), (key2438, 6), (key2427, 6), (key2427, 6), (key2504, 6)]

theorem rawRowCheck12124 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form19 = rawRow12124 := by decide +kernel

def row12124 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12124 : row12124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12124 := by decide +kernel

theorem rowEval12124 (x : Key → ℝ) : Integer.Sparse.eval row12124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12124, Integer.Sparse.eval_collectBalanced, rawRowCheck12124]

def rawRow12125 : Integer.Sparse Key := [(key2420, -4), (key2495, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2504, -4), (key2427, 6), (key2427, 6), (key2504, 6), (key2438, 6)]

theorem rawRowCheck12125 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form19 = rawRow12125 := by decide +kernel

def row12125 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12125 : row12125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12125 := by decide +kernel

theorem rowEval12125 (x : Key → ℝ) : Integer.Sparse.eval row12125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12125, Integer.Sparse.eval_collectBalanced, rawRowCheck12125]

def rawRow12126 : Integer.Sparse Key := [(key2495, -4), (key2420, -4), (key2495, -4), (key2427, -4), (key2504, -4), (key2427, -4), (key2427, 6), (key2504, 6), (key2427, 6), (key2438, 6)]

theorem rawRowCheck12126 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form19 = rawRow12126 := by decide +kernel

def row12126 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12126 : row12126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12126 := by decide +kernel

theorem rowEval12126 (x : Key → ℝ) : Integer.Sparse.eval row12126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12126, Integer.Sparse.eval_collectBalanced, rawRowCheck12126]

def rawRow12127 : Integer.Sparse Key := [(key2495, -4), (key2495, -4), (key2420, -4), (key2504, -4), (key2427, -4), (key2427, -4), (key2504, 6), (key2427, 6), (key2427, 6), (key2438, 6)]

theorem rawRowCheck12127 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form19 = rawRow12127 := by decide +kernel

def row12127 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12127 : row12127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12127 := by decide +kernel

theorem rowEval12127 (x : Key → ℝ) : Integer.Sparse.eval row12127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form19) x := by
  rw [rowCheck12127, Integer.Sparse.eval_collectBalanced, rawRowCheck12127]

def rawRow12128 : Integer.Sparse Key := [(key2427, -4), (key2495, -4), (key2504, -4), (key2420, -4), (key2427, -4), (key2495, -4), (key2427, 6), (key2438, 6), (key2504, 6), (key2427, 6)]

theorem rawRowCheck12128 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form19 = rawRow12128 := by decide +kernel

def row12128 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12128 : row12128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12128 := by decide +kernel

theorem rowEval12128 (x : Key → ℝ) : Integer.Sparse.eval row12128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12128, Integer.Sparse.eval_collectBalanced, rawRowCheck12128]

def rawRow12129 : Integer.Sparse Key := [(key2427, -4), (key2504, -4), (key2495, -4), (key2427, -4), (key2420, -4), (key2495, -4), (key2438, 6), (key2427, 6), (key2504, 6), (key2427, 6)]

theorem rawRowCheck12129 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form19 = rawRow12129 := by decide +kernel

def row12129 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12129 : row12129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12129 := by decide +kernel

theorem rowEval12129 (x : Key → ℝ) : Integer.Sparse.eval row12129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12129, Integer.Sparse.eval_collectBalanced, rawRowCheck12129]

def rawRow12130 : Integer.Sparse Key := [(key2495, -4), (key2427, -4), (key2504, -4), (key2420, -4), (key2495, -4), (key2427, -4), (key2427, 6), (key2504, 6), (key2438, 6), (key2427, 6)]

theorem rawRowCheck12130 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form19 = rawRow12130 := by decide +kernel

def row12130 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12130 : row12130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12130 := by decide +kernel

theorem rowEval12130 (x : Key → ℝ) : Integer.Sparse.eval row12130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12130, Integer.Sparse.eval_collectBalanced, rawRowCheck12130]

def rawRow12131 : Integer.Sparse Key := [(key2495, -4), (key2504, -4), (key2427, -4), (key2495, -4), (key2420, -4), (key2427, -4), (key2504, 6), (key2427, 6), (key2438, 6), (key2427, 6)]

theorem rawRowCheck12131 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form19 = rawRow12131 := by decide +kernel

def row12131 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12131 : row12131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12131 := by decide +kernel

theorem rowEval12131 (x : Key → ℝ) : Integer.Sparse.eval row12131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form19) x := by
  rw [rowCheck12131, Integer.Sparse.eval_collectBalanced, rawRowCheck12131]

def rawRow12132 : Integer.Sparse Key := [(key2504, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2495, -4), (key2420, -4), (key2438, 6), (key2504, 6), (key2427, 6), (key2427, 6)]

theorem rawRowCheck12132 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form19 = rawRow12132 := by decide +kernel

def row12132 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12132 : row12132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12132 := by decide +kernel

theorem rowEval12132 (x : Key → ℝ) : Integer.Sparse.eval row12132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12132, Integer.Sparse.eval_collectBalanced, rawRowCheck12132]

def rawRow12133 : Integer.Sparse Key := [(key2504, -4), (key2495, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2420, -4), (key2504, 6), (key2438, 6), (key2427, 6), (key2427, 6)]

theorem rawRowCheck12133 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form19 = rawRow12133 := by decide +kernel

def row12133 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

theorem rowCheck12133 : row12133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12133 := by decide +kernel

theorem rowEval12133 (x : Key → ℝ) : Integer.Sparse.eval row12133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form19) x := by
  rw [rowCheck12133, Integer.Sparse.eval_collectBalanced, rawRowCheck12133]

def rawRow12134 : Integer.Sparse Key := [(key1851, 6), (key1851, 6), (key1855, 6), (key1855, 6), (key1886, -24)]

theorem rawRowCheck12134 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form20 = rawRow12134 := by decide +kernel

def row12134 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

theorem rowCheck12134 : row12134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12134 := by decide +kernel

theorem rowEval12134 (x : Key → ℝ) : Integer.Sparse.eval row12134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12134, Integer.Sparse.eval_collectBalanced, rawRowCheck12134]

def rawRow12135 : Integer.Sparse Key := [(key1851, 6), (key1855, 6), (key1851, 6), (key1855, 6), (key1886, -24)]

theorem rawRowCheck12135 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form20 = rawRow12135 := by decide +kernel

def row12135 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

theorem rowCheck12135 : row12135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12135 := by decide +kernel

theorem rowEval12135 (x : Key → ℝ) : Integer.Sparse.eval row12135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12135, Integer.Sparse.eval_collectBalanced, rawRowCheck12135]

def rawRow12136 : Integer.Sparse Key := [(key1855, 6), (key1851, 6), (key1851, 6), (key1855, 6), (key1886, -24)]

theorem rawRowCheck12136 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form20 = rawRow12136 := by decide +kernel

def row12136 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

theorem rowCheck12136 : row12136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12136 := by decide +kernel

theorem rowEval12136 (x : Key → ℝ) : Integer.Sparse.eval row12136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12136, Integer.Sparse.eval_collectBalanced, rawRowCheck12136]

def rawRow12137 : Integer.Sparse Key := [(key1851, 6), (key1855, 6), (key1855, 6), (key1851, 6), (key1886, -24)]

theorem rawRowCheck12137 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form20 = rawRow12137 := by decide +kernel

def row12137 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

theorem rowCheck12137 : row12137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12137 := by decide +kernel

theorem rowEval12137 (x : Key → ℝ) : Integer.Sparse.eval row12137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12137, Integer.Sparse.eval_collectBalanced, rawRowCheck12137]

def rawRow12138 : Integer.Sparse Key := [(key1855, 6), (key1851, 6), (key1855, 6), (key1851, 6), (key1886, -24)]

theorem rawRowCheck12138 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form20 = rawRow12138 := by decide +kernel

def row12138 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

theorem rowCheck12138 : row12138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12138 := by decide +kernel

theorem rowEval12138 (x : Key → ℝ) : Integer.Sparse.eval row12138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12138, Integer.Sparse.eval_collectBalanced, rawRowCheck12138]

def rawRow12139 : Integer.Sparse Key := [(key1855, 6), (key1855, 6), (key1851, 6), (key1851, 6), (key1886, -24)]

theorem rawRowCheck12139 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form20 = rawRow12139 := by decide +kernel

def row12139 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

theorem rowCheck12139 : row12139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12139 := by decide +kernel

theorem rowEval12139 (x : Key → ℝ) : Integer.Sparse.eval row12139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12139, Integer.Sparse.eval_collectBalanced, rawRowCheck12139]

def rawRow12140 : Integer.Sparse Key := [(key1851, 6), (key1851, 6), (key1855, 6), (key1886, 6), (key1855, -24)]

theorem rawRowCheck12140 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form20 = rawRow12140 := by decide +kernel

def row12140 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12140 : row12140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12140 := by decide +kernel

theorem rowEval12140 (x : Key → ℝ) : Integer.Sparse.eval row12140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12140, Integer.Sparse.eval_collectBalanced, rawRowCheck12140]

def rawRow12141 : Integer.Sparse Key := [(key1851, 6), (key1855, 6), (key1851, 6), (key1886, 6), (key1855, -24)]

theorem rawRowCheck12141 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form20 = rawRow12141 := by decide +kernel

def row12141 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12141 : row12141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12141 := by decide +kernel

theorem rowEval12141 (x : Key → ℝ) : Integer.Sparse.eval row12141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12141, Integer.Sparse.eval_collectBalanced, rawRowCheck12141]

def rawRow12142 : Integer.Sparse Key := [(key1855, 6), (key1851, 6), (key1851, 6), (key1886, 6), (key1855, -24)]

theorem rawRowCheck12142 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form20 = rawRow12142 := by decide +kernel

def row12142 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12142 : row12142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12142 := by decide +kernel

theorem rowEval12142 (x : Key → ℝ) : Integer.Sparse.eval row12142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12142, Integer.Sparse.eval_collectBalanced, rawRowCheck12142]

def rawRow12143 : Integer.Sparse Key := [(key1851, 6), (key1851, 6), (key1886, 6), (key1855, 6), (key1855, -24)]

theorem rawRowCheck12143 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form20 = rawRow12143 := by decide +kernel

def row12143 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12143 : row12143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12143 := by decide +kernel

theorem rowEval12143 (x : Key → ℝ) : Integer.Sparse.eval row12143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12143, Integer.Sparse.eval_collectBalanced, rawRowCheck12143]

def rawRow12144 : Integer.Sparse Key := [(key1851, 6), (key1886, 6), (key1851, 6), (key1855, 6), (key1855, -24)]

theorem rawRowCheck12144 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form20 = rawRow12144 := by decide +kernel

def row12144 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12144 : row12144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12144 := by decide +kernel

theorem rowEval12144 (x : Key → ℝ) : Integer.Sparse.eval row12144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12144, Integer.Sparse.eval_collectBalanced, rawRowCheck12144]

def rawRow12145 : Integer.Sparse Key := [(key1886, 6), (key1851, 6), (key1851, 6), (key1855, 6), (key1855, -24)]

theorem rawRowCheck12145 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form20 = rawRow12145 := by decide +kernel

def row12145 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12145 : row12145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12145 := by decide +kernel

theorem rowEval12145 (x : Key → ℝ) : Integer.Sparse.eval row12145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form20) x := by
  rw [rowCheck12145, Integer.Sparse.eval_collectBalanced, rawRowCheck12145]

def rawRow12146 : Integer.Sparse Key := [(key1851, 6), (key1855, 6), (key1886, 6), (key1851, 6), (key1855, -24)]

theorem rawRowCheck12146 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form20 = rawRow12146 := by decide +kernel

def row12146 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12146 : row12146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12146 := by decide +kernel

theorem rowEval12146 (x : Key → ℝ) : Integer.Sparse.eval row12146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12146, Integer.Sparse.eval_collectBalanced, rawRowCheck12146]

def rawRow12147 : Integer.Sparse Key := [(key1855, 6), (key1851, 6), (key1886, 6), (key1851, 6), (key1855, -24)]

theorem rawRowCheck12147 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form20 = rawRow12147 := by decide +kernel

def row12147 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12147 : row12147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12147 := by decide +kernel

theorem rowEval12147 (x : Key → ℝ) : Integer.Sparse.eval row12147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12147, Integer.Sparse.eval_collectBalanced, rawRowCheck12147]

def rawRow12148 : Integer.Sparse Key := [(key1851, 6), (key1886, 6), (key1855, 6), (key1851, 6), (key1855, -24)]

theorem rawRowCheck12148 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form20 = rawRow12148 := by decide +kernel

def row12148 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12148 : row12148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12148 := by decide +kernel

theorem rowEval12148 (x : Key → ℝ) : Integer.Sparse.eval row12148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck12148, Integer.Sparse.eval_collectBalanced, rawRowCheck12148]

def rawRow12149 : Integer.Sparse Key := [(key1886, 6), (key1851, 6), (key1855, 6), (key1851, 6), (key1855, -24)]

theorem rawRowCheck12149 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form20 = rawRow12149 := by decide +kernel

def row12149 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12149 : row12149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12149 := by decide +kernel

theorem rowEval12149 (x : Key → ℝ) : Integer.Sparse.eval row12149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form20) x := by
  rw [rowCheck12149, Integer.Sparse.eval_collectBalanced, rawRowCheck12149]

def rawRow12150 : Integer.Sparse Key := [(key1855, 6), (key1886, 6), (key1851, 6), (key1851, 6), (key1855, -24)]

theorem rawRowCheck12150 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form20 = rawRow12150 := by decide +kernel

def row12150 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12150 : row12150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12150 := by decide +kernel

theorem rowEval12150 (x : Key → ℝ) : Integer.Sparse.eval row12150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12150, Integer.Sparse.eval_collectBalanced, rawRowCheck12150]

def rawRow12151 : Integer.Sparse Key := [(key1886, 6), (key1855, 6), (key1851, 6), (key1851, 6), (key1855, -24)]

theorem rawRowCheck12151 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form20 = rawRow12151 := by decide +kernel

def row12151 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

theorem rowCheck12151 : row12151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12151 := by decide +kernel

theorem rowEval12151 (x : Key → ℝ) : Integer.Sparse.eval row12151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form20) x := by
  rw [rowCheck12151, Integer.Sparse.eval_collectBalanced, rawRowCheck12151]

def rawRow12152 : Integer.Sparse Key := [(key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2506, 1), (key2506, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2506, 1), (key2506, 1), (key2522, 1), (key2522, 1), (key2538, -2), (key2543, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2543, -2), (key2543, -2), (key2554, -2), (key2554, -2), (key2563, -2), (key2563, -2)]

theorem rawRowCheck12152 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form21 = rawRow12152 := by decide +kernel

def row12152 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

theorem rowCheck12152 : row12152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12152 := by decide +kernel

theorem rowEval12152 (x : Key → ℝ) : Integer.Sparse.eval row12152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12152, Integer.Sparse.eval_collectBalanced, rawRowCheck12152]

def rawRow12153 : Integer.Sparse Key := [(key2480, 1), (key2482, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2482, 1), (key2506, 1), (key2543, -2), (key2538, -2), (key2543, -2), (key2554, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2563, -2), (key2543, -2), (key2554, -2)]

theorem rawRowCheck12153 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form21 = rawRow12153 := by decide +kernel

def row12153 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

theorem rowCheck12153 : row12153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12153 := by decide +kernel

theorem rowEval12153 (x : Key → ℝ) : Integer.Sparse.eval row12153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12153, Integer.Sparse.eval_collectBalanced, rawRowCheck12153]

def rawRow12154 : Integer.Sparse Key := [(key2482, 1), (key2480, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2506, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2506, 1), (key2482, 1), (key2543, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2538, -2), (key2563, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2554, -2), (key2543, -2)]

theorem rawRowCheck12154 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form21 = rawRow12154 := by decide +kernel

def row12154 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

theorem rowCheck12154 : row12154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12154 := by decide +kernel

theorem rowEval12154 (x : Key → ℝ) : Integer.Sparse.eval row12154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12154, Integer.Sparse.eval_collectBalanced, rawRowCheck12154]

def rawRow12155 : Integer.Sparse Key := [(key2503, 1), (key2506, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2480, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2506, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1), (key2554, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2543, -2), (key2563, -2), (key2538, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2543, -2), (key2554, -2)]

theorem rawRowCheck12155 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form21 = rawRow12155 := by decide +kernel

def row12155 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

theorem rowCheck12155 : row12155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12155 := by decide +kernel

theorem rowEval12155 (x : Key → ℝ) : Integer.Sparse.eval row12155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12155, Integer.Sparse.eval_collectBalanced, rawRowCheck12155]

def rawRow12156 : Integer.Sparse Key := [(key2506, 1), (key2503, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2554, -2), (key2563, -2), (key2554, -2), (key2543, -2), (key2563, -2), (key2543, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2538, -2), (key2554, -2), (key2543, -2)]

theorem rawRowCheck12156 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form21 = rawRow12156 := by decide +kernel

def row12156 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

theorem rowCheck12156 : row12156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12156 := by decide +kernel

theorem rowEval12156 (x : Key → ℝ) : Integer.Sparse.eval row12156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12156, Integer.Sparse.eval_collectBalanced, rawRowCheck12156]

def rawRow12157 : Integer.Sparse Key := [(key2522, 1), (key2522, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1), (key2506, 1), (key2506, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1), (key2563, -2), (key2554, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2543, -2), (key2554, -2), (key2554, -2), (key2543, -2), (key2543, -2), (key2538, -2), (key2538, -2)]

theorem rawRowCheck12157 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form21 = rawRow12157 := by decide +kernel

def row12157 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

theorem rowCheck12157 : row12157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12157 := by decide +kernel

theorem rowEval12157 (x : Key → ℝ) : Integer.Sparse.eval row12157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12157, Integer.Sparse.eval_collectBalanced, rawRowCheck12157]

def rawRow12158 : Integer.Sparse Key := [(key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2392, 1), (key2392, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2440, 1), (key2440, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2543, 1), (key2543, 1), (key2554, 1), (key2554, 1), (key2563, 1), (key2563, 1), (key2381, -2), (key2392, -2), (key2392, -2), (key2409, -2), (key2440, -2), (key2440, -2), (key2482, -2), (key2482, -2), (key2506, -2), (key2506, -2), (key2522, -2), (key2522, -2)]

theorem rawRowCheck12158 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form21 = rawRow12158 := by decide +kernel

def row12158 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12158 : row12158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12158 := by decide +kernel

theorem rowEval12158 (x : Key → ℝ) : Integer.Sparse.eval row12158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12158, Integer.Sparse.eval_collectBalanced, rawRowCheck12158]

def rawRow12159 : Integer.Sparse Key := [(key2390, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2563, 1), (key2543, 1), (key2554, 1), (key2392, -2), (key2381, -2), (key2392, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2506, -2), (key2522, -2), (key2482, -2), (key2522, -2), (key2482, -2), (key2506, -2)]

theorem rawRowCheck12159 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form21 = rawRow12159 := by decide +kernel

def row12159 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

theorem rowCheck12159 : row12159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12159 := by decide +kernel

theorem rowEval12159 (x : Key → ℝ) : Integer.Sparse.eval row12159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck12159, Integer.Sparse.eval_collectBalanced, rawRowCheck12159]

end MUB6.Certificate.GramRows

end OAI

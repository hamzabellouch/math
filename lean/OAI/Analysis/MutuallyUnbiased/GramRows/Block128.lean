import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow13312 : Integer.Sparse Key := [(key2502, 4), (key2502, 4), (key2377, 4), (key2502, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2377, -2), (key2518, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2389, -2), (key2479, 4), (key2479, 4), (key2389, 4)]

theorem rawRowCheck13312 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form0 = rawRow13312 := by decide +kernel

def row13312 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13312 : row13312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13312 := by decide +kernel

theorem rowEval13312 (x : Key → ℝ) : Integer.Sparse.eval row13312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13312, Integer.Sparse.eval_collectBalanced, rawRowCheck13312]

def rawRow13313 : Integer.Sparse Key := [(key2405, 4), (key2479, 4), (key2479, 4), (key2436, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2518, -2), (key2405, -2), (key2405, -2), (key2471, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2436, 4), (key2502, 4), (key2502, 4)]

theorem rawRowCheck13313 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form0 = rawRow13313 := by decide +kernel

def row13313 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13313 : row13313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13313 := by decide +kernel

theorem rowEval13313 (x : Key → ℝ) : Integer.Sparse.eval row13313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13313, Integer.Sparse.eval_collectBalanced, rawRowCheck13313]

def rawRow13314 : Integer.Sparse Key := [(key2479, 4), (key2405, 4), (key2479, 4), (key2502, -2), (key2518, -2), (key2436, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, 4), (key2436, 4), (key2502, 4)]

theorem rawRowCheck13314 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form0 = rawRow13314 := by decide +kernel

def row13314 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13314 : row13314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13314 := by decide +kernel

theorem rowEval13314 (x : Key → ℝ) : Integer.Sparse.eval row13314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13314, Integer.Sparse.eval_collectBalanced, rawRowCheck13314]

def rawRow13315 : Integer.Sparse Key := [(key2479, 4), (key2479, 4), (key2405, 4), (key2518, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2436, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2405, -2), (key2502, 4), (key2502, 4), (key2436, 4)]

theorem rawRowCheck13315 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form0 = rawRow13315 := by decide +kernel

def row13315 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13315 : row13315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13315 := by decide +kernel

theorem rowEval13315 (x : Key → ℝ) : Integer.Sparse.eval row13315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13315, Integer.Sparse.eval_collectBalanced, rawRowCheck13315]

def rawRow13316 : Integer.Sparse Key := [(key2377, 4), (key2502, 4), (key2502, 4), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2377, -2), (key2377, -2), (key2471, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2389, 4), (key2479, 4), (key2479, 4)]

theorem rawRowCheck13316 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form0 = rawRow13316 := by decide +kernel

def row13316 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13316 : row13316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13316 := by decide +kernel

theorem rowEval13316 (x : Key → ℝ) : Integer.Sparse.eval row13316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13316, Integer.Sparse.eval_collectBalanced, rawRowCheck13316]

def rawRow13317 : Integer.Sparse Key := [(key2502, 4), (key2377, 4), (key2502, 4), (key2479, -2), (key2518, -2), (key2389, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2479, 4), (key2389, 4), (key2479, 4)]

theorem rawRowCheck13317 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form0 = rawRow13317 := by decide +kernel

def row13317 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13317 : row13317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13317 := by decide +kernel

theorem rowEval13317 (x : Key → ℝ) : Integer.Sparse.eval row13317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13317, Integer.Sparse.eval_collectBalanced, rawRowCheck13317]

def rawRow13318 : Integer.Sparse Key := [(key2502, 4), (key2502, 4), (key2377, 4), (key2518, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2389, -2), (key2502, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2377, -2), (key2479, 4), (key2479, 4), (key2389, 4)]

theorem rawRowCheck13318 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form0 = rawRow13318 := by decide +kernel

def row13318 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13318 : row13318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13318 := by decide +kernel

theorem rowEval13318 (x : Key → ℝ) : Integer.Sparse.eval row13318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13318, Integer.Sparse.eval_collectBalanced, rawRowCheck13318]

def rawRow13319 : Integer.Sparse Key := [(key2389, 4), (key2436, 4), (key2518, 4), (key2377, -2), (key2389, -2), (key2405, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2377, 4), (key2405, 4), (key2471, 4)]

theorem rawRowCheck13319 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form0 = rawRow13319 := by decide +kernel

def row13319 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

theorem rowCheck13319 : row13319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13319 := by decide +kernel

theorem rowEval13319 (x : Key → ℝ) : Integer.Sparse.eval row13319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13319, Integer.Sparse.eval_collectBalanced, rawRowCheck13319]

def rawRow13320 : Integer.Sparse Key := [(key2389, 4), (key2518, 4), (key2436, 4), (key2389, -2), (key2377, -2), (key2479, -2), (key2405, -2), (key2502, -2), (key2436, -2), (key2389, -2), (key2377, -2), (key2479, -2), (key2405, -2), (key2502, -2), (key2436, -2), (key2377, 4), (key2471, 4), (key2405, 4)]

theorem rawRowCheck13320 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form0 = rawRow13320 := by decide +kernel

def row13320 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

theorem rowCheck13320 : row13320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13320 := by decide +kernel

theorem rowEval13320 (x : Key → ℝ) : Integer.Sparse.eval row13320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13320, Integer.Sparse.eval_collectBalanced, rawRowCheck13320]

def rawRow13321 : Integer.Sparse Key := [(key2436, 4), (key2389, 4), (key2518, 4), (key2405, -2), (key2436, -2), (key2377, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2405, -2), (key2436, -2), (key2377, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2405, 4), (key2377, 4), (key2471, 4)]

theorem rawRowCheck13321 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form0 = rawRow13321 := by decide +kernel

def row13321 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

theorem rowCheck13321 : row13321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13321 := by decide +kernel

theorem rowEval13321 (x : Key → ℝ) : Integer.Sparse.eval row13321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13321, Integer.Sparse.eval_collectBalanced, rawRowCheck13321]

def rawRow13322 : Integer.Sparse Key := [(key2436, 4), (key2518, 4), (key2389, 4), (key2436, -2), (key2405, -2), (key2502, -2), (key2377, -2), (key2479, -2), (key2389, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2377, -2), (key2479, -2), (key2389, -2), (key2405, 4), (key2471, 4), (key2377, 4)]

theorem rawRowCheck13322 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form0 = rawRow13322 := by decide +kernel

def row13322 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

theorem rowCheck13322 : row13322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13322 := by decide +kernel

theorem rowEval13322 (x : Key → ℝ) : Integer.Sparse.eval row13322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13322, Integer.Sparse.eval_collectBalanced, rawRowCheck13322]

def rawRow13323 : Integer.Sparse Key := [(key2518, 4), (key2389, 4), (key2436, 4), (key2479, -2), (key2502, -2), (key2389, -2), (key2436, -2), (key2377, -2), (key2405, -2), (key2479, -2), (key2502, -2), (key2389, -2), (key2436, -2), (key2377, -2), (key2405, -2), (key2471, 4), (key2377, 4), (key2405, 4)]

theorem rawRowCheck13323 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form0 = rawRow13323 := by decide +kernel

def row13323 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

theorem rowCheck13323 : row13323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13323 := by decide +kernel

theorem rowEval13323 (x : Key → ℝ) : Integer.Sparse.eval row13323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13323, Integer.Sparse.eval_collectBalanced, rawRowCheck13323]

def rawRow13324 : Integer.Sparse Key := [(key2518, 4), (key2436, 4), (key2389, 4), (key2502, -2), (key2479, -2), (key2436, -2), (key2389, -2), (key2405, -2), (key2377, -2), (key2502, -2), (key2479, -2), (key2436, -2), (key2389, -2), (key2405, -2), (key2377, -2), (key2471, 4), (key2405, 4), (key2377, 4)]

theorem rawRowCheck13324 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form0 = rawRow13324 := by decide +kernel

def row13324 : Integer.Sparse Key := [(key2471, 4), (key2479, -4), (key2502, -4), (key2518, 4)]

theorem rowCheck13324 : row13324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13324 := by decide +kernel

theorem rowEval13324 (x : Key → ℝ) : Integer.Sparse.eval row13324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13324, Integer.Sparse.eval_collectBalanced, rawRowCheck13324]

def rawRow13325 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key995, -2), (key1011, 6), (key1030, -2), (key1030, -2), (key1030, -2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1119, -2), (key1119, -2), (key1119, -2), (key1067, 6), (key1146, -2), (key1146, -2), (key1146, -2)]

theorem rawRowCheck13325 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13325 := by decide +kernel

def row13325 : Integer.Sparse Key := [(key995, -6), (key1011, 6), (key1030, -6), (key1067, 6), (key1108, 12), (key1119, -6), (key1146, -6)]

theorem rowCheck13325 : row13325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13325 := by decide +kernel

theorem rowEval13325 (x : Key → ℝ) : Integer.Sparse.eval row13325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13325, Integer.Sparse.eval_collectBalanced, rawRowCheck13325]

def rawRow13326 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key1011, -2), (key995, 6), (key1108, -2), (key1108, -2), (key1119, -2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1030, -2), (key1108, -2), (key1108, -2), (key1146, 6), (key1067, -2), (key1146, -2), (key1146, -2)]

theorem rawRowCheck13326 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form1 = rawRow13326 := by decide +kernel

def row13326 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13326 : row13326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13326 := by decide +kernel

theorem rowEval13326 (x : Key → ℝ) : Integer.Sparse.eval row13326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13326, Integer.Sparse.eval_collectBalanced, rawRowCheck13326]

def rawRow13327 : Integer.Sparse Key := [(key995, -2), (key1011, -2), (key995, -2), (key995, 6), (key1108, -2), (key1119, -2), (key1108, -2), (key1108, 2), (key1119, 2), (key1030, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1108, -2), (key1030, -2), (key1108, -2), (key1146, 6), (key1146, -2), (key1067, -2), (key1146, -2)]

theorem rawRowCheck13327 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form1 = rawRow13327 := by decide +kernel

def row13327 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13327 : row13327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13327 := by decide +kernel

theorem rowEval13327 (x : Key → ℝ) : Integer.Sparse.eval row13327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13327, Integer.Sparse.eval_collectBalanced, rawRowCheck13327]

def rawRow13328 : Integer.Sparse Key := [(key1011, -2), (key995, -2), (key995, -2), (key995, 6), (key1119, -2), (key1108, -2), (key1108, -2), (key1119, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1030, 2), (key1108, -2), (key1108, -2), (key1030, -2), (key1146, 6), (key1146, -2), (key1146, -2), (key1067, -2)]

theorem rawRowCheck13328 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form1 = rawRow13328 := by decide +kernel

def row13328 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13328 : row13328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13328 := by decide +kernel

theorem rowEval13328 (x : Key → ℝ) : Integer.Sparse.eval row13328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13328, Integer.Sparse.eval_collectBalanced, rawRowCheck13328]

def rawRow13329 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1030, -2), (key1067, 6), (key995, -2), (key995, -2), (key995, -2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1146, -2), (key1146, -2), (key1146, -2), (key1011, 6), (key1119, -2), (key1119, -2), (key1119, -2)]

theorem rawRowCheck13329 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13329 := by decide +kernel

def row13329 : Integer.Sparse Key := [(key995, -6), (key1011, 6), (key1030, -6), (key1067, 6), (key1108, 12), (key1119, -6), (key1146, -6)]

theorem rowCheck13329 : row13329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13329 := by decide +kernel

theorem rowEval13329 (x : Key → ℝ) : Integer.Sparse.eval row13329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13329, Integer.Sparse.eval_collectBalanced, rawRowCheck13329]

def rawRow13330 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1067, -2), (key1030, 6), (key1108, -2), (key1108, -2), (key1146, -2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key995, -2), (key1108, -2), (key1108, -2), (key1119, 6), (key1011, -2), (key1119, -2), (key1119, -2)]

theorem rawRowCheck13330 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form1 = rawRow13330 := by decide +kernel

def row13330 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13330 : row13330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13330 := by decide +kernel

theorem rowEval13330 (x : Key → ℝ) : Integer.Sparse.eval row13330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13330, Integer.Sparse.eval_collectBalanced, rawRowCheck13330]

def rawRow13331 : Integer.Sparse Key := [(key1030, -2), (key1067, -2), (key1030, -2), (key1030, 6), (key1108, -2), (key1146, -2), (key1108, -2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1108, -2), (key995, -2), (key1108, -2), (key1119, 6), (key1119, -2), (key1011, -2), (key1119, -2)]

theorem rawRowCheck13331 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form1 = rawRow13331 := by decide +kernel

def row13331 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13331 : row13331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13331 := by decide +kernel

theorem rowEval13331 (x : Key → ℝ) : Integer.Sparse.eval row13331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13331, Integer.Sparse.eval_collectBalanced, rawRowCheck13331]

def rawRow13332 : Integer.Sparse Key := [(key1067, -2), (key1030, -2), (key1030, -2), (key1030, 6), (key1146, -2), (key1108, -2), (key1108, -2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1108, -2), (key1108, -2), (key995, -2), (key1119, 6), (key1119, -2), (key1119, -2), (key1011, -2)]

theorem rawRowCheck13332 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form1 = rawRow13332 := by decide +kernel

def row13332 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13332 : row13332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13332 := by decide +kernel

theorem rowEval13332 (x : Key → ℝ) : Integer.Sparse.eval row13332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13332, Integer.Sparse.eval_collectBalanced, rawRowCheck13332]

def rawRow13333 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1119, -2), (key1146, 6), (key995, -2), (key995, -2), (key1011, -2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1067, -2), (key1146, -2), (key1146, -2), (key995, 6), (key1030, -2), (key1108, -2), (key1108, -2)]

theorem rawRowCheck13333 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form1 = rawRow13333 := by decide +kernel

def row13333 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13333 : row13333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13333 := by decide +kernel

theorem rowEval13333 (x : Key → ℝ) : Integer.Sparse.eval row13333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13333, Integer.Sparse.eval_collectBalanced, rawRowCheck13333]

def rawRow13334 : Integer.Sparse Key := [(key1108, -2), (key1119, -2), (key1108, -2), (key1146, 6), (key995, -2), (key1011, -2), (key995, -2), (key1108, 2), (key1119, 2), (key1030, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1146, -2), (key1067, -2), (key1146, -2), (key995, 6), (key1108, -2), (key1030, -2), (key1108, -2)]

theorem rawRowCheck13334 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form1 = rawRow13334 := by decide +kernel

def row13334 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13334 : row13334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13334 := by decide +kernel

theorem rowEval13334 (x : Key → ℝ) : Integer.Sparse.eval row13334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13334, Integer.Sparse.eval_collectBalanced, rawRowCheck13334]

def rawRow13335 : Integer.Sparse Key := [(key1119, -2), (key1108, -2), (key1108, -2), (key1146, 6), (key1011, -2), (key995, -2), (key995, -2), (key1119, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1030, 2), (key1146, -2), (key1146, -2), (key1067, -2), (key995, 6), (key1108, -2), (key1108, -2), (key1030, -2)]

theorem rawRowCheck13335 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form1 = rawRow13335 := by decide +kernel

def row13335 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13335 : row13335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13335 := by decide +kernel

theorem rowEval13335 (x : Key → ℝ) : Integer.Sparse.eval row13335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13335, Integer.Sparse.eval_collectBalanced, rawRowCheck13335]

def rawRow13336 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1146, -2), (key1119, 6), (key1030, -2), (key1030, -2), (key1067, -2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1011, -2), (key1119, -2), (key1119, -2), (key1030, 6), (key995, -2), (key1108, -2), (key1108, -2)]

theorem rawRowCheck13336 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form1 = rawRow13336 := by decide +kernel

def row13336 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13336 : row13336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13336 := by decide +kernel

theorem rowEval13336 (x : Key → ℝ) : Integer.Sparse.eval row13336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13336, Integer.Sparse.eval_collectBalanced, rawRowCheck13336]

def rawRow13337 : Integer.Sparse Key := [(key1108, -2), (key1146, -2), (key1108, -2), (key1119, 6), (key1030, -2), (key1067, -2), (key1030, -2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1119, -2), (key1011, -2), (key1119, -2), (key1030, 6), (key1108, -2), (key995, -2), (key1108, -2)]

theorem rawRowCheck13337 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form1 = rawRow13337 := by decide +kernel

def row13337 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13337 : row13337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13337 := by decide +kernel

theorem rowEval13337 (x : Key → ℝ) : Integer.Sparse.eval row13337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13337, Integer.Sparse.eval_collectBalanced, rawRowCheck13337]

def rawRow13338 : Integer.Sparse Key := [(key1146, -2), (key1108, -2), (key1108, -2), (key1119, 6), (key1067, -2), (key1030, -2), (key1030, -2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1119, -2), (key1119, -2), (key1011, -2), (key1030, 6), (key1108, -2), (key1108, -2), (key995, -2)]

theorem rawRowCheck13338 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form1 = rawRow13338 := by decide +kernel

def row13338 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, 2), (key1067, -2), (key1108, -4), (key1119, 2), (key1146, 2)]

theorem rowCheck13338 : row13338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13338 := by decide +kernel

theorem rowEval13338 (x : Key → ℝ) : Integer.Sparse.eval row13338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13338, Integer.Sparse.eval_collectBalanced, rawRowCheck13338]

def rawRow13339 : Integer.Sparse Key := [(key1108, -2), (key1119, -2), (key1146, -2), (key1108, 6), (key1108, -2), (key1119, -2), (key1146, -2), (key995, 2), (key1011, 2), (key1030, 2), (key1119, 2), (key1067, 2), (key1146, 2), (key995, -2), (key1030, -2), (key1108, -2), (key1108, 6), (key995, -2), (key1030, -2), (key1108, -2)]

theorem rawRowCheck13339 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form1 = rawRow13339 := by decide +kernel

def row13339 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

theorem rowCheck13339 : row13339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13339 := by decide +kernel

theorem rowEval13339 (x : Key → ℝ) : Integer.Sparse.eval row13339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13339, Integer.Sparse.eval_collectBalanced, rawRowCheck13339]

def rawRow13340 : Integer.Sparse Key := [(key1119, -2), (key1108, -2), (key1146, -2), (key1108, 6), (key1119, -2), (key1108, -2), (key1146, -2), (key1011, 2), (key995, 2), (key1119, 2), (key1030, 2), (key1146, 2), (key1067, 2), (key995, -2), (key1108, -2), (key1030, -2), (key1108, 6), (key995, -2), (key1108, -2), (key1030, -2)]

theorem rawRowCheck13340 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form1 = rawRow13340 := by decide +kernel

def row13340 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

theorem rowCheck13340 : row13340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13340 := by decide +kernel

theorem rowEval13340 (x : Key → ℝ) : Integer.Sparse.eval row13340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13340, Integer.Sparse.eval_collectBalanced, rawRowCheck13340]

def rawRow13341 : Integer.Sparse Key := [(key1108, -2), (key1146, -2), (key1119, -2), (key1108, 6), (key1108, -2), (key1146, -2), (key1119, -2), (key1030, 2), (key1067, 2), (key995, 2), (key1146, 2), (key1011, 2), (key1119, 2), (key1030, -2), (key995, -2), (key1108, -2), (key1108, 6), (key1030, -2), (key995, -2), (key1108, -2)]

theorem rawRowCheck13341 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form1 = rawRow13341 := by decide +kernel

def row13341 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

theorem rowCheck13341 : row13341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13341 := by decide +kernel

theorem rowEval13341 (x : Key → ℝ) : Integer.Sparse.eval row13341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13341, Integer.Sparse.eval_collectBalanced, rawRowCheck13341]

def rawRow13342 : Integer.Sparse Key := [(key1146, -2), (key1108, -2), (key1119, -2), (key1108, 6), (key1146, -2), (key1108, -2), (key1119, -2), (key1067, 2), (key1030, 2), (key1146, 2), (key995, 2), (key1119, 2), (key1011, 2), (key1030, -2), (key1108, -2), (key995, -2), (key1108, 6), (key1030, -2), (key1108, -2), (key995, -2)]

theorem rawRowCheck13342 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form1 = rawRow13342 := by decide +kernel

def row13342 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

theorem rowCheck13342 : row13342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13342 := by decide +kernel

theorem rowEval13342 (x : Key → ℝ) : Integer.Sparse.eval row13342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13342, Integer.Sparse.eval_collectBalanced, rawRowCheck13342]

def rawRow13343 : Integer.Sparse Key := [(key1119, -2), (key1146, -2), (key1108, -2), (key1108, 6), (key1119, -2), (key1146, -2), (key1108, -2), (key1119, 2), (key1146, 2), (key1011, 2), (key1067, 2), (key995, 2), (key1030, 2), (key1108, -2), (key995, -2), (key1030, -2), (key1108, 6), (key1108, -2), (key995, -2), (key1030, -2)]

theorem rawRowCheck13343 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form1 = rawRow13343 := by decide +kernel

def row13343 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

theorem rowCheck13343 : row13343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13343 := by decide +kernel

theorem rowEval13343 (x : Key → ℝ) : Integer.Sparse.eval row13343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13343, Integer.Sparse.eval_collectBalanced, rawRowCheck13343]

def rawRow13344 : Integer.Sparse Key := [(key1146, -2), (key1119, -2), (key1108, -2), (key1108, 6), (key1146, -2), (key1119, -2), (key1108, -2), (key1146, 2), (key1119, 2), (key1067, 2), (key1011, 2), (key1030, 2), (key995, 2), (key1108, -2), (key1030, -2), (key995, -2), (key1108, 6), (key1108, -2), (key1030, -2), (key995, -2)]

theorem rawRowCheck13344 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form1 = rawRow13344 := by decide +kernel

def row13344 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, -2), (key1067, 2), (key1108, 4), (key1119, -2), (key1146, -2)]

theorem rowCheck13344 : row13344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13344 := by decide +kernel

theorem rowEval13344 (x : Key → ℝ) : Integer.Sparse.eval row13344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13344, Integer.Sparse.eval_collectBalanced, rawRowCheck13344]

def rawRow13345 : Integer.Sparse Key := [(key2372, -2), (key2372, -2), (key2372, -2), (key2385, 6), (key2400, -2), (key2400, -2), (key2400, -2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2475, -2), (key2475, -2), (key2475, -2), (key2432, 6), (key2498, -2), (key2498, -2), (key2498, -2)]

theorem rawRowCheck13345 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13345 := by decide +kernel

def row13345 : Integer.Sparse Key := [(key2372, -6), (key2385, 6), (key2400, -6), (key2432, 6), (key2466, 12), (key2475, -6), (key2498, -6)]

theorem rowCheck13345 : row13345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13345 := by decide +kernel

theorem rowEval13345 (x : Key → ℝ) : Integer.Sparse.eval row13345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13345, Integer.Sparse.eval_collectBalanced, rawRowCheck13345]

def rawRow13346 : Integer.Sparse Key := [(key2372, -2), (key2372, -2), (key2385, -2), (key2372, 6), (key2466, -2), (key2466, -2), (key2475, -2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2475, 2), (key2400, -2), (key2466, -2), (key2466, -2), (key2498, 6), (key2432, -2), (key2498, -2), (key2498, -2)]

theorem rawRowCheck13346 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form2 = rawRow13346 := by decide +kernel

def row13346 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13346 : row13346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13346 := by decide +kernel

theorem rowEval13346 (x : Key → ℝ) : Integer.Sparse.eval row13346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13346, Integer.Sparse.eval_collectBalanced, rawRowCheck13346]

def rawRow13347 : Integer.Sparse Key := [(key2372, -2), (key2385, -2), (key2372, -2), (key2372, 6), (key2466, -2), (key2475, -2), (key2466, -2), (key2466, 2), (key2475, 2), (key2400, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2466, -2), (key2400, -2), (key2466, -2), (key2498, 6), (key2498, -2), (key2432, -2), (key2498, -2)]

theorem rawRowCheck13347 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form2 = rawRow13347 := by decide +kernel

def row13347 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13347 : row13347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13347 := by decide +kernel

theorem rowEval13347 (x : Key → ℝ) : Integer.Sparse.eval row13347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13347, Integer.Sparse.eval_collectBalanced, rawRowCheck13347]

def rawRow13348 : Integer.Sparse Key := [(key2385, -2), (key2372, -2), (key2372, -2), (key2372, 6), (key2475, -2), (key2466, -2), (key2466, -2), (key2475, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2400, 2), (key2466, -2), (key2466, -2), (key2400, -2), (key2498, 6), (key2498, -2), (key2498, -2), (key2432, -2)]

theorem rawRowCheck13348 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form2 = rawRow13348 := by decide +kernel

def row13348 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13348 : row13348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13348 := by decide +kernel

theorem rowEval13348 (x : Key → ℝ) : Integer.Sparse.eval row13348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13348, Integer.Sparse.eval_collectBalanced, rawRowCheck13348]

def rawRow13349 : Integer.Sparse Key := [(key2400, -2), (key2400, -2), (key2400, -2), (key2432, 6), (key2372, -2), (key2372, -2), (key2372, -2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2498, -2), (key2498, -2), (key2498, -2), (key2385, 6), (key2475, -2), (key2475, -2), (key2475, -2)]

theorem rawRowCheck13349 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13349 := by decide +kernel

def row13349 : Integer.Sparse Key := [(key2372, -6), (key2385, 6), (key2400, -6), (key2432, 6), (key2466, 12), (key2475, -6), (key2498, -6)]

theorem rowCheck13349 : row13349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13349 := by decide +kernel

theorem rowEval13349 (x : Key → ℝ) : Integer.Sparse.eval row13349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13349, Integer.Sparse.eval_collectBalanced, rawRowCheck13349]

def rawRow13350 : Integer.Sparse Key := [(key2400, -2), (key2400, -2), (key2432, -2), (key2400, 6), (key2466, -2), (key2466, -2), (key2498, -2), (key2372, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2372, -2), (key2466, -2), (key2466, -2), (key2475, 6), (key2385, -2), (key2475, -2), (key2475, -2)]

theorem rawRowCheck13350 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form2 = rawRow13350 := by decide +kernel

def row13350 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13350 : row13350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13350 := by decide +kernel

theorem rowEval13350 (x : Key → ℝ) : Integer.Sparse.eval row13350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13350, Integer.Sparse.eval_collectBalanced, rawRowCheck13350]

def rawRow13351 : Integer.Sparse Key := [(key2400, -2), (key2432, -2), (key2400, -2), (key2400, 6), (key2466, -2), (key2498, -2), (key2466, -2), (key2466, 2), (key2498, 2), (key2372, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2466, -2), (key2372, -2), (key2466, -2), (key2475, 6), (key2475, -2), (key2385, -2), (key2475, -2)]

theorem rawRowCheck13351 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form2 = rawRow13351 := by decide +kernel

def row13351 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13351 : row13351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13351 := by decide +kernel

theorem rowEval13351 (x : Key → ℝ) : Integer.Sparse.eval row13351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13351, Integer.Sparse.eval_collectBalanced, rawRowCheck13351]

def rawRow13352 : Integer.Sparse Key := [(key2432, -2), (key2400, -2), (key2400, -2), (key2400, 6), (key2498, -2), (key2466, -2), (key2466, -2), (key2498, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2466, -2), (key2466, -2), (key2372, -2), (key2475, 6), (key2475, -2), (key2475, -2), (key2385, -2)]

theorem rawRowCheck13352 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form2 = rawRow13352 := by decide +kernel

def row13352 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13352 : row13352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13352 := by decide +kernel

theorem rowEval13352 (x : Key → ℝ) : Integer.Sparse.eval row13352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13352, Integer.Sparse.eval_collectBalanced, rawRowCheck13352]

def rawRow13353 : Integer.Sparse Key := [(key2466, -2), (key2466, -2), (key2475, -2), (key2498, 6), (key2372, -2), (key2372, -2), (key2385, -2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2475, 2), (key2432, -2), (key2498, -2), (key2498, -2), (key2372, 6), (key2400, -2), (key2466, -2), (key2466, -2)]

theorem rawRowCheck13353 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form2 = rawRow13353 := by decide +kernel

def row13353 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13353 : row13353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13353 := by decide +kernel

theorem rowEval13353 (x : Key → ℝ) : Integer.Sparse.eval row13353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13353, Integer.Sparse.eval_collectBalanced, rawRowCheck13353]

def rawRow13354 : Integer.Sparse Key := [(key2466, -2), (key2475, -2), (key2466, -2), (key2498, 6), (key2372, -2), (key2385, -2), (key2372, -2), (key2466, 2), (key2475, 2), (key2400, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2498, -2), (key2432, -2), (key2498, -2), (key2372, 6), (key2466, -2), (key2400, -2), (key2466, -2)]

theorem rawRowCheck13354 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form2 = rawRow13354 := by decide +kernel

def row13354 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13354 : row13354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13354 := by decide +kernel

theorem rowEval13354 (x : Key → ℝ) : Integer.Sparse.eval row13354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13354, Integer.Sparse.eval_collectBalanced, rawRowCheck13354]

def rawRow13355 : Integer.Sparse Key := [(key2475, -2), (key2466, -2), (key2466, -2), (key2498, 6), (key2385, -2), (key2372, -2), (key2372, -2), (key2475, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2400, 2), (key2498, -2), (key2498, -2), (key2432, -2), (key2372, 6), (key2466, -2), (key2466, -2), (key2400, -2)]

theorem rawRowCheck13355 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form2 = rawRow13355 := by decide +kernel

def row13355 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13355 : row13355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13355 := by decide +kernel

theorem rowEval13355 (x : Key → ℝ) : Integer.Sparse.eval row13355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13355, Integer.Sparse.eval_collectBalanced, rawRowCheck13355]

def rawRow13356 : Integer.Sparse Key := [(key2466, -2), (key2466, -2), (key2498, -2), (key2475, 6), (key2400, -2), (key2400, -2), (key2432, -2), (key2372, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2385, -2), (key2475, -2), (key2475, -2), (key2400, 6), (key2372, -2), (key2466, -2), (key2466, -2)]

theorem rawRowCheck13356 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form2 = rawRow13356 := by decide +kernel

def row13356 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13356 : row13356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13356 := by decide +kernel

theorem rowEval13356 (x : Key → ℝ) : Integer.Sparse.eval row13356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13356, Integer.Sparse.eval_collectBalanced, rawRowCheck13356]

def rawRow13357 : Integer.Sparse Key := [(key2466, -2), (key2498, -2), (key2466, -2), (key2475, 6), (key2400, -2), (key2432, -2), (key2400, -2), (key2466, 2), (key2498, 2), (key2372, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2475, -2), (key2385, -2), (key2475, -2), (key2400, 6), (key2466, -2), (key2372, -2), (key2466, -2)]

theorem rawRowCheck13357 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form2 = rawRow13357 := by decide +kernel

def row13357 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13357 : row13357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13357 := by decide +kernel

theorem rowEval13357 (x : Key → ℝ) : Integer.Sparse.eval row13357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13357, Integer.Sparse.eval_collectBalanced, rawRowCheck13357]

def rawRow13358 : Integer.Sparse Key := [(key2498, -2), (key2466, -2), (key2466, -2), (key2475, 6), (key2432, -2), (key2400, -2), (key2400, -2), (key2498, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2475, -2), (key2475, -2), (key2385, -2), (key2400, 6), (key2466, -2), (key2466, -2), (key2372, -2)]

theorem rawRowCheck13358 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form2 = rawRow13358 := by decide +kernel

def row13358 : Integer.Sparse Key := [(key2372, 2), (key2385, -2), (key2400, 2), (key2432, -2), (key2466, -4), (key2475, 2), (key2498, 2)]

theorem rowCheck13358 : row13358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13358 := by decide +kernel

theorem rowEval13358 (x : Key → ℝ) : Integer.Sparse.eval row13358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13358, Integer.Sparse.eval_collectBalanced, rawRowCheck13358]

def rawRow13359 : Integer.Sparse Key := [(key2466, -2), (key2475, -2), (key2498, -2), (key2466, 6), (key2466, -2), (key2475, -2), (key2498, -2), (key2372, 2), (key2385, 2), (key2400, 2), (key2475, 2), (key2432, 2), (key2498, 2), (key2372, -2), (key2400, -2), (key2466, -2), (key2466, 6), (key2372, -2), (key2400, -2), (key2466, -2)]

theorem rawRowCheck13359 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form2 = rawRow13359 := by decide +kernel

def row13359 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

theorem rowCheck13359 : row13359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13359 := by decide +kernel

theorem rowEval13359 (x : Key → ℝ) : Integer.Sparse.eval row13359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13359, Integer.Sparse.eval_collectBalanced, rawRowCheck13359]

def rawRow13360 : Integer.Sparse Key := [(key2475, -2), (key2466, -2), (key2498, -2), (key2466, 6), (key2475, -2), (key2466, -2), (key2498, -2), (key2385, 2), (key2372, 2), (key2475, 2), (key2400, 2), (key2498, 2), (key2432, 2), (key2372, -2), (key2466, -2), (key2400, -2), (key2466, 6), (key2372, -2), (key2466, -2), (key2400, -2)]

theorem rawRowCheck13360 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form2 = rawRow13360 := by decide +kernel

def row13360 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

theorem rowCheck13360 : row13360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13360 := by decide +kernel

theorem rowEval13360 (x : Key → ℝ) : Integer.Sparse.eval row13360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13360, Integer.Sparse.eval_collectBalanced, rawRowCheck13360]

def rawRow13361 : Integer.Sparse Key := [(key2466, -2), (key2498, -2), (key2475, -2), (key2466, 6), (key2466, -2), (key2498, -2), (key2475, -2), (key2400, 2), (key2432, 2), (key2372, 2), (key2498, 2), (key2385, 2), (key2475, 2), (key2400, -2), (key2372, -2), (key2466, -2), (key2466, 6), (key2400, -2), (key2372, -2), (key2466, -2)]

theorem rawRowCheck13361 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form2 = rawRow13361 := by decide +kernel

def row13361 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

theorem rowCheck13361 : row13361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13361 := by decide +kernel

theorem rowEval13361 (x : Key → ℝ) : Integer.Sparse.eval row13361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13361, Integer.Sparse.eval_collectBalanced, rawRowCheck13361]

def rawRow13362 : Integer.Sparse Key := [(key2498, -2), (key2466, -2), (key2475, -2), (key2466, 6), (key2498, -2), (key2466, -2), (key2475, -2), (key2432, 2), (key2400, 2), (key2498, 2), (key2372, 2), (key2475, 2), (key2385, 2), (key2400, -2), (key2466, -2), (key2372, -2), (key2466, 6), (key2400, -2), (key2466, -2), (key2372, -2)]

theorem rawRowCheck13362 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form2 = rawRow13362 := by decide +kernel

def row13362 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

theorem rowCheck13362 : row13362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13362 := by decide +kernel

theorem rowEval13362 (x : Key → ℝ) : Integer.Sparse.eval row13362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13362, Integer.Sparse.eval_collectBalanced, rawRowCheck13362]

def rawRow13363 : Integer.Sparse Key := [(key2475, -2), (key2498, -2), (key2466, -2), (key2466, 6), (key2475, -2), (key2498, -2), (key2466, -2), (key2475, 2), (key2498, 2), (key2385, 2), (key2432, 2), (key2372, 2), (key2400, 2), (key2466, -2), (key2372, -2), (key2400, -2), (key2466, 6), (key2466, -2), (key2372, -2), (key2400, -2)]

theorem rawRowCheck13363 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form2 = rawRow13363 := by decide +kernel

def row13363 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

theorem rowCheck13363 : row13363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13363 := by decide +kernel

theorem rowEval13363 (x : Key → ℝ) : Integer.Sparse.eval row13363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13363, Integer.Sparse.eval_collectBalanced, rawRowCheck13363]

def rawRow13364 : Integer.Sparse Key := [(key2498, -2), (key2475, -2), (key2466, -2), (key2466, 6), (key2498, -2), (key2475, -2), (key2466, -2), (key2498, 2), (key2475, 2), (key2432, 2), (key2385, 2), (key2400, 2), (key2372, 2), (key2466, -2), (key2400, -2), (key2372, -2), (key2466, 6), (key2466, -2), (key2400, -2), (key2372, -2)]

theorem rawRowCheck13364 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form2 = rawRow13364 := by decide +kernel

def row13364 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, -2), (key2432, 2), (key2466, 4), (key2475, -2), (key2498, -2)]

theorem rowCheck13364 : row13364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13364 := by decide +kernel

theorem rowEval13364 (x : Key → ℝ) : Integer.Sparse.eval row13364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13364, Integer.Sparse.eval_collectBalanced, rawRowCheck13364]

def rawRow13365 : Integer.Sparse Key := [(key2606, 6), (key2622, -2), (key2622, -2), (key2622, -2), (key2661, 6), (key2696, -2), (key2696, -2), (key2696, -2), (key2776, -2), (key2776, -2), (key2776, -2), (key2799, -2), (key2799, -2), (key2799, -2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck13365 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13365 := by decide +kernel

def row13365 : Integer.Sparse Key := [(key2606, 6), (key2622, -6), (key2661, 6), (key2696, -6), (key2776, -6), (key2799, -6), (key2849, 12)]

theorem rowCheck13365 : row13365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13365 := by decide +kernel

theorem rowEval13365 (x : Key → ℝ) : Integer.Sparse.eval row13365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13365, Integer.Sparse.eval_collectBalanced, rawRowCheck13365]

def rawRow13366 : Integer.Sparse Key := [(key2622, 6), (key2606, -2), (key2622, -2), (key2622, -2), (key2696, 6), (key2661, -2), (key2696, -2), (key2696, -2), (key2799, -2), (key2849, -2), (key2849, -2), (key2776, -2), (key2849, -2), (key2849, -2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck13366 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form3 = rawRow13366 := by decide +kernel

def row13366 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, 2), (key2849, -4)]

theorem rowCheck13366 : row13366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13366 := by decide +kernel

theorem rowEval13366 (x : Key → ℝ) : Integer.Sparse.eval row13366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13366, Integer.Sparse.eval_collectBalanced, rawRowCheck13366]

def rawRow13367 : Integer.Sparse Key := [(key2622, 6), (key2622, -2), (key2606, -2), (key2622, -2), (key2696, 6), (key2696, -2), (key2661, -2), (key2696, -2), (key2849, -2), (key2799, -2), (key2849, -2), (key2849, -2), (key2776, -2), (key2849, -2), (key2799, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2776, 2), (key2799, 2)]

theorem rawRowCheck13367 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form3 = rawRow13367 := by decide +kernel

def row13367 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, 2), (key2849, -4)]

theorem rowCheck13367 : row13367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13367 := by decide +kernel

theorem rowEval13367 (x : Key → ℝ) : Integer.Sparse.eval row13367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13367, Integer.Sparse.eval_collectBalanced, rawRowCheck13367]

def rawRow13368 : Integer.Sparse Key := [(key2622, 6), (key2622, -2), (key2622, -2), (key2606, -2), (key2696, 6), (key2696, -2), (key2696, -2), (key2661, -2), (key2849, -2), (key2849, -2), (key2799, -2), (key2849, -2), (key2849, -2), (key2776, -2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2799, 2), (key2776, 2)]

theorem rawRowCheck13368 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form3 = rawRow13368 := by decide +kernel

def row13368 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, 2), (key2849, -4)]

theorem rowCheck13368 : row13368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13368 := by decide +kernel

theorem rowEval13368 (x : Key → ℝ) : Integer.Sparse.eval row13368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13368, Integer.Sparse.eval_collectBalanced, rawRowCheck13368]

def rawRow13369 : Integer.Sparse Key := [(key2661, 6), (key2696, -2), (key2696, -2), (key2696, -2), (key2606, 6), (key2799, -2), (key2799, -2), (key2799, -2), (key2622, -2), (key2622, -2), (key2622, -2), (key2696, -2), (key2696, -2), (key2696, -2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck13369 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13369 := by decide +kernel

def row13369 : Integer.Sparse Key := [(key2606, 6), (key2622, -6), (key2661, 6), (key2696, -12), (key2799, -6), (key2849, 12)]

theorem rowCheck13369 : row13369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13369 := by decide +kernel

theorem rowEval13369 (x : Key → ℝ) : Integer.Sparse.eval row13369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13369, Integer.Sparse.eval_collectBalanced, rawRowCheck13369]

def rawRow13370 : Integer.Sparse Key := [(key2696, 6), (key2661, -2), (key2696, -2), (key2696, -2), (key2799, 6), (key2606, -2), (key2799, -2), (key2799, -2), (key2696, -2), (key2849, -2), (key2849, -2), (key2622, -2), (key2849, -2), (key2849, -2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck13370 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form3 = rawRow13370 := by decide +kernel

def row13370 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 4), (key2799, 2), (key2849, -4)]

theorem rowCheck13370 : row13370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13370 := by decide +kernel

theorem rowEval13370 (x : Key → ℝ) : Integer.Sparse.eval row13370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13370, Integer.Sparse.eval_collectBalanced, rawRowCheck13370]

def rawRow13371 : Integer.Sparse Key := [(key2696, 6), (key2696, -2), (key2661, -2), (key2696, -2), (key2799, 6), (key2799, -2), (key2606, -2), (key2799, -2), (key2849, -2), (key2696, -2), (key2849, -2), (key2849, -2), (key2622, -2), (key2849, -2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

theorem rawRowCheck13371 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form3 = rawRow13371 := by decide +kernel

def row13371 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 4), (key2799, 2), (key2849, -4)]

theorem rowCheck13371 : row13371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13371 := by decide +kernel

theorem rowEval13371 (x : Key → ℝ) : Integer.Sparse.eval row13371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13371, Integer.Sparse.eval_collectBalanced, rawRowCheck13371]

def rawRow13372 : Integer.Sparse Key := [(key2696, 6), (key2696, -2), (key2696, -2), (key2661, -2), (key2799, 6), (key2799, -2), (key2799, -2), (key2606, -2), (key2849, -2), (key2849, -2), (key2696, -2), (key2849, -2), (key2849, -2), (key2622, -2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

theorem rawRowCheck13372 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form3 = rawRow13372 := by decide +kernel

def row13372 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 4), (key2799, 2), (key2849, -4)]

theorem rowCheck13372 : row13372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13372 := by decide +kernel

theorem rowEval13372 (x : Key → ℝ) : Integer.Sparse.eval row13372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13372, Integer.Sparse.eval_collectBalanced, rawRowCheck13372]

def rawRow13373 : Integer.Sparse Key := [(key2776, 6), (key2799, -2), (key2849, -2), (key2849, -2), (key2622, 6), (key2696, -2), (key2849, -2), (key2849, -2), (key2606, -2), (key2622, -2), (key2622, -2), (key2661, -2), (key2696, -2), (key2696, -2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck13373 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form3 = rawRow13373 := by decide +kernel

def row13373 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, -6), (key2776, 10), (key2799, 2), (key2849, -4)]

theorem rowCheck13373 : row13373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13373 := by decide +kernel

theorem rowEval13373 (x : Key → ℝ) : Integer.Sparse.eval row13373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13373, Integer.Sparse.eval_collectBalanced, rawRowCheck13373]

def rawRow13374 : Integer.Sparse Key := [(key2776, 6), (key2849, -2), (key2799, -2), (key2849, -2), (key2622, 6), (key2849, -2), (key2696, -2), (key2849, -2), (key2622, -2), (key2606, -2), (key2622, -2), (key2696, -2), (key2661, -2), (key2696, -2), (key2799, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2776, 2), (key2799, 2)]

theorem rawRowCheck13374 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form3 = rawRow13374 := by decide +kernel

def row13374 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, -6), (key2776, 10), (key2799, 2), (key2849, -4)]

theorem rowCheck13374 : row13374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13374 := by decide +kernel

theorem rowEval13374 (x : Key → ℝ) : Integer.Sparse.eval row13374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13374, Integer.Sparse.eval_collectBalanced, rawRowCheck13374]

def rawRow13375 : Integer.Sparse Key := [(key2776, 6), (key2849, -2), (key2849, -2), (key2799, -2), (key2622, 6), (key2849, -2), (key2849, -2), (key2696, -2), (key2622, -2), (key2622, -2), (key2606, -2), (key2696, -2), (key2696, -2), (key2661, -2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2799, 2), (key2776, 2)]

theorem rawRowCheck13375 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form3 = rawRow13375 := by decide +kernel

def row13375 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, -6), (key2776, 10), (key2799, 2), (key2849, -4)]

theorem rowCheck13375 : row13375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13375 := by decide +kernel

theorem rowEval13375 (x : Key → ℝ) : Integer.Sparse.eval row13375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13375, Integer.Sparse.eval_collectBalanced, rawRowCheck13375]

def rawRow13376 : Integer.Sparse Key := [(key2799, 6), (key2776, -2), (key2849, -2), (key2849, -2), (key2696, 6), (key2622, -2), (key2849, -2), (key2849, -2), (key2661, -2), (key2696, -2), (key2696, -2), (key2606, -2), (key2799, -2), (key2799, -2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck13376 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form3 = rawRow13376 := by decide +kernel

def row13376 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 6), (key2776, -2), (key2799, 2), (key2849, -4)]

theorem rowCheck13376 : row13376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13376 := by decide +kernel

theorem rowEval13376 (x : Key → ℝ) : Integer.Sparse.eval row13376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13376, Integer.Sparse.eval_collectBalanced, rawRowCheck13376]

def rawRow13377 : Integer.Sparse Key := [(key2799, 6), (key2849, -2), (key2776, -2), (key2849, -2), (key2696, 6), (key2849, -2), (key2622, -2), (key2849, -2), (key2696, -2), (key2661, -2), (key2696, -2), (key2799, -2), (key2606, -2), (key2799, -2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

theorem rawRowCheck13377 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form3 = rawRow13377 := by decide +kernel

def row13377 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 6), (key2776, -2), (key2799, 2), (key2849, -4)]

theorem rowCheck13377 : row13377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13377 := by decide +kernel

theorem rowEval13377 (x : Key → ℝ) : Integer.Sparse.eval row13377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13377, Integer.Sparse.eval_collectBalanced, rawRowCheck13377]

def rawRow13378 : Integer.Sparse Key := [(key2799, 6), (key2849, -2), (key2849, -2), (key2776, -2), (key2696, 6), (key2849, -2), (key2849, -2), (key2622, -2), (key2696, -2), (key2696, -2), (key2661, -2), (key2799, -2), (key2799, -2), (key2606, -2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

theorem rawRowCheck13378 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form3 = rawRow13378 := by decide +kernel

def row13378 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, -2), (key2696, 6), (key2776, -2), (key2799, 2), (key2849, -4)]

theorem rowCheck13378 : row13378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13378 := by decide +kernel

theorem rowEval13378 (x : Key → ℝ) : Integer.Sparse.eval row13378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13378, Integer.Sparse.eval_collectBalanced, rawRowCheck13378]

def rawRow13379 : Integer.Sparse Key := [(key2849, 6), (key2776, -2), (key2799, -2), (key2849, -2), (key2849, 6), (key2622, -2), (key2696, -2), (key2849, -2), (key2776, -2), (key2799, -2), (key2849, -2), (key2622, -2), (key2696, -2), (key2849, -2), (key2606, 2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, 2), (key2799, 2)]

theorem rawRowCheck13379 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form3 = rawRow13379 := by decide +kernel

def row13379 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, -2), (key2799, -2), (key2849, 4)]

theorem rowCheck13379 : row13379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13379 := by decide +kernel

theorem rowEval13379 (x : Key → ℝ) : Integer.Sparse.eval row13379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13379, Integer.Sparse.eval_collectBalanced, rawRowCheck13379]

def rawRow13380 : Integer.Sparse Key := [(key2849, 6), (key2776, -2), (key2849, -2), (key2799, -2), (key2849, 6), (key2622, -2), (key2849, -2), (key2696, -2), (key2776, -2), (key2849, -2), (key2799, -2), (key2622, -2), (key2849, -2), (key2696, -2), (key2622, 2), (key2606, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2776, 2)]

theorem rawRowCheck13380 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form3 = rawRow13380 := by decide +kernel

def row13380 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, -2), (key2799, -2), (key2849, 4)]

theorem rowCheck13380 : row13380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13380 := by decide +kernel

theorem rowEval13380 (x : Key → ℝ) : Integer.Sparse.eval row13380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13380, Integer.Sparse.eval_collectBalanced, rawRowCheck13380]

def rawRow13381 : Integer.Sparse Key := [(key2849, 6), (key2799, -2), (key2776, -2), (key2849, -2), (key2849, 6), (key2696, -2), (key2622, -2), (key2849, -2), (key2799, -2), (key2776, -2), (key2849, -2), (key2696, -2), (key2622, -2), (key2849, -2), (key2661, 2), (key2696, 2), (key2606, 2), (key2799, 2), (key2622, 2), (key2696, 2)]

theorem rawRowCheck13381 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form3 = rawRow13381 := by decide +kernel

def row13381 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, -4), (key2799, -2), (key2849, 4)]

theorem rowCheck13381 : row13381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13381 := by decide +kernel

theorem rowEval13381 (x : Key → ℝ) : Integer.Sparse.eval row13381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13381, Integer.Sparse.eval_collectBalanced, rawRowCheck13381]

def rawRow13382 : Integer.Sparse Key := [(key2849, 6), (key2799, -2), (key2849, -2), (key2776, -2), (key2849, 6), (key2696, -2), (key2849, -2), (key2622, -2), (key2799, -2), (key2849, -2), (key2776, -2), (key2696, -2), (key2849, -2), (key2622, -2), (key2696, 2), (key2661, 2), (key2799, 2), (key2606, 2), (key2696, 2), (key2622, 2)]

theorem rawRowCheck13382 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form3 = rawRow13382 := by decide +kernel

def row13382 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, -4), (key2799, -2), (key2849, 4)]

theorem rowCheck13382 : row13382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13382 := by decide +kernel

theorem rowEval13382 (x : Key → ℝ) : Integer.Sparse.eval row13382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13382, Integer.Sparse.eval_collectBalanced, rawRowCheck13382]

def rawRow13383 : Integer.Sparse Key := [(key2849, 6), (key2849, -2), (key2776, -2), (key2799, -2), (key2849, 6), (key2849, -2), (key2622, -2), (key2696, -2), (key2849, -2), (key2776, -2), (key2799, -2), (key2849, -2), (key2622, -2), (key2696, -2), (key2776, 2), (key2799, 2), (key2622, 2), (key2696, 2), (key2606, 2), (key2661, 2)]

theorem rawRowCheck13383 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form3 = rawRow13383 := by decide +kernel

def row13383 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, -2), (key2799, -2), (key2849, 4)]

theorem rowCheck13383 : row13383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13383 := by decide +kernel

theorem rowEval13383 (x : Key → ℝ) : Integer.Sparse.eval row13383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13383, Integer.Sparse.eval_collectBalanced, rawRowCheck13383]

def rawRow13384 : Integer.Sparse Key := [(key2849, 6), (key2849, -2), (key2799, -2), (key2776, -2), (key2849, 6), (key2849, -2), (key2696, -2), (key2622, -2), (key2849, -2), (key2799, -2), (key2776, -2), (key2849, -2), (key2696, -2), (key2622, -2), (key2799, 2), (key2776, 2), (key2696, 2), (key2622, 2), (key2661, 2), (key2606, 2)]

theorem rawRowCheck13384 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form3 = rawRow13384 := by decide +kernel

def row13384 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, -2), (key2799, -2), (key2849, 4)]

theorem rowCheck13384 : row13384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13384 := by decide +kernel

theorem rowEval13384 (x : Key → ℝ) : Integer.Sparse.eval row13384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form3) x := by
  rw [rowCheck13384, Integer.Sparse.eval_collectBalanced, rawRowCheck13384]

def rawRow13385 : Integer.Sparse Key := [(key1090, 4), (key1090, 4), (key1168, 4), (key1090, -2), (key1097, -2), (key1090, -2), (key1168, -2), (key1097, -2), (key1168, -2), (key1180, -2), (key1182, -2), (key1180, -2), (key1219, -2), (key1182, -2), (key1219, -2), (key1182, 4), (key1182, 4), (key1219, 4)]

theorem rawRowCheck13385 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13385 := by decide +kernel

def row13385 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13385 : row13385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13385 := by decide +kernel

theorem rowEval13385 (x : Key → ℝ) : Integer.Sparse.eval row13385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13385, Integer.Sparse.eval_collectBalanced, rawRowCheck13385]

def rawRow13386 : Integer.Sparse Key := [(key1090, 4), (key1168, 4), (key1090, 4), (key1097, -2), (key1090, -2), (key1168, -2), (key1090, -2), (key1168, -2), (key1097, -2), (key1182, -2), (key1180, -2), (key1219, -2), (key1180, -2), (key1219, -2), (key1182, -2), (key1182, 4), (key1219, 4), (key1182, 4)]

theorem rawRowCheck13386 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13386 := by decide +kernel

def row13386 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13386 : row13386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13386 := by decide +kernel

theorem rowEval13386 (x : Key → ℝ) : Integer.Sparse.eval row13386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13386, Integer.Sparse.eval_collectBalanced, rawRowCheck13386]

def rawRow13387 : Integer.Sparse Key := [(key1168, 4), (key1090, 4), (key1090, 4), (key1168, -2), (key1168, -2), (key1097, -2), (key1097, -2), (key1090, -2), (key1090, -2), (key1219, -2), (key1219, -2), (key1182, -2), (key1182, -2), (key1180, -2), (key1180, -2), (key1219, 4), (key1182, 4), (key1182, 4)]

theorem rawRowCheck13387 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13387 := by decide +kernel

def row13387 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13387 : row13387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13387 := by decide +kernel

theorem rowEval13387 (x : Key → ℝ) : Integer.Sparse.eval row13387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13387, Integer.Sparse.eval_collectBalanced, rawRowCheck13387]

def rawRow13388 : Integer.Sparse Key := [(key1097, 4), (key1097, 4), (key1097, 4), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1180, 4), (key1180, 4), (key1180, 4)]

theorem rawRowCheck13388 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13388 := by decide +kernel

def row13388 : Integer.Sparse Key := [(key1090, -12), (key1097, 12), (key1180, 12), (key1182, -12)]

theorem rowCheck13388 : row13388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13388 := by decide +kernel

theorem rowEval13388 (x : Key → ℝ) : Integer.Sparse.eval row13388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13388, Integer.Sparse.eval_collectBalanced, rawRowCheck13388]

def rawRow13389 : Integer.Sparse Key := [(key1090, 4), (key1090, 4), (key1168, 4), (key1180, -2), (key1182, -2), (key1180, -2), (key1219, -2), (key1182, -2), (key1219, -2), (key1090, -2), (key1097, -2), (key1090, -2), (key1168, -2), (key1097, -2), (key1168, -2), (key1182, 4), (key1182, 4), (key1219, 4)]

theorem rawRowCheck13389 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13389 := by decide +kernel

def row13389 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13389 : row13389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13389 := by decide +kernel

theorem rowEval13389 (x : Key → ℝ) : Integer.Sparse.eval row13389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13389, Integer.Sparse.eval_collectBalanced, rawRowCheck13389]

def rawRow13390 : Integer.Sparse Key := [(key1090, 4), (key1168, 4), (key1090, 4), (key1182, -2), (key1180, -2), (key1219, -2), (key1180, -2), (key1219, -2), (key1182, -2), (key1097, -2), (key1090, -2), (key1168, -2), (key1090, -2), (key1168, -2), (key1097, -2), (key1182, 4), (key1219, 4), (key1182, 4)]

theorem rawRowCheck13390 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13390 := by decide +kernel

def row13390 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13390 : row13390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13390 := by decide +kernel

theorem rowEval13390 (x : Key → ℝ) : Integer.Sparse.eval row13390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13390, Integer.Sparse.eval_collectBalanced, rawRowCheck13390]

def rawRow13391 : Integer.Sparse Key := [(key1168, 4), (key1090, 4), (key1090, 4), (key1219, -2), (key1219, -2), (key1182, -2), (key1182, -2), (key1180, -2), (key1180, -2), (key1168, -2), (key1168, -2), (key1097, -2), (key1097, -2), (key1090, -2), (key1090, -2), (key1219, 4), (key1182, 4), (key1182, 4)]

theorem rawRowCheck13391 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13391 := by decide +kernel

def row13391 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13391 : row13391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13391 := by decide +kernel

theorem rowEval13391 (x : Key → ℝ) : Integer.Sparse.eval row13391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13391, Integer.Sparse.eval_collectBalanced, rawRowCheck13391]

def rawRow13392 : Integer.Sparse Key := [(key976, 4), (key1180, 4), (key1219, 4), (key976, -2), (key983, -2), (key1090, -2), (key1168, -2), (key1182, -2), (key1219, -2), (key976, -2), (key983, -2), (key1090, -2), (key1168, -2), (key1182, -2), (key1219, -2), (key983, 4), (key1097, 4), (key1168, 4)]

theorem rawRowCheck13392 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13392 := by decide +kernel

def row13392 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

theorem rowCheck13392 : row13392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13392 := by decide +kernel

theorem rowEval13392 (x : Key → ℝ) : Integer.Sparse.eval row13392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13392, Integer.Sparse.eval_collectBalanced, rawRowCheck13392]

def rawRow13393 : Integer.Sparse Key := [(key976, 4), (key1219, 4), (key1180, 4), (key983, -2), (key976, -2), (key1168, -2), (key1090, -2), (key1219, -2), (key1182, -2), (key983, -2), (key976, -2), (key1168, -2), (key1090, -2), (key1219, -2), (key1182, -2), (key983, 4), (key1168, 4), (key1097, 4)]

theorem rawRowCheck13393 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13393 := by decide +kernel

def row13393 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

theorem rowCheck13393 : row13393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13393 := by decide +kernel

theorem rowEval13393 (x : Key → ℝ) : Integer.Sparse.eval row13393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13393, Integer.Sparse.eval_collectBalanced, rawRowCheck13393]

def rawRow13394 : Integer.Sparse Key := [(key1180, 4), (key976, 4), (key1219, 4), (key1090, -2), (key1182, -2), (key976, -2), (key1219, -2), (key983, -2), (key1168, -2), (key1090, -2), (key1182, -2), (key976, -2), (key1219, -2), (key983, -2), (key1168, -2), (key1097, 4), (key983, 4), (key1168, 4)]

theorem rawRowCheck13394 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13394 := by decide +kernel

def row13394 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

theorem rowCheck13394 : row13394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13394 := by decide +kernel

theorem rowEval13394 (x : Key → ℝ) : Integer.Sparse.eval row13394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13394, Integer.Sparse.eval_collectBalanced, rawRowCheck13394]

def rawRow13395 : Integer.Sparse Key := [(key1180, 4), (key1219, 4), (key976, 4), (key1182, -2), (key1090, -2), (key1219, -2), (key976, -2), (key1168, -2), (key983, -2), (key1182, -2), (key1090, -2), (key1219, -2), (key976, -2), (key1168, -2), (key983, -2), (key1097, 4), (key1168, 4), (key983, 4)]

theorem rawRowCheck13395 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13395 := by decide +kernel

def row13395 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

theorem rowCheck13395 : row13395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13395 := by decide +kernel

theorem rowEval13395 (x : Key → ℝ) : Integer.Sparse.eval row13395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13395, Integer.Sparse.eval_collectBalanced, rawRowCheck13395]

def rawRow13396 : Integer.Sparse Key := [(key1219, 4), (key976, 4), (key1180, 4), (key1168, -2), (key1219, -2), (key983, -2), (key1182, -2), (key976, -2), (key1090, -2), (key1168, -2), (key1219, -2), (key983, -2), (key1182, -2), (key976, -2), (key1090, -2), (key1168, 4), (key983, 4), (key1097, 4)]

theorem rawRowCheck13396 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13396 := by decide +kernel

def row13396 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

theorem rowCheck13396 : row13396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13396 := by decide +kernel

theorem rowEval13396 (x : Key → ℝ) : Integer.Sparse.eval row13396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13396, Integer.Sparse.eval_collectBalanced, rawRowCheck13396]

def rawRow13397 : Integer.Sparse Key := [(key1219, 4), (key1180, 4), (key976, 4), (key1219, -2), (key1168, -2), (key1182, -2), (key983, -2), (key1090, -2), (key976, -2), (key1219, -2), (key1168, -2), (key1182, -2), (key983, -2), (key1090, -2), (key976, -2), (key1168, 4), (key1097, 4), (key983, 4)]

theorem rawRowCheck13397 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13397 := by decide +kernel

def row13397 : Integer.Sparse Key := [(key1090, -4), (key1097, 4), (key1180, 4), (key1182, -4)]

theorem rowCheck13397 : row13397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13397 := by decide +kernel

theorem rowEval13397 (x : Key → ℝ) : Integer.Sparse.eval row13397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13397, Integer.Sparse.eval_collectBalanced, rawRowCheck13397]

def rawRow13398 : Integer.Sparse Key := [(key983, 4), (key1182, 4), (key1182, 4), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key983, -2), (key983, -2), (key1097, -2), (key1097, -2), (key1182, -2), (key1182, -2), (key976, 4), (key1090, 4), (key1090, 4)]

theorem rawRowCheck13398 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13398 := by decide +kernel

def row13398 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13398 : row13398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13398 := by decide +kernel

theorem rowEval13398 (x : Key → ℝ) : Integer.Sparse.eval row13398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13398, Integer.Sparse.eval_collectBalanced, rawRowCheck13398]

def rawRow13399 : Integer.Sparse Key := [(key1182, 4), (key983, 4), (key1182, 4), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1097, -2), (key1182, -2), (key983, -2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, 4), (key976, 4), (key1090, 4)]

theorem rawRowCheck13399 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13399 := by decide +kernel

def row13399 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13399 : row13399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13399 := by decide +kernel

theorem rowEval13399 (x : Key → ℝ) : Integer.Sparse.eval row13399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13399, Integer.Sparse.eval_collectBalanced, rawRowCheck13399]

def rawRow13400 : Integer.Sparse Key := [(key1182, 4), (key1182, 4), (key983, 4), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1182, -2), (key1097, -2), (key1182, -2), (key983, -2), (key1097, -2), (key983, -2), (key1090, 4), (key1090, 4), (key976, 4)]

theorem rawRowCheck13400 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13400 := by decide +kernel

def row13400 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13400 : row13400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13400 := by decide +kernel

theorem rowEval13400 (x : Key → ℝ) : Integer.Sparse.eval row13400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13400, Integer.Sparse.eval_collectBalanced, rawRowCheck13400]

def rawRow13401 : Integer.Sparse Key := [(key1097, 4), (key1097, 4), (key1097, 4), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1182, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1180, 4), (key1180, 4), (key1180, 4)]

theorem rawRowCheck13401 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13401 := by decide +kernel

def row13401 : Integer.Sparse Key := [(key1090, -12), (key1097, 12), (key1180, 12), (key1182, -12)]

theorem rowCheck13401 : row13401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13401 := by decide +kernel

theorem rowEval13401 (x : Key → ℝ) : Integer.Sparse.eval row13401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13401, Integer.Sparse.eval_collectBalanced, rawRowCheck13401]

def rawRow13402 : Integer.Sparse Key := [(key983, 4), (key1182, 4), (key1182, 4), (key983, -2), (key983, -2), (key1097, -2), (key1097, -2), (key1182, -2), (key1182, -2), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key976, 4), (key1090, 4), (key1090, 4)]

theorem rawRowCheck13402 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13402 := by decide +kernel

def row13402 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13402 : row13402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13402 := by decide +kernel

theorem rowEval13402 (x : Key → ℝ) : Integer.Sparse.eval row13402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13402, Integer.Sparse.eval_collectBalanced, rawRowCheck13402]

def rawRow13403 : Integer.Sparse Key := [(key1182, 4), (key983, 4), (key1182, 4), (key1097, -2), (key1182, -2), (key983, -2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1090, 4), (key976, 4), (key1090, 4)]

theorem rawRowCheck13403 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13403 := by decide +kernel

def row13403 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13403 : row13403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13403 := by decide +kernel

theorem rowEval13403 (x : Key → ℝ) : Integer.Sparse.eval row13403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13403, Integer.Sparse.eval_collectBalanced, rawRowCheck13403]

def rawRow13404 : Integer.Sparse Key := [(key1182, 4), (key1182, 4), (key983, 4), (key1182, -2), (key1097, -2), (key1182, -2), (key983, -2), (key1097, -2), (key983, -2), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1090, 4), (key1090, 4), (key976, 4)]

theorem rawRowCheck13404 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13404 := by decide +kernel

def row13404 : Integer.Sparse Key := [(key1090, 4), (key1097, -4), (key1180, -4), (key1182, 4)]

theorem rowCheck13404 : row13404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13404 := by decide +kernel

theorem rowEval13404 (x : Key → ℝ) : Integer.Sparse.eval row13404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13404, Integer.Sparse.eval_collectBalanced, rawRowCheck13404]

def rawRow13405 : Integer.Sparse Key := [(key2, -2), (key6, -2), (key6, -2), (key6, 6), (key85, -2), (key89, -2), (key89, -2), (key85, 2), (key89, 2), (key85, 2), (key166, 2), (key89, 2), (key166, 2), (key89, -2), (key89, -2), (key166, -2), (key150, 6), (key150, -2), (key150, -2), (key186, -2)]

theorem rawRowCheck13405 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13405 := by decide +kernel

def row13405 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13405 : row13405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13405 := by decide +kernel

theorem rowEval13405 (x : Key → ℝ) : Integer.Sparse.eval row13405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13405, Integer.Sparse.eval_collectBalanced, rawRowCheck13405]

def rawRow13406 : Integer.Sparse Key := [(key6, -2), (key2, -2), (key6, -2), (key6, 6), (key89, -2), (key85, -2), (key89, -2), (key89, 2), (key85, 2), (key166, 2), (key85, 2), (key166, 2), (key89, 2), (key89, -2), (key166, -2), (key89, -2), (key150, 6), (key150, -2), (key186, -2), (key150, -2)]

theorem rawRowCheck13406 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13406 := by decide +kernel

def row13406 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13406 : row13406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13406 := by decide +kernel

theorem rowEval13406 (x : Key → ℝ) : Integer.Sparse.eval row13406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13406, Integer.Sparse.eval_collectBalanced, rawRowCheck13406]

def rawRow13407 : Integer.Sparse Key := [(key6, -2), (key6, -2), (key2, -2), (key6, 6), (key89, -2), (key89, -2), (key85, -2), (key166, 2), (key166, 2), (key89, 2), (key89, 2), (key85, 2), (key85, 2), (key166, -2), (key89, -2), (key89, -2), (key150, 6), (key186, -2), (key150, -2), (key150, -2)]

theorem rawRowCheck13407 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13407 := by decide +kernel

def row13407 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13407 : row13407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13407 := by decide +kernel

theorem rowEval13407 (x : Key → ℝ) : Integer.Sparse.eval row13407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13407, Integer.Sparse.eval_collectBalanced, rawRowCheck13407]

def rawRow13408 : Integer.Sparse Key := [(key6, -2), (key6, -2), (key6, -2), (key2, 6), (key166, -2), (key166, -2), (key166, -2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key85, -2), (key85, -2), (key85, -2), (key186, 6), (key150, -2), (key150, -2), (key150, -2)]

theorem rawRowCheck13408 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13408 := by decide +kernel

def row13408 : Integer.Sparse Key := [(key2, 6), (key6, -6), (key85, -6), (key89, 12), (key150, -6), (key166, -6), (key186, 6)]

theorem rowCheck13408 : row13408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13408 := by decide +kernel

theorem rowEval13408 (x : Key → ℝ) : Integer.Sparse.eval row13408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13408, Integer.Sparse.eval_collectBalanced, rawRowCheck13408]

def rawRow13409 : Integer.Sparse Key := [(key85, -2), (key89, -2), (key89, -2), (key150, 6), (key2, -2), (key6, -2), (key6, -2), (key85, 2), (key89, 2), (key85, 2), (key166, 2), (key89, 2), (key166, 2), (key150, -2), (key150, -2), (key186, -2), (key6, 6), (key89, -2), (key89, -2), (key166, -2)]

theorem rawRowCheck13409 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13409 := by decide +kernel

def row13409 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13409 : row13409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13409 := by decide +kernel

theorem rowEval13409 (x : Key → ℝ) : Integer.Sparse.eval row13409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13409, Integer.Sparse.eval_collectBalanced, rawRowCheck13409]

def rawRow13410 : Integer.Sparse Key := [(key89, -2), (key85, -2), (key89, -2), (key150, 6), (key6, -2), (key2, -2), (key6, -2), (key89, 2), (key85, 2), (key166, 2), (key85, 2), (key166, 2), (key89, 2), (key150, -2), (key186, -2), (key150, -2), (key6, 6), (key89, -2), (key166, -2), (key89, -2)]

theorem rawRowCheck13410 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13410 := by decide +kernel

def row13410 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13410 : row13410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13410 := by decide +kernel

theorem rowEval13410 (x : Key → ℝ) : Integer.Sparse.eval row13410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13410, Integer.Sparse.eval_collectBalanced, rawRowCheck13410]

def rawRow13411 : Integer.Sparse Key := [(key89, -2), (key89, -2), (key85, -2), (key150, 6), (key6, -2), (key6, -2), (key2, -2), (key166, 2), (key166, 2), (key89, 2), (key89, 2), (key85, 2), (key85, 2), (key186, -2), (key150, -2), (key150, -2), (key6, 6), (key166, -2), (key89, -2), (key89, -2)]

theorem rawRowCheck13411 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13411 := by decide +kernel

def row13411 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13411 : row13411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13411 := by decide +kernel

theorem rowEval13411 (x : Key → ℝ) : Integer.Sparse.eval row13411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13411, Integer.Sparse.eval_collectBalanced, rawRowCheck13411]

def rawRow13412 : Integer.Sparse Key := [(key85, -2), (key89, -2), (key150, -2), (key89, 6), (key85, -2), (key89, -2), (key150, -2), (key2, 2), (key6, 2), (key85, 2), (key166, 2), (key150, 2), (key186, 2), (key6, -2), (key89, -2), (key166, -2), (key89, 6), (key6, -2), (key89, -2), (key166, -2)]

theorem rawRowCheck13412 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13412 := by decide +kernel

def row13412 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck13412 : row13412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13412 := by decide +kernel

theorem rowEval13412 (x : Key → ℝ) : Integer.Sparse.eval row13412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13412, Integer.Sparse.eval_collectBalanced, rawRowCheck13412]

def rawRow13413 : Integer.Sparse Key := [(key89, -2), (key85, -2), (key150, -2), (key89, 6), (key89, -2), (key85, -2), (key150, -2), (key6, 2), (key2, 2), (key166, 2), (key85, 2), (key186, 2), (key150, 2), (key6, -2), (key166, -2), (key89, -2), (key89, 6), (key6, -2), (key166, -2), (key89, -2)]

theorem rawRowCheck13413 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13413 := by decide +kernel

def row13413 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck13413 : row13413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13413 := by decide +kernel

theorem rowEval13413 (x : Key → ℝ) : Integer.Sparse.eval row13413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13413, Integer.Sparse.eval_collectBalanced, rawRowCheck13413]

def rawRow13414 : Integer.Sparse Key := [(key85, -2), (key150, -2), (key89, -2), (key89, 6), (key85, -2), (key150, -2), (key89, -2), (key85, 2), (key150, 2), (key2, 2), (key186, 2), (key6, 2), (key166, 2), (key89, -2), (key6, -2), (key166, -2), (key89, 6), (key89, -2), (key6, -2), (key166, -2)]

theorem rawRowCheck13414 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13414 := by decide +kernel

def row13414 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck13414 : row13414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13414 := by decide +kernel

theorem rowEval13414 (x : Key → ℝ) : Integer.Sparse.eval row13414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13414, Integer.Sparse.eval_collectBalanced, rawRowCheck13414]

def rawRow13415 : Integer.Sparse Key := [(key150, -2), (key85, -2), (key89, -2), (key89, 6), (key150, -2), (key85, -2), (key89, -2), (key150, 2), (key85, 2), (key186, 2), (key2, 2), (key166, 2), (key6, 2), (key89, -2), (key166, -2), (key6, -2), (key89, 6), (key89, -2), (key166, -2), (key6, -2)]

theorem rawRowCheck13415 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13415 := by decide +kernel

def row13415 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck13415 : row13415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13415 := by decide +kernel

theorem rowEval13415 (x : Key → ℝ) : Integer.Sparse.eval row13415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13415, Integer.Sparse.eval_collectBalanced, rawRowCheck13415]

def rawRow13416 : Integer.Sparse Key := [(key89, -2), (key150, -2), (key85, -2), (key89, 6), (key89, -2), (key150, -2), (key85, -2), (key166, 2), (key186, 2), (key6, 2), (key150, 2), (key2, 2), (key85, 2), (key166, -2), (key6, -2), (key89, -2), (key89, 6), (key166, -2), (key6, -2), (key89, -2)]

theorem rawRowCheck13416 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13416 := by decide +kernel

def row13416 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck13416 : row13416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13416 := by decide +kernel

theorem rowEval13416 (x : Key → ℝ) : Integer.Sparse.eval row13416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13416, Integer.Sparse.eval_collectBalanced, rawRowCheck13416]

def rawRow13417 : Integer.Sparse Key := [(key150, -2), (key89, -2), (key85, -2), (key89, 6), (key150, -2), (key89, -2), (key85, -2), (key186, 2), (key166, 2), (key150, 2), (key6, 2), (key85, 2), (key2, 2), (key166, -2), (key89, -2), (key6, -2), (key89, 6), (key166, -2), (key89, -2), (key6, -2)]

theorem rawRowCheck13417 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13417 := by decide +kernel

def row13417 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key89, 4), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck13417 : row13417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13417 := by decide +kernel

theorem rowEval13417 (x : Key → ℝ) : Integer.Sparse.eval row13417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13417, Integer.Sparse.eval_collectBalanced, rawRowCheck13417]

def rawRow13418 : Integer.Sparse Key := [(key89, -2), (key89, -2), (key150, -2), (key85, 6), (key166, -2), (key166, -2), (key186, -2), (key6, 2), (key6, 2), (key89, 2), (key89, 2), (key150, 2), (key150, 2), (key2, -2), (key85, -2), (key85, -2), (key166, 6), (key6, -2), (key89, -2), (key89, -2)]

theorem rawRowCheck13418 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13418 := by decide +kernel

def row13418 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13418 : row13418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13418 := by decide +kernel

theorem rowEval13418 (x : Key → ℝ) : Integer.Sparse.eval row13418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13418, Integer.Sparse.eval_collectBalanced, rawRowCheck13418]

def rawRow13419 : Integer.Sparse Key := [(key89, -2), (key150, -2), (key89, -2), (key85, 6), (key166, -2), (key186, -2), (key166, -2), (key89, 2), (key150, 2), (key6, 2), (key150, 2), (key6, 2), (key89, 2), (key85, -2), (key2, -2), (key85, -2), (key166, 6), (key89, -2), (key6, -2), (key89, -2)]

theorem rawRowCheck13419 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13419 := by decide +kernel

def row13419 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13419 : row13419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13419 := by decide +kernel

theorem rowEval13419 (x : Key → ℝ) : Integer.Sparse.eval row13419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13419, Integer.Sparse.eval_collectBalanced, rawRowCheck13419]

def rawRow13420 : Integer.Sparse Key := [(key150, -2), (key89, -2), (key89, -2), (key85, 6), (key186, -2), (key166, -2), (key166, -2), (key150, 2), (key89, 2), (key150, 2), (key6, 2), (key89, 2), (key6, 2), (key85, -2), (key85, -2), (key2, -2), (key166, 6), (key89, -2), (key89, -2), (key6, -2)]

theorem rawRowCheck13420 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13420 := by decide +kernel

def row13420 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13420 : row13420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13420 := by decide +kernel

theorem rowEval13420 (x : Key → ℝ) : Integer.Sparse.eval row13420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13420, Integer.Sparse.eval_collectBalanced, rawRowCheck13420]

def rawRow13421 : Integer.Sparse Key := [(key166, -2), (key166, -2), (key166, -2), (key186, 6), (key6, -2), (key6, -2), (key6, -2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key89, 2), (key150, -2), (key150, -2), (key150, -2), (key2, 6), (key85, -2), (key85, -2), (key85, -2)]

theorem rawRowCheck13421 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13421 := by decide +kernel

def row13421 : Integer.Sparse Key := [(key2, 6), (key6, -6), (key85, -6), (key89, 12), (key150, -6), (key166, -6), (key186, 6)]

theorem rowCheck13421 : row13421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13421 := by decide +kernel

theorem rowEval13421 (x : Key → ℝ) : Integer.Sparse.eval row13421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13421, Integer.Sparse.eval_collectBalanced, rawRowCheck13421]

def rawRow13422 : Integer.Sparse Key := [(key166, -2), (key166, -2), (key186, -2), (key166, 6), (key89, -2), (key89, -2), (key150, -2), (key6, 2), (key6, 2), (key89, 2), (key89, 2), (key150, 2), (key150, 2), (key6, -2), (key89, -2), (key89, -2), (key85, 6), (key2, -2), (key85, -2), (key85, -2)]

theorem rawRowCheck13422 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13422 := by decide +kernel

def row13422 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13422 : row13422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13422 := by decide +kernel

theorem rowEval13422 (x : Key → ℝ) : Integer.Sparse.eval row13422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13422, Integer.Sparse.eval_collectBalanced, rawRowCheck13422]

def rawRow13423 : Integer.Sparse Key := [(key166, -2), (key186, -2), (key166, -2), (key166, 6), (key89, -2), (key150, -2), (key89, -2), (key89, 2), (key150, 2), (key6, 2), (key150, 2), (key6, 2), (key89, 2), (key89, -2), (key6, -2), (key89, -2), (key85, 6), (key85, -2), (key2, -2), (key85, -2)]

theorem rawRowCheck13423 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13423 := by decide +kernel

def row13423 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13423 : row13423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13423 := by decide +kernel

theorem rowEval13423 (x : Key → ℝ) : Integer.Sparse.eval row13423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13423, Integer.Sparse.eval_collectBalanced, rawRowCheck13423]

def rawRow13424 : Integer.Sparse Key := [(key186, -2), (key166, -2), (key166, -2), (key166, 6), (key150, -2), (key89, -2), (key89, -2), (key150, 2), (key89, 2), (key150, 2), (key6, 2), (key89, 2), (key6, 2), (key89, -2), (key89, -2), (key6, -2), (key85, 6), (key85, -2), (key85, -2), (key2, -2)]

theorem rawRowCheck13424 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13424 := by decide +kernel

def row13424 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key89, -4), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck13424 : row13424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13424 := by decide +kernel

theorem rowEval13424 (x : Key → ℝ) : Integer.Sparse.eval row13424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13424, Integer.Sparse.eval_collectBalanced, rawRowCheck13424]

def rawRow13425 : Integer.Sparse Key := [(key972, -2), (key978, -2), (key978, -2), (key978, 6), (key1086, -2), (key1092, -2), (key1092, -2), (key1086, 2), (key1092, 2), (key1086, 2), (key1163, 2), (key1092, 2), (key1163, 2), (key1092, -2), (key1092, -2), (key1163, -2), (key1227, 6), (key1227, -2), (key1227, -2), (key1244, -2)]

theorem rawRowCheck13425 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13425 := by decide +kernel

def row13425 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13425 : row13425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13425 := by decide +kernel

theorem rowEval13425 (x : Key → ℝ) : Integer.Sparse.eval row13425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13425, Integer.Sparse.eval_collectBalanced, rawRowCheck13425]

def rawRow13426 : Integer.Sparse Key := [(key978, -2), (key972, -2), (key978, -2), (key978, 6), (key1092, -2), (key1086, -2), (key1092, -2), (key1092, 2), (key1086, 2), (key1163, 2), (key1086, 2), (key1163, 2), (key1092, 2), (key1092, -2), (key1163, -2), (key1092, -2), (key1227, 6), (key1227, -2), (key1244, -2), (key1227, -2)]

theorem rawRowCheck13426 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13426 := by decide +kernel

def row13426 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13426 : row13426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13426 := by decide +kernel

theorem rowEval13426 (x : Key → ℝ) : Integer.Sparse.eval row13426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13426, Integer.Sparse.eval_collectBalanced, rawRowCheck13426]

def rawRow13427 : Integer.Sparse Key := [(key978, -2), (key978, -2), (key972, -2), (key978, 6), (key1092, -2), (key1092, -2), (key1086, -2), (key1163, 2), (key1163, 2), (key1092, 2), (key1092, 2), (key1086, 2), (key1086, 2), (key1163, -2), (key1092, -2), (key1092, -2), (key1227, 6), (key1244, -2), (key1227, -2), (key1227, -2)]

theorem rawRowCheck13427 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13427 := by decide +kernel

def row13427 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13427 : row13427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13427 := by decide +kernel

theorem rowEval13427 (x : Key → ℝ) : Integer.Sparse.eval row13427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13427, Integer.Sparse.eval_collectBalanced, rawRowCheck13427]

def rawRow13428 : Integer.Sparse Key := [(key978, -2), (key978, -2), (key978, -2), (key972, 6), (key1163, -2), (key1163, -2), (key1163, -2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1092, 2), (key1086, -2), (key1086, -2), (key1086, -2), (key1244, 6), (key1227, -2), (key1227, -2), (key1227, -2)]

theorem rawRowCheck13428 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13428 := by decide +kernel

def row13428 : Integer.Sparse Key := [(key972, 6), (key978, -6), (key1086, -6), (key1092, 12), (key1163, -6), (key1227, -6), (key1244, 6)]

theorem rowCheck13428 : row13428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13428 := by decide +kernel

theorem rowEval13428 (x : Key → ℝ) : Integer.Sparse.eval row13428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13428, Integer.Sparse.eval_collectBalanced, rawRowCheck13428]

def rawRow13429 : Integer.Sparse Key := [(key1086, -2), (key1092, -2), (key1092, -2), (key1227, 6), (key972, -2), (key978, -2), (key978, -2), (key1086, 2), (key1092, 2), (key1086, 2), (key1163, 2), (key1092, 2), (key1163, 2), (key1227, -2), (key1227, -2), (key1244, -2), (key978, 6), (key1092, -2), (key1092, -2), (key1163, -2)]

theorem rawRowCheck13429 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13429 := by decide +kernel

def row13429 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13429 : row13429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13429 := by decide +kernel

theorem rowEval13429 (x : Key → ℝ) : Integer.Sparse.eval row13429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13429, Integer.Sparse.eval_collectBalanced, rawRowCheck13429]

def rawRow13430 : Integer.Sparse Key := [(key1092, -2), (key1086, -2), (key1092, -2), (key1227, 6), (key978, -2), (key972, -2), (key978, -2), (key1092, 2), (key1086, 2), (key1163, 2), (key1086, 2), (key1163, 2), (key1092, 2), (key1227, -2), (key1244, -2), (key1227, -2), (key978, 6), (key1092, -2), (key1163, -2), (key1092, -2)]

theorem rawRowCheck13430 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13430 := by decide +kernel

def row13430 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13430 : row13430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13430 := by decide +kernel

theorem rowEval13430 (x : Key → ℝ) : Integer.Sparse.eval row13430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13430, Integer.Sparse.eval_collectBalanced, rawRowCheck13430]

def rawRow13431 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1086, -2), (key1227, 6), (key978, -2), (key978, -2), (key972, -2), (key1163, 2), (key1163, 2), (key1092, 2), (key1092, 2), (key1086, 2), (key1086, 2), (key1244, -2), (key1227, -2), (key1227, -2), (key978, 6), (key1163, -2), (key1092, -2), (key1092, -2)]

theorem rawRowCheck13431 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13431 := by decide +kernel

def row13431 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13431 : row13431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13431 := by decide +kernel

theorem rowEval13431 (x : Key → ℝ) : Integer.Sparse.eval row13431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13431, Integer.Sparse.eval_collectBalanced, rawRowCheck13431]

def rawRow13432 : Integer.Sparse Key := [(key1086, -2), (key1092, -2), (key1227, -2), (key1092, 6), (key1086, -2), (key1092, -2), (key1227, -2), (key972, 2), (key978, 2), (key1086, 2), (key1163, 2), (key1227, 2), (key1244, 2), (key978, -2), (key1092, -2), (key1163, -2), (key1092, 6), (key978, -2), (key1092, -2), (key1163, -2)]

theorem rawRowCheck13432 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13432 := by decide +kernel

def row13432 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck13432 : row13432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13432 := by decide +kernel

theorem rowEval13432 (x : Key → ℝ) : Integer.Sparse.eval row13432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13432, Integer.Sparse.eval_collectBalanced, rawRowCheck13432]

def rawRow13433 : Integer.Sparse Key := [(key1092, -2), (key1086, -2), (key1227, -2), (key1092, 6), (key1092, -2), (key1086, -2), (key1227, -2), (key978, 2), (key972, 2), (key1163, 2), (key1086, 2), (key1244, 2), (key1227, 2), (key978, -2), (key1163, -2), (key1092, -2), (key1092, 6), (key978, -2), (key1163, -2), (key1092, -2)]

theorem rawRowCheck13433 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13433 := by decide +kernel

def row13433 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck13433 : row13433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13433 := by decide +kernel

theorem rowEval13433 (x : Key → ℝ) : Integer.Sparse.eval row13433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13433, Integer.Sparse.eval_collectBalanced, rawRowCheck13433]

def rawRow13434 : Integer.Sparse Key := [(key1086, -2), (key1227, -2), (key1092, -2), (key1092, 6), (key1086, -2), (key1227, -2), (key1092, -2), (key1086, 2), (key1227, 2), (key972, 2), (key1244, 2), (key978, 2), (key1163, 2), (key1092, -2), (key978, -2), (key1163, -2), (key1092, 6), (key1092, -2), (key978, -2), (key1163, -2)]

theorem rawRowCheck13434 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13434 := by decide +kernel

def row13434 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck13434 : row13434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13434 := by decide +kernel

theorem rowEval13434 (x : Key → ℝ) : Integer.Sparse.eval row13434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13434, Integer.Sparse.eval_collectBalanced, rawRowCheck13434]

def rawRow13435 : Integer.Sparse Key := [(key1227, -2), (key1086, -2), (key1092, -2), (key1092, 6), (key1227, -2), (key1086, -2), (key1092, -2), (key1227, 2), (key1086, 2), (key1244, 2), (key972, 2), (key1163, 2), (key978, 2), (key1092, -2), (key1163, -2), (key978, -2), (key1092, 6), (key1092, -2), (key1163, -2), (key978, -2)]

theorem rawRowCheck13435 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13435 := by decide +kernel

def row13435 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck13435 : row13435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13435 := by decide +kernel

theorem rowEval13435 (x : Key → ℝ) : Integer.Sparse.eval row13435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13435, Integer.Sparse.eval_collectBalanced, rawRowCheck13435]

def rawRow13436 : Integer.Sparse Key := [(key1092, -2), (key1227, -2), (key1086, -2), (key1092, 6), (key1092, -2), (key1227, -2), (key1086, -2), (key1163, 2), (key1244, 2), (key978, 2), (key1227, 2), (key972, 2), (key1086, 2), (key1163, -2), (key978, -2), (key1092, -2), (key1092, 6), (key1163, -2), (key978, -2), (key1092, -2)]

theorem rawRowCheck13436 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13436 := by decide +kernel

def row13436 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck13436 : row13436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13436 := by decide +kernel

theorem rowEval13436 (x : Key → ℝ) : Integer.Sparse.eval row13436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13436, Integer.Sparse.eval_collectBalanced, rawRowCheck13436]

def rawRow13437 : Integer.Sparse Key := [(key1227, -2), (key1092, -2), (key1086, -2), (key1092, 6), (key1227, -2), (key1092, -2), (key1086, -2), (key1244, 2), (key1163, 2), (key1227, 2), (key978, 2), (key1086, 2), (key972, 2), (key1163, -2), (key1092, -2), (key978, -2), (key1092, 6), (key1163, -2), (key1092, -2), (key978, -2)]

theorem rawRowCheck13437 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13437 := by decide +kernel

def row13437 : Integer.Sparse Key := [(key972, 2), (key978, -2), (key1086, -2), (key1092, 4), (key1163, -2), (key1227, -2), (key1244, 2)]

theorem rowCheck13437 : row13437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13437 := by decide +kernel

theorem rowEval13437 (x : Key → ℝ) : Integer.Sparse.eval row13437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13437, Integer.Sparse.eval_collectBalanced, rawRowCheck13437]

def rawRow13438 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1227, -2), (key1086, 6), (key1163, -2), (key1163, -2), (key1244, -2), (key978, 2), (key978, 2), (key1092, 2), (key1092, 2), (key1227, 2), (key1227, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1163, 6), (key978, -2), (key1092, -2), (key1092, -2)]

theorem rawRowCheck13438 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13438 := by decide +kernel

def row13438 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13438 : row13438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13438 := by decide +kernel

theorem rowEval13438 (x : Key → ℝ) : Integer.Sparse.eval row13438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13438, Integer.Sparse.eval_collectBalanced, rawRowCheck13438]

def rawRow13439 : Integer.Sparse Key := [(key1092, -2), (key1227, -2), (key1092, -2), (key1086, 6), (key1163, -2), (key1244, -2), (key1163, -2), (key1092, 2), (key1227, 2), (key978, 2), (key1227, 2), (key978, 2), (key1092, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1163, 6), (key1092, -2), (key978, -2), (key1092, -2)]

theorem rawRowCheck13439 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13439 := by decide +kernel

def row13439 : Integer.Sparse Key := [(key972, -2), (key978, 2), (key1086, 2), (key1092, -4), (key1163, 2), (key1227, 2), (key1244, -2)]

theorem rowCheck13439 : row13439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13439 := by decide +kernel

theorem rowEval13439 (x : Key → ℝ) : Integer.Sparse.eval row13439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13439, Integer.Sparse.eval_collectBalanced, rawRowCheck13439]

end MUB6.Certificate.GramRows

end OAI

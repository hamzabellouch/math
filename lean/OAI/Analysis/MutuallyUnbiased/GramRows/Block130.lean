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
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow13568 : Integer.Sparse Key := [(key153, -2), (key188, -2), (key157, -2), (key157, 6), (key92, -2), (key168, -2), (key95, -2), (key92, 2), (key168, 2), (key9, 2), (key188, 2), (key12, 2), (key157, 2), (key95, -2), (key12, -2), (key157, -2), (key92, 6), (key92, -2), (key9, -2), (key153, -2)]

theorem rawRowCheck13568 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow13568 := by decide +kernel

def row13568 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13568 : row13568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13568 := by decide +kernel

theorem rowEval13568 (x : Key → ℝ) : Integer.Sparse.eval row13568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13568, Integer.Sparse.eval_collectBalanced, rawRowCheck13568]

def rawRow13569 : Integer.Sparse Key := [(key188, -2), (key153, -2), (key157, -2), (key157, 6), (key168, -2), (key92, -2), (key95, -2), (key168, 2), (key92, 2), (key188, 2), (key9, 2), (key157, 2), (key12, 2), (key95, -2), (key157, -2), (key12, -2), (key92, 6), (key92, -2), (key153, -2), (key9, -2)]

theorem rawRowCheck13569 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow13569 := by decide +kernel

def row13569 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13569 : row13569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13569 := by decide +kernel

theorem rowEval13569 (x : Key → ℝ) : Integer.Sparse.eval row13569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13569, Integer.Sparse.eval_collectBalanced, rawRowCheck13569]

def rawRow13570 : Integer.Sparse Key := [(key157, -2), (key188, -2), (key153, -2), (key157, 6), (key95, -2), (key168, -2), (key92, -2), (key157, 2), (key188, 2), (key12, 2), (key168, 2), (key9, 2), (key92, 2), (key157, -2), (key12, -2), (key95, -2), (key92, 6), (key153, -2), (key9, -2), (key92, -2)]

theorem rawRowCheck13570 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow13570 := by decide +kernel

def row13570 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13570 : row13570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13570 := by decide +kernel

theorem rowEval13570 (x : Key → ℝ) : Integer.Sparse.eval row13570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13570, Integer.Sparse.eval_collectBalanced, rawRowCheck13570]

def rawRow13571 : Integer.Sparse Key := [(key188, -2), (key157, -2), (key153, -2), (key157, 6), (key168, -2), (key95, -2), (key92, -2), (key188, 2), (key157, 2), (key168, 2), (key12, 2), (key92, 2), (key9, 2), (key157, -2), (key95, -2), (key12, -2), (key92, 6), (key153, -2), (key92, -2), (key9, -2)]

theorem rawRowCheck13571 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow13571 := by decide +kernel

def row13571 : Integer.Sparse Key := [(key92, 4), (key95, -4), (key153, -4), (key157, 4)]

theorem rowCheck13571 : row13571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13571 := by decide +kernel

theorem rowEval13571 (x : Key → ℝ) : Integer.Sparse.eval row13571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13571, Integer.Sparse.eval_collectBalanced, rawRowCheck13571]

def rawRow13572 : Integer.Sparse Key := [(key157, -2), (key157, -2), (key188, -2), (key153, 6), (key157, -2), (key157, -2), (key188, -2), (key12, 2), (key12, 2), (key95, 2), (key95, 2), (key168, 2), (key168, 2), (key9, -2), (key92, -2), (key92, -2), (key153, 6), (key9, -2), (key92, -2), (key92, -2)]

theorem rawRowCheck13572 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow13572 := by decide +kernel

def row13572 : Integer.Sparse Key := [(key9, -4), (key12, 4), (key92, -8), (key95, 4), (key153, 12), (key157, -8), (key168, 4), (key188, -4)]

theorem rowCheck13572 : row13572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13572 := by decide +kernel

theorem rowEval13572 (x : Key → ℝ) : Integer.Sparse.eval row13572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13572, Integer.Sparse.eval_collectBalanced, rawRowCheck13572]

def rawRow13573 : Integer.Sparse Key := [(key157, -2), (key188, -2), (key157, -2), (key153, 6), (key157, -2), (key188, -2), (key157, -2), (key95, 2), (key168, 2), (key12, 2), (key168, 2), (key12, 2), (key95, 2), (key92, -2), (key9, -2), (key92, -2), (key153, 6), (key92, -2), (key9, -2), (key92, -2)]

theorem rawRowCheck13573 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow13573 := by decide +kernel

def row13573 : Integer.Sparse Key := [(key9, -4), (key12, 4), (key92, -8), (key95, 4), (key153, 12), (key157, -8), (key168, 4), (key188, -4)]

theorem rowCheck13573 : row13573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13573 := by decide +kernel

theorem rowEval13573 (x : Key → ℝ) : Integer.Sparse.eval row13573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13573, Integer.Sparse.eval_collectBalanced, rawRowCheck13573]

def rawRow13574 : Integer.Sparse Key := [(key188, -2), (key157, -2), (key157, -2), (key153, 6), (key188, -2), (key157, -2), (key157, -2), (key168, 2), (key95, 2), (key168, 2), (key12, 2), (key95, 2), (key12, 2), (key92, -2), (key92, -2), (key9, -2), (key153, 6), (key92, -2), (key92, -2), (key9, -2)]

theorem rawRowCheck13574 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow13574 := by decide +kernel

def row13574 : Integer.Sparse Key := [(key9, -4), (key12, 4), (key92, -8), (key95, 4), (key153, 12), (key157, -8), (key168, 4), (key188, -4)]

theorem rowCheck13574 : row13574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13574 := by decide +kernel

theorem rowEval13574 (x : Key → ℝ) : Integer.Sparse.eval row13574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13574, Integer.Sparse.eval_collectBalanced, rawRowCheck13574]

def rawRow13575 : Integer.Sparse Key := [(key10, 4), (key189, 4), (key189, 4), (key13, -2), (key13, -2), (key158, -2), (key158, -2), (key192, -2), (key192, -2), (key13, -2), (key13, -2), (key158, -2), (key158, -2), (key192, -2), (key192, -2), (key15, 4), (key163, 4), (key163, 4)]

theorem rawRowCheck13575 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form5 = rawRow13575 := by decide +kernel

def row13575 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key158, -8), (key163, 8), (key189, 8), (key192, -8)]

theorem rowCheck13575 : row13575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13575 := by decide +kernel

theorem rowEval13575 (x : Key → ℝ) : Integer.Sparse.eval row13575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13575, Integer.Sparse.eval_collectBalanced, rawRowCheck13575]

def rawRow13576 : Integer.Sparse Key := [(key189, 4), (key10, 4), (key189, 4), (key158, -2), (key192, -2), (key13, -2), (key192, -2), (key13, -2), (key158, -2), (key158, -2), (key192, -2), (key13, -2), (key192, -2), (key13, -2), (key158, -2), (key163, 4), (key15, 4), (key163, 4)]

theorem rawRowCheck13576 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form5 = rawRow13576 := by decide +kernel

def row13576 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key158, -8), (key163, 8), (key189, 8), (key192, -8)]

theorem rowCheck13576 : row13576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13576 := by decide +kernel

theorem rowEval13576 (x : Key → ℝ) : Integer.Sparse.eval row13576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13576, Integer.Sparse.eval_collectBalanced, rawRowCheck13576]

def rawRow13577 : Integer.Sparse Key := [(key189, 4), (key189, 4), (key10, 4), (key192, -2), (key158, -2), (key192, -2), (key13, -2), (key158, -2), (key13, -2), (key192, -2), (key158, -2), (key192, -2), (key13, -2), (key158, -2), (key13, -2), (key163, 4), (key163, 4), (key15, 4)]

theorem rawRowCheck13577 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form5 = rawRow13577 := by decide +kernel

def row13577 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key158, -8), (key163, 8), (key189, 8), (key192, -8)]

theorem rowCheck13577 : row13577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13577 := by decide +kernel

theorem rowEval13577 (x : Key → ℝ) : Integer.Sparse.eval row13577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13577, Integer.Sparse.eval_collectBalanced, rawRowCheck13577]

def rawRow13578 : Integer.Sparse Key := [(key13, 4), (key158, 4), (key192, 4), (key10, -2), (key13, -2), (key93, -2), (key158, -2), (key169, -2), (key189, -2), (key13, -2), (key15, -2), (key96, -2), (key163, -2), (key170, -2), (key192, -2), (key13, 4), (key96, 4), (key158, 4)]

theorem rawRowCheck13578 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5 = rawRow13578 := by decide +kernel

def row13578 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13578 : row13578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13578 := by decide +kernel

theorem rowEval13578 (x : Key → ℝ) : Integer.Sparse.eval row13578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13578, Integer.Sparse.eval_collectBalanced, rawRowCheck13578]

def rawRow13579 : Integer.Sparse Key := [(key13, 4), (key192, 4), (key158, 4), (key13, -2), (key10, -2), (key158, -2), (key93, -2), (key189, -2), (key169, -2), (key15, -2), (key13, -2), (key163, -2), (key96, -2), (key192, -2), (key170, -2), (key13, 4), (key158, 4), (key96, 4)]

theorem rawRowCheck13579 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5 = rawRow13579 := by decide +kernel

def row13579 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13579 : row13579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13579 := by decide +kernel

theorem rowEval13579 (x : Key → ℝ) : Integer.Sparse.eval row13579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13579, Integer.Sparse.eval_collectBalanced, rawRowCheck13579]

def rawRow13580 : Integer.Sparse Key := [(key158, 4), (key13, 4), (key192, 4), (key93, -2), (key158, -2), (key10, -2), (key189, -2), (key13, -2), (key158, -2), (key96, -2), (key170, -2), (key13, -2), (key192, -2), (key15, -2), (key163, -2), (key96, 4), (key13, 4), (key158, 4)]

theorem rawRowCheck13580 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5 = rawRow13580 := by decide +kernel

def row13580 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 4), (key163, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13580 : row13580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13580 := by decide +kernel

theorem rowEval13580 (x : Key → ℝ) : Integer.Sparse.eval row13580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13580, Integer.Sparse.eval_collectBalanced, rawRowCheck13580]

def rawRow13581 : Integer.Sparse Key := [(key158, 4), (key192, 4), (key13, 4), (key158, -2), (key93, -2), (key189, -2), (key10, -2), (key158, -2), (key13, -2), (key170, -2), (key96, -2), (key192, -2), (key13, -2), (key163, -2), (key15, -2), (key96, 4), (key158, 4), (key13, 4)]

theorem rawRowCheck13581 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5 = rawRow13581 := by decide +kernel

def row13581 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 4), (key163, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13581 : row13581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13581 := by decide +kernel

theorem rowEval13581 (x : Key → ℝ) : Integer.Sparse.eval row13581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13581, Integer.Sparse.eval_collectBalanced, rawRowCheck13581]

def rawRow13582 : Integer.Sparse Key := [(key192, 4), (key13, 4), (key158, 4), (key169, -2), (key189, -2), (key13, -2), (key158, -2), (key10, -2), (key93, -2), (key163, -2), (key192, -2), (key15, -2), (key170, -2), (key13, -2), (key96, -2), (key158, 4), (key13, 4), (key96, 4)]

theorem rawRowCheck13582 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5 = rawRow13582 := by decide +kernel

def row13582 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13582 : row13582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13582 := by decide +kernel

theorem rowEval13582 (x : Key → ℝ) : Integer.Sparse.eval row13582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13582, Integer.Sparse.eval_collectBalanced, rawRowCheck13582]

def rawRow13583 : Integer.Sparse Key := [(key192, 4), (key158, 4), (key13, 4), (key189, -2), (key169, -2), (key158, -2), (key13, -2), (key93, -2), (key10, -2), (key192, -2), (key163, -2), (key170, -2), (key15, -2), (key96, -2), (key13, -2), (key158, 4), (key96, 4), (key13, 4)]

theorem rawRowCheck13583 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5 = rawRow13583 := by decide +kernel

def row13583 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13583 : row13583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13583 := by decide +kernel

theorem rowEval13583 (x : Key → ℝ) : Integer.Sparse.eval row13583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13583, Integer.Sparse.eval_collectBalanced, rawRowCheck13583]

def rawRow13584 : Integer.Sparse Key := [(key13, 4), (key158, 4), (key192, 4), (key13, -2), (key15, -2), (key96, -2), (key170, -2), (key163, -2), (key192, -2), (key10, -2), (key13, -2), (key93, -2), (key158, -2), (key169, -2), (key189, -2), (key13, 4), (key96, 4), (key158, 4)]

theorem rawRowCheck13584 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5 = rawRow13584 := by decide +kernel

def row13584 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13584 : row13584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13584 := by decide +kernel

theorem rowEval13584 (x : Key → ℝ) : Integer.Sparse.eval row13584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13584, Integer.Sparse.eval_collectBalanced, rawRowCheck13584]

def rawRow13585 : Integer.Sparse Key := [(key13, 4), (key192, 4), (key158, 4), (key15, -2), (key13, -2), (key170, -2), (key96, -2), (key192, -2), (key163, -2), (key13, -2), (key10, -2), (key158, -2), (key93, -2), (key189, -2), (key169, -2), (key13, 4), (key158, 4), (key96, 4)]

theorem rawRowCheck13585 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5 = rawRow13585 := by decide +kernel

def row13585 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13585 : row13585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13585 := by decide +kernel

theorem rowEval13585 (x : Key → ℝ) : Integer.Sparse.eval row13585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13585, Integer.Sparse.eval_collectBalanced, rawRowCheck13585]

def rawRow13586 : Integer.Sparse Key := [(key158, 4), (key13, 4), (key192, 4), (key96, -2), (key163, -2), (key13, -2), (key192, -2), (key15, -2), (key170, -2), (key93, -2), (key158, -2), (key10, -2), (key189, -2), (key13, -2), (key158, -2), (key96, 4), (key13, 4), (key158, 4)]

theorem rawRowCheck13586 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5 = rawRow13586 := by decide +kernel

def row13586 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 4), (key163, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13586 : row13586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13586 := by decide +kernel

theorem rowEval13586 (x : Key → ℝ) : Integer.Sparse.eval row13586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13586, Integer.Sparse.eval_collectBalanced, rawRowCheck13586]

def rawRow13587 : Integer.Sparse Key := [(key158, 4), (key192, 4), (key13, 4), (key163, -2), (key96, -2), (key192, -2), (key13, -2), (key170, -2), (key15, -2), (key158, -2), (key93, -2), (key189, -2), (key10, -2), (key158, -2), (key13, -2), (key96, 4), (key158, 4), (key13, 4)]

theorem rawRowCheck13587 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5 = rawRow13587 := by decide +kernel

def row13587 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 4), (key163, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13587 : row13587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13587 := by decide +kernel

theorem rowEval13587 (x : Key → ℝ) : Integer.Sparse.eval row13587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13587, Integer.Sparse.eval_collectBalanced, rawRowCheck13587]

def rawRow13588 : Integer.Sparse Key := [(key192, 4), (key13, 4), (key158, 4), (key170, -2), (key192, -2), (key15, -2), (key163, -2), (key13, -2), (key96, -2), (key169, -2), (key189, -2), (key13, -2), (key158, -2), (key10, -2), (key93, -2), (key158, 4), (key13, 4), (key96, 4)]

theorem rawRowCheck13588 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5 = rawRow13588 := by decide +kernel

def row13588 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13588 : row13588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13588 := by decide +kernel

theorem rowEval13588 (x : Key → ℝ) : Integer.Sparse.eval row13588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13588, Integer.Sparse.eval_collectBalanced, rawRowCheck13588]

def rawRow13589 : Integer.Sparse Key := [(key192, 4), (key158, 4), (key13, 4), (key192, -2), (key170, -2), (key163, -2), (key15, -2), (key96, -2), (key13, -2), (key189, -2), (key169, -2), (key158, -2), (key13, -2), (key93, -2), (key10, -2), (key158, 4), (key96, 4), (key13, 4)]

theorem rawRowCheck13589 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5 = rawRow13589 := by decide +kernel

def row13589 : Integer.Sparse Key := [(key10, -2), (key13, 4), (key15, -2), (key93, -2), (key96, 2), (key158, 6), (key163, -2), (key169, -2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck13589 : row13589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13589 := by decide +kernel

theorem rowEval13589 (x : Key → ℝ) : Integer.Sparse.eval row13589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13589, Integer.Sparse.eval_collectBalanced, rawRowCheck13589]

def rawRow13590 : Integer.Sparse Key := [(key15, 4), (key163, 4), (key163, 4), (key13, -2), (key13, -2), (key96, -2), (key96, -2), (key158, -2), (key158, -2), (key13, -2), (key13, -2), (key96, -2), (key96, -2), (key158, -2), (key158, -2), (key10, 4), (key93, 4), (key93, 4)]

theorem rawRowCheck13590 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5 = rawRow13590 := by decide +kernel

def row13590 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key93, 8), (key96, -8), (key158, -8), (key163, 8)]

theorem rowCheck13590 : row13590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13590 := by decide +kernel

theorem rowEval13590 (x : Key → ℝ) : Integer.Sparse.eval row13590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13590, Integer.Sparse.eval_collectBalanced, rawRowCheck13590]

def rawRow13591 : Integer.Sparse Key := [(key163, 4), (key15, 4), (key163, 4), (key96, -2), (key158, -2), (key13, -2), (key158, -2), (key13, -2), (key96, -2), (key96, -2), (key158, -2), (key13, -2), (key158, -2), (key13, -2), (key96, -2), (key93, 4), (key10, 4), (key93, 4)]

theorem rawRowCheck13591 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5 = rawRow13591 := by decide +kernel

def row13591 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key93, 8), (key96, -8), (key158, -8), (key163, 8)]

theorem rowCheck13591 : row13591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13591 := by decide +kernel

theorem rowEval13591 (x : Key → ℝ) : Integer.Sparse.eval row13591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13591, Integer.Sparse.eval_collectBalanced, rawRowCheck13591]

def rawRow13592 : Integer.Sparse Key := [(key163, 4), (key163, 4), (key15, 4), (key158, -2), (key96, -2), (key158, -2), (key13, -2), (key96, -2), (key13, -2), (key158, -2), (key96, -2), (key158, -2), (key13, -2), (key96, -2), (key13, -2), (key93, 4), (key93, 4), (key10, 4)]

theorem rawRowCheck13592 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5 = rawRow13592 := by decide +kernel

def row13592 : Integer.Sparse Key := [(key10, 4), (key13, -8), (key15, 4), (key93, 8), (key96, -8), (key158, -8), (key163, 8)]

theorem rowCheck13592 : row13592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13592 := by decide +kernel

theorem rowEval13592 (x : Key → ℝ) : Integer.Sparse.eval row13592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13592, Integer.Sparse.eval_collectBalanced, rawRowCheck13592]

def rawRow13593 : Integer.Sparse Key := [(key2587, 4), (key2966, 4), (key2989, 4), (key2587, -2), (key2593, -2), (key2843, -2), (key2880, -2), (key2968, -2), (key2989, -2), (key2598, -2), (key2600, -2), (key2887, -2), (key2910, -2), (key2995, -2), (key3002, -2), (key2600, 4), (key2889, 4), (key2910, 4)]

theorem rawRowCheck13593 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form0 = rawRow13593 := by decide +kernel

def row13593 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13593 : row13593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13593 := by decide +kernel

theorem rowEval13593 (x : Key → ℝ) : Integer.Sparse.eval row13593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13593, Integer.Sparse.eval_collectBalanced, rawRowCheck13593]

def rawRow13594 : Integer.Sparse Key := [(key2587, 4), (key2989, 4), (key2966, 4), (key2593, -2), (key2587, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2968, -2), (key2600, -2), (key2598, -2), (key2910, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2600, 4), (key2910, 4), (key2889, 4)]

theorem rawRowCheck13594 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form0 = rawRow13594 := by decide +kernel

def row13594 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13594 : row13594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13594 := by decide +kernel

theorem rowEval13594 (x : Key → ℝ) : Integer.Sparse.eval row13594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13594, Integer.Sparse.eval_collectBalanced, rawRowCheck13594]

def rawRow13595 : Integer.Sparse Key := [(key2966, 4), (key2587, 4), (key2989, 4), (key2843, -2), (key2968, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2887, -2), (key2995, -2), (key2598, -2), (key3002, -2), (key2600, -2), (key2910, -2), (key2889, 4), (key2600, 4), (key2910, 4)]

theorem rawRowCheck13595 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form0 = rawRow13595 := by decide +kernel

def row13595 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13595 : row13595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13595 := by decide +kernel

theorem rowEval13595 (x : Key → ℝ) : Integer.Sparse.eval row13595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13595, Integer.Sparse.eval_collectBalanced, rawRowCheck13595]

def rawRow13596 : Integer.Sparse Key := [(key2966, 4), (key2989, 4), (key2587, 4), (key2968, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2880, -2), (key2593, -2), (key2995, -2), (key2887, -2), (key3002, -2), (key2598, -2), (key2910, -2), (key2600, -2), (key2889, 4), (key2910, 4), (key2600, 4)]

theorem rawRowCheck13596 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form0 = rawRow13596 := by decide +kernel

def row13596 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13596 : row13596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13596 := by decide +kernel

theorem rowEval13596 (x : Key → ℝ) : Integer.Sparse.eval row13596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13596, Integer.Sparse.eval_collectBalanced, rawRowCheck13596]

def rawRow13597 : Integer.Sparse Key := [(key2989, 4), (key2587, 4), (key2966, 4), (key2880, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2587, -2), (key2843, -2), (key2910, -2), (key3002, -2), (key2600, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2910, 4), (key2600, 4), (key2889, 4)]

theorem rawRowCheck13597 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form0 = rawRow13597 := by decide +kernel

def row13597 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13597 : row13597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13597 := by decide +kernel

theorem rowEval13597 (x : Key → ℝ) : Integer.Sparse.eval row13597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13597, Integer.Sparse.eval_collectBalanced, rawRowCheck13597]

def rawRow13598 : Integer.Sparse Key := [(key2989, 4), (key2966, 4), (key2587, 4), (key2989, -2), (key2880, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key3002, -2), (key2910, -2), (key2995, -2), (key2600, -2), (key2887, -2), (key2598, -2), (key2910, 4), (key2889, 4), (key2600, 4)]

theorem rawRowCheck13598 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form0 = rawRow13598 := by decide +kernel

def row13598 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13598 : row13598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13598 := by decide +kernel

theorem rowEval13598 (x : Key → ℝ) : Integer.Sparse.eval row13598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13598, Integer.Sparse.eval_collectBalanced, rawRowCheck13598]

def rawRow13599 : Integer.Sparse Key := [(key2593, 4), (key2968, 4), (key2968, 4), (key2587, -2), (key2587, -2), (key2843, -2), (key2843, -2), (key2966, -2), (key2966, -2), (key2600, -2), (key2600, -2), (key2889, -2), (key2889, -2), (key2995, -2), (key2995, -2), (key2598, 4), (key2887, 4), (key2887, 4)]

theorem rawRowCheck13599 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form0 = rawRow13599 := by decide +kernel

def row13599 : Integer.Sparse Key := [(key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2843, -4), (key2887, 8), (key2889, -4), (key2966, -4), (key2968, 8), (key2995, -4)]

theorem rowCheck13599 : row13599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13599 := by decide +kernel

theorem rowEval13599 (x : Key → ℝ) : Integer.Sparse.eval row13599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13599, Integer.Sparse.eval_collectBalanced, rawRowCheck13599]

def rawRow13600 : Integer.Sparse Key := [(key2968, 4), (key2593, 4), (key2968, 4), (key2843, -2), (key2966, -2), (key2587, -2), (key2966, -2), (key2587, -2), (key2843, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2887, 4), (key2598, 4), (key2887, 4)]

theorem rawRowCheck13600 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form0 = rawRow13600 := by decide +kernel

def row13600 : Integer.Sparse Key := [(key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2843, -4), (key2887, 8), (key2889, -4), (key2966, -4), (key2968, 8), (key2995, -4)]

theorem rowCheck13600 : row13600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13600 := by decide +kernel

theorem rowEval13600 (x : Key → ℝ) : Integer.Sparse.eval row13600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13600, Integer.Sparse.eval_collectBalanced, rawRowCheck13600]

def rawRow13601 : Integer.Sparse Key := [(key2968, 4), (key2968, 4), (key2593, 4), (key2966, -2), (key2843, -2), (key2966, -2), (key2587, -2), (key2843, -2), (key2587, -2), (key2995, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2600, -2), (key2887, 4), (key2887, 4), (key2598, 4)]

theorem rawRowCheck13601 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form0 = rawRow13601 := by decide +kernel

def row13601 : Integer.Sparse Key := [(key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2843, -4), (key2887, 8), (key2889, -4), (key2966, -4), (key2968, 8), (key2995, -4)]

theorem rowCheck13601 : row13601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13601 := by decide +kernel

theorem rowEval13601 (x : Key → ℝ) : Integer.Sparse.eval row13601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13601, Integer.Sparse.eval_collectBalanced, rawRowCheck13601]

def rawRow13602 : Integer.Sparse Key := [(key2587, 4), (key2966, 4), (key2989, 4), (key2598, -2), (key2600, -2), (key2887, -2), (key2910, -2), (key2995, -2), (key3002, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2880, -2), (key2968, -2), (key2989, -2), (key2600, 4), (key2889, 4), (key2910, 4)]

theorem rawRowCheck13602 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form0 = rawRow13602 := by decide +kernel

def row13602 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13602 : row13602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13602 := by decide +kernel

theorem rowEval13602 (x : Key → ℝ) : Integer.Sparse.eval row13602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13602, Integer.Sparse.eval_collectBalanced, rawRowCheck13602]

def rawRow13603 : Integer.Sparse Key := [(key2587, 4), (key2989, 4), (key2966, 4), (key2600, -2), (key2598, -2), (key2910, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2593, -2), (key2587, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2968, -2), (key2600, 4), (key2910, 4), (key2889, 4)]

theorem rawRowCheck13603 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form0 = rawRow13603 := by decide +kernel

def row13603 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13603 : row13603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13603 := by decide +kernel

theorem rowEval13603 (x : Key → ℝ) : Integer.Sparse.eval row13603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13603, Integer.Sparse.eval_collectBalanced, rawRowCheck13603]

def rawRow13604 : Integer.Sparse Key := [(key2966, 4), (key2587, 4), (key2989, 4), (key2887, -2), (key2995, -2), (key2598, -2), (key3002, -2), (key2600, -2), (key2910, -2), (key2843, -2), (key2968, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2889, 4), (key2600, 4), (key2910, 4)]

theorem rawRowCheck13604 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form0 = rawRow13604 := by decide +kernel

def row13604 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13604 : row13604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13604 := by decide +kernel

theorem rowEval13604 (x : Key → ℝ) : Integer.Sparse.eval row13604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13604, Integer.Sparse.eval_collectBalanced, rawRowCheck13604]

def rawRow13605 : Integer.Sparse Key := [(key2966, 4), (key2989, 4), (key2587, 4), (key2995, -2), (key2887, -2), (key3002, -2), (key2598, -2), (key2910, -2), (key2600, -2), (key2968, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2880, -2), (key2593, -2), (key2889, 4), (key2910, 4), (key2600, 4)]

theorem rawRowCheck13605 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form0 = rawRow13605 := by decide +kernel

def row13605 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13605 : row13605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13605 := by decide +kernel

theorem rowEval13605 (x : Key → ℝ) : Integer.Sparse.eval row13605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13605, Integer.Sparse.eval_collectBalanced, rawRowCheck13605]

def rawRow13606 : Integer.Sparse Key := [(key2989, 4), (key2587, 4), (key2966, 4), (key2910, -2), (key3002, -2), (key2600, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2880, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2587, -2), (key2843, -2), (key2910, 4), (key2600, 4), (key2889, 4)]

theorem rawRowCheck13606 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form0 = rawRow13606 := by decide +kernel

def row13606 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13606 : row13606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13606 := by decide +kernel

theorem rowEval13606 (x : Key → ℝ) : Integer.Sparse.eval row13606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13606, Integer.Sparse.eval_collectBalanced, rawRowCheck13606]

def rawRow13607 : Integer.Sparse Key := [(key2989, 4), (key2966, 4), (key2587, 4), (key3002, -2), (key2910, -2), (key2995, -2), (key2600, -2), (key2887, -2), (key2598, -2), (key2989, -2), (key2880, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key2910, 4), (key2889, 4), (key2600, 4)]

theorem rawRowCheck13607 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form0 = rawRow13607 := by decide +kernel

def row13607 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck13607 : row13607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13607 := by decide +kernel

theorem rowEval13607 (x : Key → ℝ) : Integer.Sparse.eval row13607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13607, Integer.Sparse.eval_collectBalanced, rawRowCheck13607]

def rawRow13608 : Integer.Sparse Key := [(key2390, 4), (key2929, 4), (key3002, 4), (key2587, -2), (key2600, -2), (key2766, -2), (key2910, -2), (key2931, -2), (key2989, -2), (key2587, -2), (key2600, -2), (key2766, -2), (key2910, -2), (key2931, -2), (key2989, -2), (key2593, 4), (key2772, 4), (key2880, 4)]

theorem rawRowCheck13608 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form0 = rawRow13608 := by decide +kernel

def row13608 : Integer.Sparse Key := [(key2390, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2929, 4), (key2931, -4), (key2989, -4), (key3002, 4)]

theorem rowCheck13608 : row13608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13608 := by decide +kernel

theorem rowEval13608 (x : Key → ℝ) : Integer.Sparse.eval row13608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13608, Integer.Sparse.eval_collectBalanced, rawRowCheck13608]

def rawRow13609 : Integer.Sparse Key := [(key2390, 4), (key3002, 4), (key2929, 4), (key2600, -2), (key2587, -2), (key2910, -2), (key2766, -2), (key2989, -2), (key2931, -2), (key2600, -2), (key2587, -2), (key2910, -2), (key2766, -2), (key2989, -2), (key2931, -2), (key2593, 4), (key2880, 4), (key2772, 4)]

theorem rawRowCheck13609 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form0 = rawRow13609 := by decide +kernel

def row13609 : Integer.Sparse Key := [(key2390, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2929, 4), (key2931, -4), (key2989, -4), (key3002, 4)]

theorem rowCheck13609 : row13609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13609 := by decide +kernel

theorem rowEval13609 (x : Key → ℝ) : Integer.Sparse.eval row13609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13609, Integer.Sparse.eval_collectBalanced, rawRowCheck13609]

def rawRow13610 : Integer.Sparse Key := [(key2437, 4), (key2598, 4), (key3002, 4), (key2766, -2), (key2931, -2), (key2587, -2), (key2989, -2), (key2600, -2), (key2910, -2), (key2766, -2), (key2931, -2), (key2587, -2), (key2989, -2), (key2600, -2), (key2910, -2), (key2772, 4), (key2593, 4), (key2880, 4)]

theorem rawRowCheck13610 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form0 = rawRow13610 := by decide +kernel

def row13610 : Integer.Sparse Key := [(key2437, 4), (key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4), (key3002, 4)]

theorem rowCheck13610 : row13610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13610 := by decide +kernel

theorem rowEval13610 (x : Key → ℝ) : Integer.Sparse.eval row13610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13610, Integer.Sparse.eval_collectBalanced, rawRowCheck13610]

def rawRow13611 : Integer.Sparse Key := [(key2437, 4), (key3002, 4), (key2598, 4), (key2931, -2), (key2766, -2), (key2989, -2), (key2587, -2), (key2910, -2), (key2600, -2), (key2931, -2), (key2766, -2), (key2989, -2), (key2587, -2), (key2910, -2), (key2600, -2), (key2772, 4), (key2880, 4), (key2593, 4)]

theorem rawRowCheck13611 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form0 = rawRow13611 := by decide +kernel

def row13611 : Integer.Sparse Key := [(key2437, 4), (key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4), (key3002, 4)]

theorem rowCheck13611 : row13611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13611 := by decide +kernel

theorem rowEval13611 (x : Key → ℝ) : Integer.Sparse.eval row13611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13611, Integer.Sparse.eval_collectBalanced, rawRowCheck13611]

def rawRow13612 : Integer.Sparse Key := [(key2580, 4), (key2390, 4), (key2437, 4), (key2910, -2), (key2989, -2), (key2600, -2), (key2931, -2), (key2587, -2), (key2766, -2), (key2910, -2), (key2989, -2), (key2600, -2), (key2931, -2), (key2587, -2), (key2766, -2), (key2880, 4), (key2593, 4), (key2772, 4)]

theorem rawRowCheck13612 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form0 = rawRow13612 := by decide +kernel

def row13612 : Integer.Sparse Key := [(key2390, 4), (key2437, 4), (key2580, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4)]

theorem rowCheck13612 : row13612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13612 := by decide +kernel

theorem rowEval13612 (x : Key → ℝ) : Integer.Sparse.eval row13612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13612, Integer.Sparse.eval_collectBalanced, rawRowCheck13612]

def rawRow13613 : Integer.Sparse Key := [(key2580, 4), (key2437, 4), (key2390, 4), (key2989, -2), (key2910, -2), (key2931, -2), (key2600, -2), (key2766, -2), (key2587, -2), (key2989, -2), (key2910, -2), (key2931, -2), (key2600, -2), (key2766, -2), (key2587, -2), (key2880, 4), (key2772, 4), (key2593, 4)]

theorem rawRowCheck13613 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form0 = rawRow13613 := by decide +kernel

def row13613 : Integer.Sparse Key := [(key2390, 4), (key2437, 4), (key2580, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4)]

theorem rowCheck13613 : row13613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13613 := by decide +kernel

theorem rowEval13613 (x : Key → ℝ) : Integer.Sparse.eval row13613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13613, Integer.Sparse.eval_collectBalanced, rawRowCheck13613]

def rawRow13614 : Integer.Sparse Key := [(key2394, 4), (key2443, 4), (key2524, 4), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2889, -2), (key2931, -2), (key2968, -2), (key2587, 4), (key2766, 4), (key2843, 4)]

theorem rawRowCheck13614 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form0 = rawRow13614 := by decide +kernel

def row13614 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

theorem rowCheck13614 : row13614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13614 := by decide +kernel

theorem rowEval13614 (x : Key → ℝ) : Integer.Sparse.eval row13614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13614, Integer.Sparse.eval_collectBalanced, rawRowCheck13614]

def rawRow13615 : Integer.Sparse Key := [(key2394, 4), (key2524, 4), (key2443, 4), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2600, -2), (key2593, -2), (key2889, -2), (key2772, -2), (key2968, -2), (key2931, -2), (key2587, 4), (key2843, 4), (key2766, 4)]

theorem rawRowCheck13615 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form0 = rawRow13615 := by decide +kernel

def row13615 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

theorem rowCheck13615 : row13615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13615 := by decide +kernel

theorem rowEval13615 (x : Key → ℝ) : Integer.Sparse.eval row13615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13615, Integer.Sparse.eval_collectBalanced, rawRowCheck13615]

def rawRow13616 : Integer.Sparse Key := [(key2443, 4), (key2394, 4), (key2524, 4), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2772, -2), (key2931, -2), (key2593, -2), (key2968, -2), (key2600, -2), (key2889, -2), (key2766, 4), (key2587, 4), (key2843, 4)]

theorem rawRowCheck13616 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form0 = rawRow13616 := by decide +kernel

def row13616 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

theorem rowCheck13616 : row13616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13616 := by decide +kernel

theorem rowEval13616 (x : Key → ℝ) : Integer.Sparse.eval row13616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13616, Integer.Sparse.eval_collectBalanced, rawRowCheck13616]

def rawRow13617 : Integer.Sparse Key := [(key2443, 4), (key2524, 4), (key2394, 4), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2931, -2), (key2772, -2), (key2968, -2), (key2593, -2), (key2889, -2), (key2600, -2), (key2766, 4), (key2843, 4), (key2587, 4)]

theorem rawRowCheck13617 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form0 = rawRow13617 := by decide +kernel

def row13617 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

theorem rowCheck13617 : row13617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13617 := by decide +kernel

theorem rowEval13617 (x : Key → ℝ) : Integer.Sparse.eval row13617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13617, Integer.Sparse.eval_collectBalanced, rawRowCheck13617]

def rawRow13618 : Integer.Sparse Key := [(key2524, 4), (key2394, 4), (key2443, 4), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2889, -2), (key2968, -2), (key2600, -2), (key2931, -2), (key2593, -2), (key2772, -2), (key2843, 4), (key2587, 4), (key2766, 4)]

theorem rawRowCheck13618 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form0 = rawRow13618 := by decide +kernel

def row13618 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

theorem rowCheck13618 : row13618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13618 := by decide +kernel

theorem rowEval13618 (x : Key → ℝ) : Integer.Sparse.eval row13618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13618, Integer.Sparse.eval_collectBalanced, rawRowCheck13618]

def rawRow13619 : Integer.Sparse Key := [(key2524, 4), (key2443, 4), (key2394, 4), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2968, -2), (key2889, -2), (key2931, -2), (key2600, -2), (key2772, -2), (key2593, -2), (key2843, 4), (key2766, 4), (key2587, 4)]

theorem rawRowCheck13619 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form0 = rawRow13619 := by decide +kernel

def row13619 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

theorem rowCheck13619 : row13619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13619 := by decide +kernel

theorem rowEval13619 (x : Key → ℝ) : Integer.Sparse.eval row13619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13619, Integer.Sparse.eval_collectBalanced, rawRowCheck13619]

def rawRow13620 : Integer.Sparse Key := [(key2383, 4), (key2509, 4), (key2509, 4), (key2394, -2), (key2394, -2), (key2484, -2), (key2484, -2), (key2524, -2), (key2524, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, 4), (key2480, 4), (key2480, 4)]

theorem rawRowCheck13620 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form0 = rawRow13620 := by decide +kernel

def row13620 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2472, -4), (key2480, 8), (key2484, -4), (key2503, -4), (key2509, 8), (key2524, -4)]

theorem rowCheck13620 : row13620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13620 := by decide +kernel

theorem rowEval13620 (x : Key → ℝ) : Integer.Sparse.eval row13620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13620, Integer.Sparse.eval_collectBalanced, rawRowCheck13620]

def rawRow13621 : Integer.Sparse Key := [(key2509, 4), (key2383, 4), (key2509, 4), (key2484, -2), (key2524, -2), (key2394, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, 4), (key2390, 4), (key2480, 4)]

theorem rawRowCheck13621 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form0 = rawRow13621 := by decide +kernel

def row13621 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2472, -4), (key2480, 8), (key2484, -4), (key2503, -4), (key2509, 8), (key2524, -4)]

theorem rowCheck13621 : row13621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13621 := by decide +kernel

theorem rowEval13621 (x : Key → ℝ) : Integer.Sparse.eval row13621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13621, Integer.Sparse.eval_collectBalanced, rawRowCheck13621]

def rawRow13622 : Integer.Sparse Key := [(key2509, 4), (key2509, 4), (key2383, 4), (key2524, -2), (key2484, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2394, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, 4), (key2480, 4), (key2390, 4)]

theorem rawRowCheck13622 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form0 = rawRow13622 := by decide +kernel

def row13622 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2472, -4), (key2480, 8), (key2484, -4), (key2503, -4), (key2509, 8), (key2524, -4)]

theorem rowCheck13622 : row13622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13622 := by decide +kernel

theorem rowEval13622 (x : Key → ℝ) : Integer.Sparse.eval row13622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13622, Integer.Sparse.eval_collectBalanced, rawRowCheck13622]

def rawRow13623 : Integer.Sparse Key := [(key2394, 4), (key2443, 4), (key2524, 4), (key2383, -2), (key2394, -2), (key2411, -2), (key2484, -2), (key2443, -2), (key2509, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, 4), (key2406, 4), (key2472, 4)]

theorem rawRowCheck13623 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form0 = rawRow13623 := by decide +kernel

def row13623 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

theorem rowCheck13623 : row13623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13623 := by decide +kernel

theorem rowEval13623 (x : Key → ℝ) : Integer.Sparse.eval row13623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13623, Integer.Sparse.eval_collectBalanced, rawRowCheck13623]

def rawRow13624 : Integer.Sparse Key := [(key2394, 4), (key2524, 4), (key2443, 4), (key2394, -2), (key2383, -2), (key2484, -2), (key2411, -2), (key2509, -2), (key2443, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, 4), (key2472, 4), (key2406, 4)]

theorem rawRowCheck13624 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form0 = rawRow13624 := by decide +kernel

def row13624 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

theorem rowCheck13624 : row13624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13624 := by decide +kernel

theorem rowEval13624 (x : Key → ℝ) : Integer.Sparse.eval row13624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13624, Integer.Sparse.eval_collectBalanced, rawRowCheck13624]

def rawRow13625 : Integer.Sparse Key := [(key2443, 4), (key2394, 4), (key2524, 4), (key2411, -2), (key2443, -2), (key2383, -2), (key2509, -2), (key2394, -2), (key2484, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, 4), (key2378, 4), (key2472, 4)]

theorem rawRowCheck13625 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form0 = rawRow13625 := by decide +kernel

def row13625 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

theorem rowCheck13625 : row13625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13625 := by decide +kernel

theorem rowEval13625 (x : Key → ℝ) : Integer.Sparse.eval row13625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13625, Integer.Sparse.eval_collectBalanced, rawRowCheck13625]

def rawRow13626 : Integer.Sparse Key := [(key2443, 4), (key2524, 4), (key2394, 4), (key2443, -2), (key2411, -2), (key2509, -2), (key2383, -2), (key2484, -2), (key2394, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, 4), (key2472, 4), (key2378, 4)]

theorem rawRowCheck13626 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form0 = rawRow13626 := by decide +kernel

def row13626 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

theorem rowCheck13626 : row13626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13626 := by decide +kernel

theorem rowEval13626 (x : Key → ℝ) : Integer.Sparse.eval row13626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13626, Integer.Sparse.eval_collectBalanced, rawRowCheck13626]

def rawRow13627 : Integer.Sparse Key := [(key2524, 4), (key2394, 4), (key2443, 4), (key2484, -2), (key2509, -2), (key2394, -2), (key2443, -2), (key2383, -2), (key2411, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, 4), (key2378, 4), (key2406, 4)]

theorem rawRowCheck13627 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form0 = rawRow13627 := by decide +kernel

def row13627 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

theorem rowCheck13627 : row13627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13627 := by decide +kernel

theorem rowEval13627 (x : Key → ℝ) : Integer.Sparse.eval row13627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13627, Integer.Sparse.eval_collectBalanced, rawRowCheck13627]

def rawRow13628 : Integer.Sparse Key := [(key2524, 4), (key2443, 4), (key2394, 4), (key2509, -2), (key2484, -2), (key2443, -2), (key2394, -2), (key2411, -2), (key2383, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, 4), (key2406, 4), (key2378, 4)]

theorem rawRowCheck13628 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form0 = rawRow13628 := by decide +kernel

def row13628 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

theorem rowCheck13628 : row13628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13628 := by decide +kernel

theorem rowEval13628 (x : Key → ℝ) : Integer.Sparse.eval row13628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13628, Integer.Sparse.eval_collectBalanced, rawRowCheck13628]

def rawRow13629 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1071, -2), (key1036, 6), (key1106, -2), (key1114, -2), (key1150, -2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1001, -2), (key1114, -2), (key1232, -2), (key1123, 6), (key1015, -2), (key1123, -2), (key1235, -2)]

theorem rawRowCheck13629 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form1 = rawRow13629 := by decide +kernel

def row13629 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13629 : row13629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13629 := by decide +kernel

theorem rowEval13629 (x : Key → ℝ) : Integer.Sparse.eval row13629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13629, Integer.Sparse.eval_collectBalanced, rawRowCheck13629]

def rawRow13630 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1071, -2), (key1036, 6), (key1114, -2), (key1106, -2), (key1150, -2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1001, -2), (key1232, -2), (key1114, -2), (key1123, 6), (key1015, -2), (key1235, -2), (key1123, -2)]

theorem rawRowCheck13630 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form1 = rawRow13630 := by decide +kernel

def row13630 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13630 : row13630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13630 := by decide +kernel

theorem rowEval13630 (x : Key → ℝ) : Integer.Sparse.eval row13630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13630, Integer.Sparse.eval_collectBalanced, rawRowCheck13630]

def rawRow13631 : Integer.Sparse Key := [(key1028, -2), (key1071, -2), (key1036, -2), (key1036, 6), (key1106, -2), (key1150, -2), (key1114, -2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1114, -2), (key1001, -2), (key1232, -2), (key1123, 6), (key1123, -2), (key1015, -2), (key1235, -2)]

theorem rawRowCheck13631 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form1 = rawRow13631 := by decide +kernel

def row13631 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13631 : row13631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13631 := by decide +kernel

theorem rowEval13631 (x : Key → ℝ) : Integer.Sparse.eval row13631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13631, Integer.Sparse.eval_collectBalanced, rawRowCheck13631]

def rawRow13632 : Integer.Sparse Key := [(key1071, -2), (key1028, -2), (key1036, -2), (key1036, 6), (key1150, -2), (key1106, -2), (key1114, -2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1114, -2), (key1232, -2), (key1001, -2), (key1123, 6), (key1123, -2), (key1235, -2), (key1015, -2)]

theorem rawRowCheck13632 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form1 = rawRow13632 := by decide +kernel

def row13632 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13632 : row13632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13632 := by decide +kernel

theorem rowEval13632 (x : Key → ℝ) : Integer.Sparse.eval row13632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13632, Integer.Sparse.eval_collectBalanced, rawRowCheck13632]

def rawRow13633 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1028, -2), (key1036, 6), (key1114, -2), (key1150, -2), (key1106, -2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1232, -2), (key1001, -2), (key1114, -2), (key1123, 6), (key1235, -2), (key1015, -2), (key1123, -2)]

theorem rawRowCheck13633 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form1 = rawRow13633 := by decide +kernel

def row13633 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13633 : row13633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13633 := by decide +kernel

theorem rowEval13633 (x : Key → ℝ) : Integer.Sparse.eval row13633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13633, Integer.Sparse.eval_collectBalanced, rawRowCheck13633]

def rawRow13634 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1028, -2), (key1036, 6), (key1150, -2), (key1114, -2), (key1106, -2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1232, -2), (key1114, -2), (key1001, -2), (key1123, 6), (key1235, -2), (key1123, -2), (key1015, -2)]

theorem rawRowCheck13634 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form1 = rawRow13634 := by decide +kernel

def row13634 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13634 : row13634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13634 := by decide +kernel

theorem rowEval13634 (x : Key → ℝ) : Integer.Sparse.eval row13634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13634, Integer.Sparse.eval_collectBalanced, rawRowCheck13634]

def rawRow13635 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1071, -2), (key1028, 6), (key1232, -2), (key1232, -2), (key1242, -2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1235, 6), (key1015, -2), (key1123, -2), (key1123, -2)]

theorem rawRowCheck13635 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form1 = rawRow13635 := by decide +kernel

def row13635 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

theorem rowCheck13635 : row13635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13635 := by decide +kernel

theorem rowEval13635 (x : Key → ℝ) : Integer.Sparse.eval row13635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13635, Integer.Sparse.eval_collectBalanced, rawRowCheck13635]

def rawRow13636 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1036, -2), (key1028, 6), (key1232, -2), (key1242, -2), (key1232, -2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1235, 6), (key1123, -2), (key1015, -2), (key1123, -2)]

theorem rawRowCheck13636 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form1 = rawRow13636 := by decide +kernel

def row13636 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

theorem rowCheck13636 : row13636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13636 := by decide +kernel

theorem rowEval13636 (x : Key → ℝ) : Integer.Sparse.eval row13636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13636, Integer.Sparse.eval_collectBalanced, rawRowCheck13636]

def rawRow13637 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1036, -2), (key1028, 6), (key1242, -2), (key1232, -2), (key1232, -2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1235, 6), (key1123, -2), (key1123, -2), (key1015, -2)]

theorem rawRowCheck13637 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form1 = rawRow13637 := by decide +kernel

def row13637 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

theorem rowCheck13637 : row13637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13637 := by decide +kernel

theorem rowEval13637 (x : Key → ℝ) : Integer.Sparse.eval row13637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13637, Integer.Sparse.eval_collectBalanced, rawRowCheck13637]

def rawRow13638 : Integer.Sparse Key := [(key1106, -2), (key1114, -2), (key1150, -2), (key1123, 6), (key1028, -2), (key1036, -2), (key1071, -2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1015, -2), (key1123, -2), (key1235, -2), (key1036, 6), (key1001, -2), (key1114, -2), (key1232, -2)]

theorem rawRowCheck13638 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form1 = rawRow13638 := by decide +kernel

def row13638 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13638 : row13638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13638 := by decide +kernel

theorem rowEval13638 (x : Key → ℝ) : Integer.Sparse.eval row13638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13638, Integer.Sparse.eval_collectBalanced, rawRowCheck13638]

def rawRow13639 : Integer.Sparse Key := [(key1114, -2), (key1106, -2), (key1150, -2), (key1123, 6), (key1036, -2), (key1028, -2), (key1071, -2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1015, -2), (key1235, -2), (key1123, -2), (key1036, 6), (key1001, -2), (key1232, -2), (key1114, -2)]

theorem rawRowCheck13639 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form1 = rawRow13639 := by decide +kernel

def row13639 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13639 : row13639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13639 := by decide +kernel

theorem rowEval13639 (x : Key → ℝ) : Integer.Sparse.eval row13639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13639, Integer.Sparse.eval_collectBalanced, rawRowCheck13639]

def rawRow13640 : Integer.Sparse Key := [(key1106, -2), (key1150, -2), (key1114, -2), (key1123, 6), (key1028, -2), (key1071, -2), (key1036, -2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1123, -2), (key1015, -2), (key1235, -2), (key1036, 6), (key1114, -2), (key1001, -2), (key1232, -2)]

theorem rawRowCheck13640 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form1 = rawRow13640 := by decide +kernel

def row13640 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13640 : row13640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13640 := by decide +kernel

theorem rowEval13640 (x : Key → ℝ) : Integer.Sparse.eval row13640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13640, Integer.Sparse.eval_collectBalanced, rawRowCheck13640]

def rawRow13641 : Integer.Sparse Key := [(key1150, -2), (key1106, -2), (key1114, -2), (key1123, 6), (key1071, -2), (key1028, -2), (key1036, -2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1123, -2), (key1235, -2), (key1015, -2), (key1036, 6), (key1114, -2), (key1232, -2), (key1001, -2)]

theorem rawRowCheck13641 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form1 = rawRow13641 := by decide +kernel

def row13641 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13641 : row13641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13641 := by decide +kernel

theorem rowEval13641 (x : Key → ℝ) : Integer.Sparse.eval row13641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13641, Integer.Sparse.eval_collectBalanced, rawRowCheck13641]

def rawRow13642 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1106, -2), (key1123, 6), (key1036, -2), (key1071, -2), (key1028, -2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1235, -2), (key1015, -2), (key1123, -2), (key1036, 6), (key1232, -2), (key1001, -2), (key1114, -2)]

theorem rawRowCheck13642 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form1 = rawRow13642 := by decide +kernel

def row13642 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13642 : row13642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13642 := by decide +kernel

theorem rowEval13642 (x : Key → ℝ) : Integer.Sparse.eval row13642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13642, Integer.Sparse.eval_collectBalanced, rawRowCheck13642]

def rawRow13643 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1106, -2), (key1123, 6), (key1071, -2), (key1036, -2), (key1028, -2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1235, -2), (key1123, -2), (key1015, -2), (key1036, 6), (key1232, -2), (key1114, -2), (key1001, -2)]

theorem rawRowCheck13643 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form1 = rawRow13643 := by decide +kernel

def row13643 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

theorem rowCheck13643 : row13643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13643 := by decide +kernel

theorem rowEval13643 (x : Key → ℝ) : Integer.Sparse.eval row13643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13643, Integer.Sparse.eval_collectBalanced, rawRowCheck13643]

def rawRow13644 : Integer.Sparse Key := [(key1106, -2), (key1123, -2), (key1150, -2), (key1114, 6), (key1106, -2), (key1123, -2), (key1150, -2), (key993, 2), (key1015, 2), (key1028, 2), (key1235, 2), (key1071, 2), (key1242, 2), (key1001, -2), (key1036, -2), (key1232, -2), (key1114, 6), (key1001, -2), (key1036, -2), (key1232, -2)]

theorem rawRowCheck13644 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form1 = rawRow13644 := by decide +kernel

def row13644 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck13644 : row13644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13644 := by decide +kernel

theorem rowEval13644 (x : Key → ℝ) : Integer.Sparse.eval row13644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13644, Integer.Sparse.eval_collectBalanced, rawRowCheck13644]

def rawRow13645 : Integer.Sparse Key := [(key1123, -2), (key1106, -2), (key1150, -2), (key1114, 6), (key1123, -2), (key1106, -2), (key1150, -2), (key1015, 2), (key993, 2), (key1235, 2), (key1028, 2), (key1242, 2), (key1071, 2), (key1001, -2), (key1232, -2), (key1036, -2), (key1114, 6), (key1001, -2), (key1232, -2), (key1036, -2)]

theorem rawRowCheck13645 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form1 = rawRow13645 := by decide +kernel

def row13645 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck13645 : row13645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13645 := by decide +kernel

theorem rowEval13645 (x : Key → ℝ) : Integer.Sparse.eval row13645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13645, Integer.Sparse.eval_collectBalanced, rawRowCheck13645]

def rawRow13646 : Integer.Sparse Key := [(key1106, -2), (key1150, -2), (key1123, -2), (key1114, 6), (key1106, -2), (key1150, -2), (key1123, -2), (key1028, 2), (key1071, 2), (key993, 2), (key1242, 2), (key1015, 2), (key1235, 2), (key1036, -2), (key1001, -2), (key1232, -2), (key1114, 6), (key1036, -2), (key1001, -2), (key1232, -2)]

theorem rawRowCheck13646 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form1 = rawRow13646 := by decide +kernel

def row13646 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck13646 : row13646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13646 := by decide +kernel

theorem rowEval13646 (x : Key → ℝ) : Integer.Sparse.eval row13646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13646, Integer.Sparse.eval_collectBalanced, rawRowCheck13646]

def rawRow13647 : Integer.Sparse Key := [(key1150, -2), (key1106, -2), (key1123, -2), (key1114, 6), (key1150, -2), (key1106, -2), (key1123, -2), (key1071, 2), (key1028, 2), (key1242, 2), (key993, 2), (key1235, 2), (key1015, 2), (key1036, -2), (key1232, -2), (key1001, -2), (key1114, 6), (key1036, -2), (key1232, -2), (key1001, -2)]

theorem rawRowCheck13647 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form1 = rawRow13647 := by decide +kernel

def row13647 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck13647 : row13647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13647 := by decide +kernel

theorem rowEval13647 (x : Key → ℝ) : Integer.Sparse.eval row13647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13647, Integer.Sparse.eval_collectBalanced, rawRowCheck13647]

def rawRow13648 : Integer.Sparse Key := [(key1123, -2), (key1150, -2), (key1106, -2), (key1114, 6), (key1123, -2), (key1150, -2), (key1106, -2), (key1235, 2), (key1242, 2), (key1015, 2), (key1071, 2), (key993, 2), (key1028, 2), (key1232, -2), (key1001, -2), (key1036, -2), (key1114, 6), (key1232, -2), (key1001, -2), (key1036, -2)]

theorem rawRowCheck13648 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form1 = rawRow13648 := by decide +kernel

def row13648 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck13648 : row13648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13648 := by decide +kernel

theorem rowEval13648 (x : Key → ℝ) : Integer.Sparse.eval row13648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13648, Integer.Sparse.eval_collectBalanced, rawRowCheck13648]

def rawRow13649 : Integer.Sparse Key := [(key1150, -2), (key1123, -2), (key1106, -2), (key1114, 6), (key1150, -2), (key1123, -2), (key1106, -2), (key1242, 2), (key1235, 2), (key1071, 2), (key1015, 2), (key1028, 2), (key993, 2), (key1232, -2), (key1036, -2), (key1001, -2), (key1114, 6), (key1232, -2), (key1036, -2), (key1001, -2)]

theorem rawRowCheck13649 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form1 = rawRow13649 := by decide +kernel

def row13649 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

theorem rowCheck13649 : row13649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13649 := by decide +kernel

theorem rowEval13649 (x : Key → ℝ) : Integer.Sparse.eval row13649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13649, Integer.Sparse.eval_collectBalanced, rawRowCheck13649]

def rawRow13650 : Integer.Sparse Key := [(key1114, -2), (key1123, -2), (key1150, -2), (key1106, 6), (key1232, -2), (key1235, -2), (key1242, -2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1232, 6), (key1001, -2), (key1036, -2), (key1114, -2)]

theorem rawRowCheck13650 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form1 = rawRow13650 := by decide +kernel

def row13650 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13650 : row13650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13650 := by decide +kernel

theorem rowEval13650 (x : Key → ℝ) : Integer.Sparse.eval row13650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13650, Integer.Sparse.eval_collectBalanced, rawRowCheck13650]

def rawRow13651 : Integer.Sparse Key := [(key1123, -2), (key1114, -2), (key1150, -2), (key1106, 6), (key1235, -2), (key1232, -2), (key1242, -2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1232, 6), (key1001, -2), (key1114, -2), (key1036, -2)]

theorem rawRowCheck13651 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form1 = rawRow13651 := by decide +kernel

def row13651 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13651 : row13651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13651 := by decide +kernel

theorem rowEval13651 (x : Key → ℝ) : Integer.Sparse.eval row13651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13651, Integer.Sparse.eval_collectBalanced, rawRowCheck13651]

def rawRow13652 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1123, -2), (key1106, 6), (key1232, -2), (key1242, -2), (key1235, -2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1232, 6), (key1036, -2), (key1001, -2), (key1114, -2)]

theorem rawRowCheck13652 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form1 = rawRow13652 := by decide +kernel

def row13652 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13652 : row13652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13652 := by decide +kernel

theorem rowEval13652 (x : Key → ℝ) : Integer.Sparse.eval row13652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13652, Integer.Sparse.eval_collectBalanced, rawRowCheck13652]

def rawRow13653 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1123, -2), (key1106, 6), (key1242, -2), (key1232, -2), (key1235, -2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1232, 6), (key1036, -2), (key1114, -2), (key1001, -2)]

theorem rawRowCheck13653 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form1 = rawRow13653 := by decide +kernel

def row13653 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13653 : row13653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13653 := by decide +kernel

theorem rowEval13653 (x : Key → ℝ) : Integer.Sparse.eval row13653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13653, Integer.Sparse.eval_collectBalanced, rawRowCheck13653]

def rawRow13654 : Integer.Sparse Key := [(key1123, -2), (key1150, -2), (key1114, -2), (key1106, 6), (key1235, -2), (key1242, -2), (key1232, -2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1232, 6), (key1114, -2), (key1001, -2), (key1036, -2)]

theorem rawRowCheck13654 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form1 = rawRow13654 := by decide +kernel

def row13654 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13654 : row13654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13654 := by decide +kernel

theorem rowEval13654 (x : Key → ℝ) : Integer.Sparse.eval row13654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13654, Integer.Sparse.eval_collectBalanced, rawRowCheck13654]

def rawRow13655 : Integer.Sparse Key := [(key1150, -2), (key1123, -2), (key1114, -2), (key1106, 6), (key1242, -2), (key1235, -2), (key1232, -2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1232, 6), (key1114, -2), (key1036, -2), (key1001, -2)]

theorem rawRowCheck13655 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form1 = rawRow13655 := by decide +kernel

def row13655 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13655 : row13655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13655 := by decide +kernel

theorem rowEval13655 (x : Key → ℝ) : Integer.Sparse.eval row13655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13655, Integer.Sparse.eval_collectBalanced, rawRowCheck13655]

def rawRow13656 : Integer.Sparse Key := [(key1232, -2), (key1232, -2), (key1242, -2), (key1235, 6), (key1036, -2), (key1036, -2), (key1071, -2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key1015, -2), (key1123, -2), (key1123, -2), (key1028, 6), (key993, -2), (key1106, -2), (key1106, -2)]

theorem rawRowCheck13656 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form1 = rawRow13656 := by decide +kernel

def row13656 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

theorem rowCheck13656 : row13656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13656 := by decide +kernel

theorem rowEval13656 (x : Key → ℝ) : Integer.Sparse.eval row13656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13656, Integer.Sparse.eval_collectBalanced, rawRowCheck13656]

def rawRow13657 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1232, -2), (key1235, 6), (key1036, -2), (key1071, -2), (key1036, -2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1123, -2), (key1015, -2), (key1123, -2), (key1028, 6), (key1106, -2), (key993, -2), (key1106, -2)]

theorem rawRowCheck13657 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form1 = rawRow13657 := by decide +kernel

def row13657 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

theorem rowCheck13657 : row13657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13657 := by decide +kernel

theorem rowEval13657 (x : Key → ℝ) : Integer.Sparse.eval row13657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13657, Integer.Sparse.eval_collectBalanced, rawRowCheck13657]

def rawRow13658 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1232, -2), (key1235, 6), (key1071, -2), (key1036, -2), (key1036, -2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1123, -2), (key1123, -2), (key1015, -2), (key1028, 6), (key1106, -2), (key1106, -2), (key993, -2)]

theorem rawRowCheck13658 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form1 = rawRow13658 := by decide +kernel

def row13658 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

theorem rowCheck13658 : row13658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13658 := by decide +kernel

theorem rowEval13658 (x : Key → ℝ) : Integer.Sparse.eval row13658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13658, Integer.Sparse.eval_collectBalanced, rawRowCheck13658]

def rawRow13659 : Integer.Sparse Key := [(key1232, -2), (key1235, -2), (key1242, -2), (key1232, 6), (key1114, -2), (key1123, -2), (key1150, -2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key1001, -2), (key1036, -2), (key1114, -2), (key1106, 6), (key993, -2), (key1028, -2), (key1106, -2)]

theorem rawRowCheck13659 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form1 = rawRow13659 := by decide +kernel

def row13659 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13659 : row13659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13659 := by decide +kernel

theorem rowEval13659 (x : Key → ℝ) : Integer.Sparse.eval row13659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13659, Integer.Sparse.eval_collectBalanced, rawRowCheck13659]

def rawRow13660 : Integer.Sparse Key := [(key1235, -2), (key1232, -2), (key1242, -2), (key1232, 6), (key1123, -2), (key1114, -2), (key1150, -2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key1001, -2), (key1114, -2), (key1036, -2), (key1106, 6), (key993, -2), (key1106, -2), (key1028, -2)]

theorem rawRowCheck13660 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form1 = rawRow13660 := by decide +kernel

def row13660 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13660 : row13660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13660 := by decide +kernel

theorem rowEval13660 (x : Key → ℝ) : Integer.Sparse.eval row13660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13660, Integer.Sparse.eval_collectBalanced, rawRowCheck13660]

def rawRow13661 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1235, -2), (key1232, 6), (key1114, -2), (key1150, -2), (key1123, -2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1036, -2), (key1001, -2), (key1114, -2), (key1106, 6), (key1028, -2), (key993, -2), (key1106, -2)]

theorem rawRowCheck13661 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form1 = rawRow13661 := by decide +kernel

def row13661 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13661 : row13661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13661 := by decide +kernel

theorem rowEval13661 (x : Key → ℝ) : Integer.Sparse.eval row13661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13661, Integer.Sparse.eval_collectBalanced, rawRowCheck13661]

def rawRow13662 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1235, -2), (key1232, 6), (key1150, -2), (key1114, -2), (key1123, -2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1036, -2), (key1114, -2), (key1001, -2), (key1106, 6), (key1028, -2), (key1106, -2), (key993, -2)]

theorem rawRowCheck13662 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form1 = rawRow13662 := by decide +kernel

def row13662 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13662 : row13662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13662 := by decide +kernel

theorem rowEval13662 (x : Key → ℝ) : Integer.Sparse.eval row13662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13662, Integer.Sparse.eval_collectBalanced, rawRowCheck13662]

def rawRow13663 : Integer.Sparse Key := [(key1235, -2), (key1242, -2), (key1232, -2), (key1232, 6), (key1123, -2), (key1150, -2), (key1114, -2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1114, -2), (key1001, -2), (key1036, -2), (key1106, 6), (key1106, -2), (key993, -2), (key1028, -2)]

theorem rawRowCheck13663 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form1 = rawRow13663 := by decide +kernel

def row13663 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13663 : row13663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13663 := by decide +kernel

theorem rowEval13663 (x : Key → ℝ) : Integer.Sparse.eval row13663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13663, Integer.Sparse.eval_collectBalanced, rawRowCheck13663]

def rawRow13664 : Integer.Sparse Key := [(key1242, -2), (key1235, -2), (key1232, -2), (key1232, 6), (key1150, -2), (key1123, -2), (key1114, -2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1114, -2), (key1036, -2), (key1001, -2), (key1106, 6), (key1106, -2), (key1028, -2), (key993, -2)]

theorem rawRowCheck13664 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form1 = rawRow13664 := by decide +kernel

def row13664 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, -2), (key1071, 2), (key1106, 4), (key1114, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck13664 : row13664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13664 := by decide +kernel

theorem rowEval13664 (x : Key → ℝ) : Integer.Sparse.eval row13664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13664, Integer.Sparse.eval_collectBalanced, rawRowCheck13664]

def rawRow13665 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2404, 6), (key2839, -2), (key2845, -2), (key3019, -2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2589, -2), (key2845, -2), (key2876, -2), (key2916, 6), (key2604, -2), (key2916, -2), (key2925, -2)]

theorem rawRowCheck13665 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form2 = rawRow13665 := by decide +kernel

def row13665 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

theorem rowCheck13665 : row13665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13665 := by decide +kernel

theorem rowEval13665 (x : Key → ℝ) : Integer.Sparse.eval row13665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13665, Integer.Sparse.eval_collectBalanced, rawRowCheck13665]

def rawRow13666 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2435, -2), (key2404, 6), (key2845, -2), (key2839, -2), (key3019, -2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2589, -2), (key2876, -2), (key2845, -2), (key2916, 6), (key2604, -2), (key2925, -2), (key2916, -2)]

theorem rawRowCheck13666 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form2 = rawRow13666 := by decide +kernel

def row13666 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

theorem rowCheck13666 : row13666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13666 := by decide +kernel

theorem rowEval13666 (x : Key → ℝ) : Integer.Sparse.eval row13666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13666, Integer.Sparse.eval_collectBalanced, rawRowCheck13666]

def rawRow13667 : Integer.Sparse Key := [(key2398, -2), (key2435, -2), (key2404, -2), (key2404, 6), (key2839, -2), (key3019, -2), (key2845, -2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2845, -2), (key2589, -2), (key2876, -2), (key2916, 6), (key2916, -2), (key2604, -2), (key2925, -2)]

theorem rawRowCheck13667 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form2 = rawRow13667 := by decide +kernel

def row13667 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

theorem rowCheck13667 : row13667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13667 := by decide +kernel

theorem rowEval13667 (x : Key → ℝ) : Integer.Sparse.eval row13667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13667, Integer.Sparse.eval_collectBalanced, rawRowCheck13667]

def rawRow13668 : Integer.Sparse Key := [(key2435, -2), (key2398, -2), (key2404, -2), (key2404, 6), (key3019, -2), (key2839, -2), (key2845, -2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2845, -2), (key2876, -2), (key2589, -2), (key2916, 6), (key2916, -2), (key2925, -2), (key2604, -2)]

theorem rawRowCheck13668 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form2 = rawRow13668 := by decide +kernel

def row13668 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

theorem rowCheck13668 : row13668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13668 := by decide +kernel

theorem rowEval13668 (x : Key → ℝ) : Integer.Sparse.eval row13668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13668, Integer.Sparse.eval_collectBalanced, rawRowCheck13668]

def rawRow13669 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2398, -2), (key2404, 6), (key2845, -2), (key3019, -2), (key2839, -2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2876, -2), (key2589, -2), (key2845, -2), (key2916, 6), (key2925, -2), (key2604, -2), (key2916, -2)]

theorem rawRowCheck13669 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form2 = rawRow13669 := by decide +kernel

def row13669 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

theorem rowCheck13669 : row13669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13669 := by decide +kernel

theorem rowEval13669 (x : Key → ℝ) : Integer.Sparse.eval row13669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13669, Integer.Sparse.eval_collectBalanced, rawRowCheck13669]

def rawRow13670 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2398, -2), (key2404, 6), (key3019, -2), (key2845, -2), (key2839, -2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2876, -2), (key2845, -2), (key2589, -2), (key2916, 6), (key2925, -2), (key2916, -2), (key2604, -2)]

theorem rawRowCheck13670 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form2 = rawRow13670 := by decide +kernel

def row13670 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

theorem rowCheck13670 : row13670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13670 := by decide +kernel

theorem rowEval13670 (x : Key → ℝ) : Integer.Sparse.eval row13670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13670, Integer.Sparse.eval_collectBalanced, rawRowCheck13670]

def rawRow13671 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2435, -2), (key2398, 6), (key2876, -2), (key2876, -2), (key3028, -2), (key2589, 2), (key2589, 2), (key2845, 2), (key2845, 2), (key3019, 2), (key3019, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2925, 6), (key2604, -2), (key2916, -2), (key2916, -2)]

theorem rawRowCheck13671 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form2 = rawRow13671 := by decide +kernel

def row13671 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2589, 4), (key2604, -2), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, -4), (key2925, 6), (key3019, 4), (key3028, -2)]

theorem rowCheck13671 : row13671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13671 := by decide +kernel

theorem rowEval13671 (x : Key → ℝ) : Integer.Sparse.eval row13671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13671, Integer.Sparse.eval_collectBalanced, rawRowCheck13671]

def rawRow13672 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2404, -2), (key2398, 6), (key2876, -2), (key3028, -2), (key2876, -2), (key2845, 2), (key3019, 2), (key2589, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2925, 6), (key2916, -2), (key2604, -2), (key2916, -2)]

theorem rawRowCheck13672 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form2 = rawRow13672 := by decide +kernel

def row13672 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2589, 4), (key2604, -2), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, -4), (key2925, 6), (key3019, 4), (key3028, -2)]

theorem rowCheck13672 : row13672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13672 := by decide +kernel

theorem rowEval13672 (x : Key → ℝ) : Integer.Sparse.eval row13672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13672, Integer.Sparse.eval_collectBalanced, rawRowCheck13672]

def rawRow13673 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2404, -2), (key2398, 6), (key3028, -2), (key2876, -2), (key2876, -2), (key3019, 2), (key2845, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2589, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2925, 6), (key2916, -2), (key2916, -2), (key2604, -2)]

theorem rawRowCheck13673 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form2 = rawRow13673 := by decide +kernel

def row13673 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2589, 4), (key2604, -2), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, -4), (key2925, 6), (key3019, 4), (key3028, -2)]

theorem rowCheck13673 : row13673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13673 := by decide +kernel

theorem rowEval13673 (x : Key → ℝ) : Integer.Sparse.eval row13673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13673, Integer.Sparse.eval_collectBalanced, rawRowCheck13673]

def rawRow13674 : Integer.Sparse Key := [(key2464, -2), (key2470, -2), (key2501, -2), (key2478, 6), (key2398, -2), (key2404, -2), (key2435, -2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2604, -2), (key2916, -2), (key2925, -2), (key2768, 6), (key2589, -2), (key2845, -2), (key2876, -2)]

theorem rawRowCheck13674 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form2 = rawRow13674 := by decide +kernel

def row13674 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

theorem rowCheck13674 : row13674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13674 := by decide +kernel

theorem rowEval13674 (x : Key → ℝ) : Integer.Sparse.eval row13674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13674, Integer.Sparse.eval_collectBalanced, rawRowCheck13674]

def rawRow13675 : Integer.Sparse Key := [(key2470, -2), (key2464, -2), (key2501, -2), (key2478, 6), (key2404, -2), (key2398, -2), (key2435, -2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2604, -2), (key2925, -2), (key2916, -2), (key2768, 6), (key2589, -2), (key2876, -2), (key2845, -2)]

theorem rawRowCheck13675 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form2 = rawRow13675 := by decide +kernel

def row13675 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

theorem rowCheck13675 : row13675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13675 := by decide +kernel

theorem rowEval13675 (x : Key → ℝ) : Integer.Sparse.eval row13675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13675, Integer.Sparse.eval_collectBalanced, rawRowCheck13675]

def rawRow13676 : Integer.Sparse Key := [(key2464, -2), (key2501, -2), (key2470, -2), (key2478, 6), (key2398, -2), (key2435, -2), (key2404, -2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2916, -2), (key2604, -2), (key2925, -2), (key2768, 6), (key2845, -2), (key2589, -2), (key2876, -2)]

theorem rawRowCheck13676 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form2 = rawRow13676 := by decide +kernel

def row13676 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

theorem rowCheck13676 : row13676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13676 := by decide +kernel

theorem rowEval13676 (x : Key → ℝ) : Integer.Sparse.eval row13676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13676, Integer.Sparse.eval_collectBalanced, rawRowCheck13676]

def rawRow13677 : Integer.Sparse Key := [(key2501, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2435, -2), (key2398, -2), (key2404, -2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2916, -2), (key2925, -2), (key2604, -2), (key2768, 6), (key2845, -2), (key2876, -2), (key2589, -2)]

theorem rawRowCheck13677 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form2 = rawRow13677 := by decide +kernel

def row13677 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

theorem rowCheck13677 : row13677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13677 := by decide +kernel

theorem rowEval13677 (x : Key → ℝ) : Integer.Sparse.eval row13677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13677, Integer.Sparse.eval_collectBalanced, rawRowCheck13677]

def rawRow13678 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2464, -2), (key2478, 6), (key2404, -2), (key2435, -2), (key2398, -2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2925, -2), (key2604, -2), (key2916, -2), (key2768, 6), (key2876, -2), (key2589, -2), (key2845, -2)]

theorem rawRowCheck13678 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form2 = rawRow13678 := by decide +kernel

def row13678 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

theorem rowCheck13678 : row13678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13678 := by decide +kernel

theorem rowEval13678 (x : Key → ℝ) : Integer.Sparse.eval row13678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13678, Integer.Sparse.eval_collectBalanced, rawRowCheck13678]

def rawRow13679 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2464, -2), (key2478, 6), (key2435, -2), (key2404, -2), (key2398, -2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2925, -2), (key2916, -2), (key2604, -2), (key2768, 6), (key2876, -2), (key2845, -2), (key2589, -2)]

theorem rawRowCheck13679 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form2 = rawRow13679 := by decide +kernel

def row13679 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

theorem rowCheck13679 : row13679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13679 := by decide +kernel

theorem rowEval13679 (x : Key → ℝ) : Integer.Sparse.eval row13679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13679, Integer.Sparse.eval_collectBalanced, rawRowCheck13679]

def rawRow13680 : Integer.Sparse Key := [(key2464, -2), (key2478, -2), (key2501, -2), (key2470, 6), (key2464, -2), (key2478, -2), (key2501, -2), (key2370, 2), (key2388, 2), (key2762, 2), (key2925, 2), (key3005, 2), (key3028, 2), (key2589, -2), (key2768, -2), (key2876, -2), (key2845, 6), (key2589, -2), (key2768, -2), (key2876, -2)]

theorem rawRowCheck13680 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form2 = rawRow13680 := by decide +kernel

def row13680 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2589, -4), (key2762, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3005, 2), (key3028, 2)]

theorem rowCheck13680 : row13680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13680 := by decide +kernel

theorem rowEval13680 (x : Key → ℝ) : Integer.Sparse.eval row13680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13680, Integer.Sparse.eval_collectBalanced, rawRowCheck13680]

def rawRow13681 : Integer.Sparse Key := [(key2478, -2), (key2464, -2), (key2501, -2), (key2470, 6), (key2478, -2), (key2464, -2), (key2501, -2), (key2388, 2), (key2370, 2), (key2925, 2), (key2762, 2), (key3028, 2), (key3005, 2), (key2589, -2), (key2876, -2), (key2768, -2), (key2845, 6), (key2589, -2), (key2876, -2), (key2768, -2)]

theorem rawRowCheck13681 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form2 = rawRow13681 := by decide +kernel

def row13681 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2589, -4), (key2762, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3005, 2), (key3028, 2)]

theorem rowCheck13681 : row13681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13681 := by decide +kernel

theorem rowEval13681 (x : Key → ℝ) : Integer.Sparse.eval row13681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13681, Integer.Sparse.eval_collectBalanced, rawRowCheck13681]

def rawRow13682 : Integer.Sparse Key := [(key2464, -2), (key2501, -2), (key2478, -2), (key2470, 6), (key2464, -2), (key2501, -2), (key2478, -2), (key2398, 2), (key2435, 2), (key2583, 2), (key3028, 2), (key2604, 2), (key2925, 2), (key2768, -2), (key2589, -2), (key2876, -2), (key2845, 6), (key2768, -2), (key2589, -2), (key2876, -2)]

theorem rawRowCheck13682 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form2 = rawRow13682 := by decide +kernel

def row13682 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, -4), (key2604, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3028, 2)]

theorem rowCheck13682 : row13682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13682 := by decide +kernel

theorem rowEval13682 (x : Key → ℝ) : Integer.Sparse.eval row13682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13682, Integer.Sparse.eval_collectBalanced, rawRowCheck13682]

def rawRow13683 : Integer.Sparse Key := [(key2501, -2), (key2464, -2), (key2478, -2), (key2470, 6), (key2501, -2), (key2464, -2), (key2478, -2), (key2435, 2), (key2398, 2), (key3028, 2), (key2583, 2), (key2925, 2), (key2604, 2), (key2768, -2), (key2876, -2), (key2589, -2), (key2845, 6), (key2768, -2), (key2876, -2), (key2589, -2)]

theorem rawRowCheck13683 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form2 = rawRow13683 := by decide +kernel

def row13683 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, -4), (key2604, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3028, 2)]

theorem rowCheck13683 : row13683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13683 := by decide +kernel

theorem rowEval13683 (x : Key → ℝ) : Integer.Sparse.eval row13683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13683, Integer.Sparse.eval_collectBalanced, rawRowCheck13683]

def rawRow13684 : Integer.Sparse Key := [(key2478, -2), (key2501, -2), (key2464, -2), (key2470, 6), (key2478, -2), (key2501, -2), (key2464, -2), (key2570, 2), (key2575, 2), (key2388, 2), (key2435, 2), (key2370, 2), (key2762, 2), (key2876, -2), (key2589, -2), (key2768, -2), (key2845, 6), (key2876, -2), (key2589, -2), (key2768, -2)]

theorem rawRowCheck13684 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form2 = rawRow13684 := by decide +kernel

def row13684 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2589, -4), (key2762, 2), (key2768, -4), (key2845, 6), (key2876, -4)]

theorem rowCheck13684 : row13684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13684 := by decide +kernel

theorem rowEval13684 (x : Key → ℝ) : Integer.Sparse.eval row13684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13684, Integer.Sparse.eval_collectBalanced, rawRowCheck13684]

def rawRow13685 : Integer.Sparse Key := [(key2501, -2), (key2478, -2), (key2464, -2), (key2470, 6), (key2501, -2), (key2478, -2), (key2464, -2), (key2575, 2), (key2570, 2), (key2435, 2), (key2388, 2), (key2398, 2), (key2583, 2), (key2876, -2), (key2768, -2), (key2589, -2), (key2845, 6), (key2876, -2), (key2768, -2), (key2589, -2)]

theorem rawRowCheck13685 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form2 = rawRow13685 := by decide +kernel

def row13685 : Integer.Sparse Key := [(key2388, 2), (key2398, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2583, 2), (key2589, -4), (key2768, -4), (key2845, 6), (key2876, -4)]

theorem rowCheck13685 : row13685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13685 := by decide +kernel

theorem rowEval13685 (x : Key → ℝ) : Integer.Sparse.eval row13685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13685, Integer.Sparse.eval_collectBalanced, rawRowCheck13685]

def rawRow13686 : Integer.Sparse Key := [(key2470, -2), (key2478, -2), (key2501, -2), (key2464, 6), (key2568, -2), (key2570, -2), (key2575, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2876, 6), (key2589, -2), (key2768, -2), (key2845, -2)]

theorem rawRowCheck13686 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form2 = rawRow13686 := by decide +kernel

def row13686 : Integer.Sparse Key := [(key2370, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, 6), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2589, -2), (key2762, -2), (key2768, -2), (key2839, -2), (key2845, -2), (key2876, 6)]

theorem rowCheck13686 : row13686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13686 := by decide +kernel

theorem rowEval13686 (x : Key → ℝ) : Integer.Sparse.eval row13686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13686, Integer.Sparse.eval_collectBalanced, rawRowCheck13686]

def rawRow13687 : Integer.Sparse Key := [(key2478, -2), (key2470, -2), (key2501, -2), (key2464, 6), (key2570, -2), (key2568, -2), (key2575, -2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2876, 6), (key2589, -2), (key2845, -2), (key2768, -2)]

theorem rawRowCheck13687 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form2 = rawRow13687 := by decide +kernel

def row13687 : Integer.Sparse Key := [(key2370, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, 6), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2589, -2), (key2762, -2), (key2768, -2), (key2839, -2), (key2845, -2), (key2876, 6)]

theorem rowCheck13687 : row13687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13687 := by decide +kernel

theorem rowEval13687 (x : Key → ℝ) : Integer.Sparse.eval row13687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13687, Integer.Sparse.eval_collectBalanced, rawRowCheck13687]

def rawRow13688 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2478, -2), (key2464, 6), (key2568, -2), (key2575, -2), (key2570, -2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2876, 6), (key2768, -2), (key2589, -2), (key2845, -2)]

theorem rawRowCheck13688 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form2 = rawRow13688 := by decide +kernel

def row13688 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, -2), (key2404, 2), (key2435, 2), (key2464, 6), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2583, -2), (key2589, -2), (key2768, -2), (key2839, -2), (key2845, -2), (key2876, 6)]

theorem rowCheck13688 : row13688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13688 := by decide +kernel

theorem rowEval13688 (x : Key → ℝ) : Integer.Sparse.eval row13688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13688, Integer.Sparse.eval_collectBalanced, rawRowCheck13688]

def rawRow13689 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2478, -2), (key2464, 6), (key2575, -2), (key2568, -2), (key2570, -2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2876, 6), (key2768, -2), (key2845, -2), (key2589, -2)]

theorem rawRowCheck13689 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form2 = rawRow13689 := by decide +kernel

def row13689 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, -2), (key2404, 2), (key2435, 2), (key2464, 6), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2583, -2), (key2589, -2), (key2768, -2), (key2839, -2), (key2845, -2), (key2876, 6)]

theorem rowCheck13689 : row13689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13689 := by decide +kernel

theorem rowEval13689 (x : Key → ℝ) : Integer.Sparse.eval row13689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13689, Integer.Sparse.eval_collectBalanced, rawRowCheck13689]

def rawRow13690 : Integer.Sparse Key := [(key2478, -2), (key2501, -2), (key2470, -2), (key2464, 6), (key2570, -2), (key2575, -2), (key2568, -2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2876, 6), (key2845, -2), (key2589, -2), (key2768, -2)]

theorem rawRowCheck13690 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form2 = rawRow13690 := by decide +kernel

def row13690 : Integer.Sparse Key := [(key2370, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, 4), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2589, -2), (key2762, -2), (key2768, -2), (key2845, -2), (key2876, 6)]

theorem rowCheck13690 : row13690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13690 := by decide +kernel

theorem rowEval13690 (x : Key → ℝ) : Integer.Sparse.eval row13690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13690, Integer.Sparse.eval_collectBalanced, rawRowCheck13690]

def rawRow13691 : Integer.Sparse Key := [(key2501, -2), (key2478, -2), (key2470, -2), (key2464, 6), (key2575, -2), (key2570, -2), (key2568, -2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2876, 6), (key2845, -2), (key2768, -2), (key2589, -2)]

theorem rawRowCheck13691 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form2 = rawRow13691 := by decide +kernel

def row13691 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, -2), (key2404, 2), (key2435, 2), (key2464, 4), (key2470, -2), (key2568, -2), (key2570, -2), (key2575, -2), (key2583, -2), (key2589, -2), (key2768, -2), (key2845, -2), (key2876, 6)]

theorem rowCheck13691 : row13691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13691 := by decide +kernel

theorem rowEval13691 (x : Key → ℝ) : Integer.Sparse.eval row13691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13691, Integer.Sparse.eval_collectBalanced, rawRowCheck13691]

def rawRow13692 : Integer.Sparse Key := [(key2568, -2), (key2568, -2), (key2575, -2), (key2570, 6), (key2404, -2), (key2404, -2), (key2435, -2), (key2376, 2), (key2376, 2), (key2470, 2), (key2470, 2), (key2501, 2), (key2501, 2), (key2388, -2), (key2478, -2), (key2478, -2), (key2398, 6), (key2583, -2), (key2839, -2), (key2839, -2)]

theorem rawRowCheck13692 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form2 = rawRow13692 := by decide +kernel

def row13692 : Integer.Sparse Key := [(key2376, 4), (key2388, -2), (key2398, 6), (key2404, -4), (key2435, -2), (key2470, 4), (key2478, -4), (key2501, 4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, -2), (key2839, -4)]

theorem rowCheck13692 : row13692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13692 := by decide +kernel

theorem rowEval13692 (x : Key → ℝ) : Integer.Sparse.eval row13692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13692, Integer.Sparse.eval_collectBalanced, rawRowCheck13692]

def rawRow13693 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2568, -2), (key2570, 6), (key2404, -2), (key2435, -2), (key2404, -2), (key2470, 2), (key2501, 2), (key2376, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2478, -2), (key2388, -2), (key2478, -2), (key2398, 6), (key2839, -2), (key2583, -2), (key2839, -2)]

theorem rawRowCheck13693 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form2 = rawRow13693 := by decide +kernel

def row13693 : Integer.Sparse Key := [(key2376, 4), (key2388, -2), (key2398, 6), (key2404, -4), (key2435, -2), (key2470, 4), (key2478, -4), (key2501, 4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, -2), (key2839, -4)]

theorem rowCheck13693 : row13693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13693 := by decide +kernel

theorem rowEval13693 (x : Key → ℝ) : Integer.Sparse.eval row13693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13693, Integer.Sparse.eval_collectBalanced, rawRowCheck13693]

def rawRow13694 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2568, -2), (key2570, 6), (key2435, -2), (key2404, -2), (key2404, -2), (key2501, 2), (key2470, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2376, 2), (key2478, -2), (key2478, -2), (key2388, -2), (key2398, 6), (key2839, -2), (key2839, -2), (key2583, -2)]

theorem rawRowCheck13694 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form2 = rawRow13694 := by decide +kernel

def row13694 : Integer.Sparse Key := [(key2376, 4), (key2388, -2), (key2398, 6), (key2404, -4), (key2435, -2), (key2470, 4), (key2478, -4), (key2501, 4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, -2), (key2839, -4)]

theorem rowCheck13694 : row13694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13694 := by decide +kernel

theorem rowEval13694 (x : Key → ℝ) : Integer.Sparse.eval row13694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13694, Integer.Sparse.eval_collectBalanced, rawRowCheck13694]

def rawRow13695 : Integer.Sparse Key := [(key2568, -2), (key2570, -2), (key2575, -2), (key2568, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2376, -2), (key2404, -2), (key2470, -2), (key2464, 6), (key2370, -2), (key2762, -2), (key2839, -2)]

theorem rawRowCheck13695 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form2 = rawRow13695 := by decide +kernel

def row13695 : Integer.Sparse Key := [(key2370, -2), (key2388, 2), (key2435, 2), (key2464, 6), (key2470, -4), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, -2), (key2839, -2)]

theorem rowCheck13695 : row13695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13695 := by decide +kernel

theorem rowEval13695 (x : Key → ℝ) : Integer.Sparse.eval row13695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13695, Integer.Sparse.eval_collectBalanced, rawRowCheck13695]

end MUB6.Certificate.GramRows

end OAI

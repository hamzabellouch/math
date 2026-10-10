import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
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

def rawRow7424 : Integer.Sparse Key := [(key151, -6), (key84, -6), (key90, -6), (key90, -6), (key151, 2), (key84, 2), (key90, 2), (key151, 2), (key84, 2), (key202, 2), (key1, 2), (key151, 2), (key7, 2), (key90, 2), (key151, 2), (key7, 2)]

theorem rawRowCheck7424 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form2 = rawRow7424 := by decide +kernel

def row7424 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, 2), (key202, 2)]

theorem rowCheck7424 : row7424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7424 := by decide +kernel

theorem rowEval7424 (x : Key → ℝ) : Integer.Sparse.eval row7424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7424, Integer.Sparse.eval_collectBalanced, rawRowCheck7424]

def rawRow7425 : Integer.Sparse Key := [(key90, -6), (key151, -6), (key84, -6), (key90, -6), (key90, 2), (key151, 2), (key84, 2), (key193, 2), (key202, 2), (key7, 2), (key151, 2), (key1, 2), (key84, 2), (key151, 2), (key7, 2), (key90, 2)]

theorem rawRowCheck7425 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form2 = rawRow7425 := by decide +kernel

def row7425 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

theorem rowCheck7425 : row7425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7425 := by decide +kernel

theorem rowEval7425 (x : Key → ℝ) : Integer.Sparse.eval row7425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7425, Integer.Sparse.eval_collectBalanced, rawRowCheck7425]

def rawRow7426 : Integer.Sparse Key := [(key151, -6), (key90, -6), (key84, -6), (key90, -6), (key151, 2), (key90, 2), (key84, 2), (key202, 2), (key193, 2), (key151, 2), (key7, 2), (key84, 2), (key1, 2), (key151, 2), (key90, 2), (key7, 2)]

theorem rawRowCheck7426 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form2 = rawRow7426 := by decide +kernel

def row7426 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

theorem rowCheck7426 : row7426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7426 := by decide +kernel

theorem rowEval7426 (x : Key → ℝ) : Integer.Sparse.eval row7426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7426, Integer.Sparse.eval_collectBalanced, rawRowCheck7426]

def rawRow7427 : Integer.Sparse Key := [(key90, -6), (key90, -6), (key151, -6), (key84, -6), (key193, 2), (key193, 2), (key202, 2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key1, 2), (key84, 2), (key84, 2)]

theorem rawRowCheck7427 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form2 = rawRow7427 := by decide +kernel

def row7427 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

theorem rowCheck7427 : row7427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7427 := by decide +kernel

theorem rowEval7427 (x : Key → ℝ) : Integer.Sparse.eval row7427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7427, Integer.Sparse.eval_collectBalanced, rawRowCheck7427]

def rawRow7428 : Integer.Sparse Key := [(key90, -6), (key151, -6), (key90, -6), (key84, -6), (key193, 2), (key202, 2), (key193, 2), (key90, 2), (key151, 2), (key7, 2), (key151, 2), (key7, 2), (key90, 2), (key84, 2), (key1, 2), (key84, 2)]

theorem rawRowCheck7428 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form2 = rawRow7428 := by decide +kernel

def row7428 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

theorem rowCheck7428 : row7428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7428 := by decide +kernel

theorem rowEval7428 (x : Key → ℝ) : Integer.Sparse.eval row7428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7428, Integer.Sparse.eval_collectBalanced, rawRowCheck7428]

def rawRow7429 : Integer.Sparse Key := [(key151, -6), (key90, -6), (key90, -6), (key84, -6), (key202, 2), (key193, 2), (key193, 2), (key151, 2), (key90, 2), (key151, 2), (key7, 2), (key90, 2), (key7, 2), (key84, 2), (key84, 2), (key1, 2)]

theorem rawRowCheck7429 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form2 = rawRow7429 := by decide +kernel

def row7429 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

theorem rowCheck7429 : row7429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7429 := by decide +kernel

theorem rowEval7429 (x : Key → ℝ) : Integer.Sparse.eval row7429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7429, Integer.Sparse.eval_collectBalanced, rawRowCheck7429]

def rawRow7430 : Integer.Sparse Key := [(key2377, 2), (key2377, 2), (key2377, 2), (key2471, 2), (key2471, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2389, -2), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2518, -2)]

theorem rawRowCheck7430 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7430 := by decide +kernel

def row7430 : Integer.Sparse Key := [(key2377, 6), (key2389, -6), (key2471, 6), (key2479, -12), (key2502, 12), (key2518, -6)]

theorem rowCheck7430 : row7430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7430 := by decide +kernel

theorem rowEval7430 (x : Key → ℝ) : Integer.Sparse.eval row7430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7430, Integer.Sparse.eval_collectBalanced, rawRowCheck7430]

def rawRow7431 : Integer.Sparse Key := [(key2471, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2377, 2), (key2471, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2479, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2)]

theorem rawRowCheck7431 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0 = rawRow7431 := by decide +kernel

def row7431 : Integer.Sparse Key := [(key2377, 6), (key2389, -6), (key2471, 6), (key2479, -12), (key2502, 12), (key2518, -6)]

theorem rowCheck7431 : row7431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7431 := by decide +kernel

theorem rowEval7431 (x : Key → ℝ) : Integer.Sparse.eval row7431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7431, Integer.Sparse.eval_collectBalanced, rawRowCheck7431]

def rawRow7432 : Integer.Sparse Key := [(key2502, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2377, 2), (key2471, 2), (key2479, -2), (key2518, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2479, -2)]

theorem rawRowCheck7432 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0 = rawRow7432 := by decide +kernel

def row7432 : Integer.Sparse Key := [(key2377, 6), (key2389, -6), (key2471, 6), (key2479, -12), (key2502, 12), (key2518, -6)]

theorem rowCheck7432 : row7432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7432 := by decide +kernel

theorem rowEval7432 (x : Key → ℝ) : Integer.Sparse.eval row7432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7432, Integer.Sparse.eval_collectBalanced, rawRowCheck7432]

def rawRow7433 : Integer.Sparse Key := [(key2502, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2377, 2), (key2471, 2), (key2377, 2), (key2518, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2389, -2)]

theorem rawRowCheck7433 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0 = rawRow7433 := by decide +kernel

def row7433 : Integer.Sparse Key := [(key2377, 6), (key2389, -6), (key2471, 6), (key2479, -12), (key2502, 12), (key2518, -6)]

theorem rowCheck7433 : row7433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7433 := by decide +kernel

theorem rowEval7433 (x : Key → ℝ) : Integer.Sparse.eval row7433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7433, Integer.Sparse.eval_collectBalanced, rawRowCheck7433]

def rawRow7434 : Integer.Sparse Key := [(key2377, 2), (key2389, 2), (key2389, 2), (key2405, 2), (key2479, 2), (key2479, 2), (key2436, 2), (key2436, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2), (key2377, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2405, -2), (key2471, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2502, -2)]

theorem rawRowCheck7434 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow7434 := by decide +kernel

def row7434 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7434 : row7434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7434 := by decide +kernel

theorem rowEval7434 (x : Key → ℝ) : Integer.Sparse.eval row7434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7434, Integer.Sparse.eval_collectBalanced, rawRowCheck7434]

def rawRow7435 : Integer.Sparse Key := [(key2389, 2), (key2377, 2), (key2389, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2502, 2), (key2518, 2), (key2436, 2), (key2518, 2), (key2436, 2), (key2502, 2), (key2377, -2), (key2389, -2), (key2377, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2436, -2), (key2502, -2)]

theorem rawRowCheck7435 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow7435 := by decide +kernel

def row7435 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7435 : row7435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7435 := by decide +kernel

theorem rowEval7435 (x : Key → ℝ) : Integer.Sparse.eval row7435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7435, Integer.Sparse.eval_collectBalanced, rawRowCheck7435]

def rawRow7436 : Integer.Sparse Key := [(key2389, 2), (key2389, 2), (key2377, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2518, 2), (key2502, 2), (key2518, 2), (key2436, 2), (key2502, 2), (key2436, 2), (key2389, -2), (key2377, -2), (key2377, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2405, -2), (key2502, -2), (key2502, -2), (key2436, -2)]

theorem rawRowCheck7436 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow7436 := by decide +kernel

def row7436 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7436 : row7436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7436 := by decide +kernel

theorem rowEval7436 (x : Key → ℝ) : Integer.Sparse.eval row7436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7436, Integer.Sparse.eval_collectBalanced, rawRowCheck7436]

def rawRow7437 : Integer.Sparse Key := [(key2405, 2), (key2436, 2), (key2436, 2), (key2377, 2), (key2502, 2), (key2502, 2), (key2389, 2), (key2389, 2), (key2479, 2), (key2479, 2), (key2518, 2), (key2518, 2), (key2405, -2), (key2405, -2), (key2436, -2), (key2377, -2), (key2377, -2), (key2471, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2479, -2)]

theorem rawRowCheck7437 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow7437 := by decide +kernel

def row7437 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7437 : row7437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7437 := by decide +kernel

theorem rowEval7437 (x : Key → ℝ) : Integer.Sparse.eval row7437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7437, Integer.Sparse.eval_collectBalanced, rawRowCheck7437]

def rawRow7438 : Integer.Sparse Key := [(key2436, 2), (key2405, 2), (key2436, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2479, 2), (key2518, 2), (key2389, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2405, -2), (key2436, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2479, -2), (key2389, -2), (key2479, -2)]

theorem rawRowCheck7438 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow7438 := by decide +kernel

def row7438 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7438 : row7438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7438 := by decide +kernel

theorem rowEval7438 (x : Key → ℝ) : Integer.Sparse.eval row7438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7438, Integer.Sparse.eval_collectBalanced, rawRowCheck7438]

def rawRow7439 : Integer.Sparse Key := [(key2436, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2389, 2), (key2436, -2), (key2405, -2), (key2405, -2), (key2502, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2377, -2), (key2479, -2), (key2479, -2), (key2389, -2)]

theorem rawRowCheck7439 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow7439 := by decide +kernel

def row7439 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7439 : row7439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7439 := by decide +kernel

theorem rowEval7439 (x : Key → ℝ) : Integer.Sparse.eval row7439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7439, Integer.Sparse.eval_collectBalanced, rawRowCheck7439]

def rawRow7440 : Integer.Sparse Key := [(key2479, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2518, 2), (key2377, 2), (key2389, 2), (key2405, 2), (key2479, 2), (key2436, 2), (key2502, 2), (key2471, -2), (key2479, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2377, -2), (key2405, -2), (key2471, -2)]

theorem rawRowCheck7440 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0 = rawRow7440 := by decide +kernel

def row7440 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7440 : row7440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7440 := by decide +kernel

theorem rowEval7440 (x : Key → ℝ) : Integer.Sparse.eval row7440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7440, Integer.Sparse.eval_collectBalanced, rawRowCheck7440]

def rawRow7441 : Integer.Sparse Key := [(key2479, 2), (key2518, 2), (key2502, 2), (key2389, 2), (key2518, 2), (key2436, 2), (key2389, 2), (key2377, 2), (key2479, 2), (key2405, 2), (key2502, 2), (key2436, 2), (key2479, -2), (key2471, -2), (key2502, -2), (key2389, -2), (key2377, -2), (key2479, -2), (key2405, -2), (key2502, -2), (key2436, -2), (key2377, -2), (key2471, -2), (key2405, -2)]

theorem rawRowCheck7441 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0 = rawRow7441 := by decide +kernel

def row7441 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7441 : row7441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7441 := by decide +kernel

theorem rowEval7441 (x : Key → ℝ) : Integer.Sparse.eval row7441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7441, Integer.Sparse.eval_collectBalanced, rawRowCheck7441]

def rawRow7442 : Integer.Sparse Key := [(key2502, 2), (key2479, 2), (key2518, 2), (key2436, 2), (key2389, 2), (key2518, 2), (key2405, 2), (key2436, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2471, -2), (key2502, -2), (key2479, -2), (key2405, -2), (key2436, -2), (key2377, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2405, -2), (key2377, -2), (key2471, -2)]

theorem rawRowCheck7442 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0 = rawRow7442 := by decide +kernel

def row7442 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7442 : row7442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7442 := by decide +kernel

theorem rowEval7442 (x : Key → ℝ) : Integer.Sparse.eval row7442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7442, Integer.Sparse.eval_collectBalanced, rawRowCheck7442]

def rawRow7443 : Integer.Sparse Key := [(key2502, 2), (key2518, 2), (key2479, 2), (key2436, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2479, 2), (key2389, 2), (key2502, -2), (key2471, -2), (key2479, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2377, -2), (key2479, -2), (key2389, -2), (key2405, -2), (key2471, -2), (key2377, -2)]

theorem rawRowCheck7443 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0 = rawRow7443 := by decide +kernel

def row7443 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7443 : row7443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7443 := by decide +kernel

theorem rowEval7443 (x : Key → ℝ) : Integer.Sparse.eval row7443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7443, Integer.Sparse.eval_collectBalanced, rawRowCheck7443]

def rawRow7444 : Integer.Sparse Key := [(key2518, 2), (key2479, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2479, 2), (key2502, 2), (key2389, 2), (key2436, 2), (key2377, 2), (key2405, 2), (key2479, -2), (key2502, -2), (key2471, -2), (key2479, -2), (key2502, -2), (key2389, -2), (key2436, -2), (key2377, -2), (key2405, -2), (key2471, -2), (key2377, -2), (key2405, -2)]

theorem rawRowCheck7444 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0 = rawRow7444 := by decide +kernel

def row7444 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7444 : row7444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7444 := by decide +kernel

theorem rowEval7444 (x : Key → ℝ) : Integer.Sparse.eval row7444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7444, Integer.Sparse.eval_collectBalanced, rawRowCheck7444]

def rawRow7445 : Integer.Sparse Key := [(key2518, 2), (key2502, 2), (key2479, 2), (key2518, 2), (key2436, 2), (key2389, 2), (key2502, 2), (key2479, 2), (key2436, 2), (key2389, 2), (key2405, 2), (key2377, 2), (key2502, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2479, -2), (key2436, -2), (key2389, -2), (key2405, -2), (key2377, -2), (key2471, -2), (key2405, -2), (key2377, -2)]

theorem rawRowCheck7445 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0 = rawRow7445 := by decide +kernel

def row7445 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

theorem rowCheck7445 : row7445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7445 := by decide +kernel

theorem rowEval7445 (x : Key → ℝ) : Integer.Sparse.eval row7445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7445, Integer.Sparse.eval_collectBalanced, rawRowCheck7445]

def rawRow7446 : Integer.Sparse Key := [(key1024, -24), (key989, 6), (key1102, 6), (key1102, 6), (key1102, 6)]

theorem rawRowCheck7446 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7446 := by decide +kernel

def row7446 : Integer.Sparse Key := [(key989, 6), (key1024, -24), (key1102, 18)]

theorem rowCheck7446 : row7446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7446 := by decide +kernel

theorem rowEval7446 (x : Key → ℝ) : Integer.Sparse.eval row7446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7446, Integer.Sparse.eval_collectBalanced, rawRowCheck7446]

def rawRow7447 : Integer.Sparse Key := [(key1024, -24), (key1102, 6), (key989, 6), (key1102, 6), (key1102, 6)]

theorem rawRowCheck7447 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1 = rawRow7447 := by decide +kernel

def row7447 : Integer.Sparse Key := [(key989, 6), (key1024, -24), (key1102, 18)]

theorem rowCheck7447 : row7447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7447 := by decide +kernel

theorem rowEval7447 (x : Key → ℝ) : Integer.Sparse.eval row7447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7447, Integer.Sparse.eval_collectBalanced, rawRowCheck7447]

def rawRow7448 : Integer.Sparse Key := [(key1024, -24), (key1102, 6), (key1102, 6), (key989, 6), (key1102, 6)]

theorem rawRowCheck7448 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1 = rawRow7448 := by decide +kernel

def row7448 : Integer.Sparse Key := [(key989, 6), (key1024, -24), (key1102, 18)]

theorem rowCheck7448 : row7448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7448 := by decide +kernel

theorem rowEval7448 (x : Key → ℝ) : Integer.Sparse.eval row7448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7448, Integer.Sparse.eval_collectBalanced, rawRowCheck7448]

def rawRow7449 : Integer.Sparse Key := [(key1024, -24), (key1102, 6), (key1102, 6), (key1102, 6), (key989, 6)]

theorem rawRowCheck7449 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1 = rawRow7449 := by decide +kernel

def row7449 : Integer.Sparse Key := [(key989, 6), (key1024, -24), (key1102, 18)]

theorem rowCheck7449 : row7449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7449 := by decide +kernel

theorem rowEval7449 (x : Key → ℝ) : Integer.Sparse.eval row7449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7449, Integer.Sparse.eval_collectBalanced, rawRowCheck7449]

def rawRow7450 : Integer.Sparse Key := [(key1102, -24), (key989, 6), (key1024, 6), (key1102, 6), (key1102, 6)]

theorem rawRowCheck7450 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow7450 := by decide +kernel

def row7450 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7450 : row7450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7450 := by decide +kernel

theorem rowEval7450 (x : Key → ℝ) : Integer.Sparse.eval row7450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7450, Integer.Sparse.eval_collectBalanced, rawRowCheck7450]

def rawRow7451 : Integer.Sparse Key := [(key1102, -24), (key989, 6), (key1102, 6), (key1024, 6), (key1102, 6)]

theorem rawRowCheck7451 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow7451 := by decide +kernel

def row7451 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7451 : row7451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7451 := by decide +kernel

theorem rowEval7451 (x : Key → ℝ) : Integer.Sparse.eval row7451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7451, Integer.Sparse.eval_collectBalanced, rawRowCheck7451]

def rawRow7452 : Integer.Sparse Key := [(key1102, -24), (key989, 6), (key1102, 6), (key1102, 6), (key1024, 6)]

theorem rawRowCheck7452 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow7452 := by decide +kernel

def row7452 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7452 : row7452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7452 := by decide +kernel

theorem rowEval7452 (x : Key → ℝ) : Integer.Sparse.eval row7452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7452, Integer.Sparse.eval_collectBalanced, rawRowCheck7452]

def rawRow7453 : Integer.Sparse Key := [(key1102, -24), (key1024, 6), (key989, 6), (key1102, 6), (key1102, 6)]

theorem rawRowCheck7453 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow7453 := by decide +kernel

def row7453 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7453 : row7453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7453 := by decide +kernel

theorem rowEval7453 (x : Key → ℝ) : Integer.Sparse.eval row7453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7453, Integer.Sparse.eval_collectBalanced, rawRowCheck7453]

def rawRow7454 : Integer.Sparse Key := [(key1102, -24), (key1024, 6), (key1102, 6), (key989, 6), (key1102, 6)]

theorem rawRowCheck7454 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow7454 := by decide +kernel

def row7454 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7454 : row7454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7454 := by decide +kernel

theorem rowEval7454 (x : Key → ℝ) : Integer.Sparse.eval row7454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7454, Integer.Sparse.eval_collectBalanced, rawRowCheck7454]

def rawRow7455 : Integer.Sparse Key := [(key1102, -24), (key1024, 6), (key1102, 6), (key1102, 6), (key989, 6)]

theorem rawRowCheck7455 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow7455 := by decide +kernel

def row7455 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7455 : row7455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7455 := by decide +kernel

theorem rowEval7455 (x : Key → ℝ) : Integer.Sparse.eval row7455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7455, Integer.Sparse.eval_collectBalanced, rawRowCheck7455]

def rawRow7456 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key989, 6), (key1024, 6), (key1102, 6)]

theorem rawRowCheck7456 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form1 = rawRow7456 := by decide +kernel

def row7456 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7456 : row7456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7456 := by decide +kernel

theorem rowEval7456 (x : Key → ℝ) : Integer.Sparse.eval row7456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7456, Integer.Sparse.eval_collectBalanced, rawRowCheck7456]

def rawRow7457 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key989, 6), (key1102, 6), (key1024, 6)]

theorem rawRowCheck7457 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form1 = rawRow7457 := by decide +kernel

def row7457 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7457 : row7457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7457 := by decide +kernel

theorem rowEval7457 (x : Key → ℝ) : Integer.Sparse.eval row7457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7457, Integer.Sparse.eval_collectBalanced, rawRowCheck7457]

def rawRow7458 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1024, 6), (key989, 6), (key1102, 6)]

theorem rawRowCheck7458 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form1 = rawRow7458 := by decide +kernel

def row7458 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7458 : row7458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7458 := by decide +kernel

theorem rowEval7458 (x : Key → ℝ) : Integer.Sparse.eval row7458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7458, Integer.Sparse.eval_collectBalanced, rawRowCheck7458]

def rawRow7459 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1024, 6), (key1102, 6), (key989, 6)]

theorem rawRowCheck7459 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form1 = rawRow7459 := by decide +kernel

def row7459 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7459 : row7459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7459 := by decide +kernel

theorem rowEval7459 (x : Key → ℝ) : Integer.Sparse.eval row7459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7459, Integer.Sparse.eval_collectBalanced, rawRowCheck7459]

def rawRow7460 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1102, 6), (key989, 6), (key1024, 6)]

theorem rawRowCheck7460 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form1 = rawRow7460 := by decide +kernel

def row7460 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7460 : row7460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7460 := by decide +kernel

theorem rowEval7460 (x : Key → ℝ) : Integer.Sparse.eval row7460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7460, Integer.Sparse.eval_collectBalanced, rawRowCheck7460]

def rawRow7461 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1102, 6), (key1024, 6), (key989, 6)]

theorem rawRowCheck7461 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form1 = rawRow7461 := by decide +kernel

def row7461 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

theorem rowCheck7461 : row7461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7461 := by decide +kernel

theorem rowEval7461 (x : Key → ℝ) : Integer.Sparse.eval row7461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7461, Integer.Sparse.eval_collectBalanced, rawRowCheck7461]

def rawRow7462 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1030, -6), (key1067, -6), (key995, 2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1146, 2)]

theorem rawRowCheck7462 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7462 := by decide +kernel

def row7462 : Integer.Sparse Key := [(key995, 6), (key1030, -18), (key1067, -6), (key1108, 12), (key1146, 6)]

theorem rowCheck7462 : row7462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7462 := by decide +kernel

theorem rowEval7462 (x : Key → ℝ) : Integer.Sparse.eval row7462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7462, Integer.Sparse.eval_collectBalanced, rawRowCheck7462]

def rawRow7463 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1067, -6), (key1030, -6), (key1108, 2), (key1108, 2), (key1146, 2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1108, 2)]

theorem rawRowCheck7463 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2 = rawRow7463 := by decide +kernel

def row7463 : Integer.Sparse Key := [(key995, 6), (key1030, -18), (key1067, -6), (key1108, 12), (key1146, 6)]

theorem rowCheck7463 : row7463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7463 := by decide +kernel

theorem rowEval7463 (x : Key → ℝ) : Integer.Sparse.eval row7463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7463, Integer.Sparse.eval_collectBalanced, rawRowCheck7463]

def rawRow7464 : Integer.Sparse Key := [(key1030, -6), (key1067, -6), (key1030, -6), (key1030, -6), (key1108, 2), (key1146, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1108, 2), (key995, 2), (key1108, 2)]

theorem rawRowCheck7464 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2 = rawRow7464 := by decide +kernel

def row7464 : Integer.Sparse Key := [(key995, 6), (key1030, -18), (key1067, -6), (key1108, 12), (key1146, 6)]

theorem rowCheck7464 : row7464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7464 := by decide +kernel

theorem rowEval7464 (x : Key → ℝ) : Integer.Sparse.eval row7464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7464, Integer.Sparse.eval_collectBalanced, rawRowCheck7464]

def rawRow7465 : Integer.Sparse Key := [(key1067, -6), (key1030, -6), (key1030, -6), (key1030, -6), (key1146, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1108, 2), (key1108, 2), (key995, 2)]

theorem rawRowCheck7465 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2 = rawRow7465 := by decide +kernel

def row7465 : Integer.Sparse Key := [(key995, 6), (key1030, -18), (key1067, -6), (key1108, 12), (key1146, 6)]

theorem rowCheck7465 : row7465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7465 := by decide +kernel

theorem rowEval7465 (x : Key → ℝ) : Integer.Sparse.eval row7465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7465, Integer.Sparse.eval_collectBalanced, rawRowCheck7465]

def rawRow7466 : Integer.Sparse Key := [(key1108, -6), (key1108, -6), (key1119, -6), (key1146, -6), (key995, 2), (key995, 2), (key1011, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1067, 2), (key1146, 2), (key1146, 2)]

theorem rawRowCheck7466 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow7466 := by decide +kernel

def row7466 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7466 : row7466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7466 := by decide +kernel

theorem rowEval7466 (x : Key → ℝ) : Integer.Sparse.eval row7466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7466, Integer.Sparse.eval_collectBalanced, rawRowCheck7466]

def rawRow7467 : Integer.Sparse Key := [(key1108, -6), (key1119, -6), (key1108, -6), (key1146, -6), (key995, 2), (key1011, 2), (key995, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1146, 2), (key1067, 2), (key1146, 2)]

theorem rawRowCheck7467 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow7467 := by decide +kernel

def row7467 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7467 : row7467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7467 := by decide +kernel

theorem rowEval7467 (x : Key → ℝ) : Integer.Sparse.eval row7467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7467, Integer.Sparse.eval_collectBalanced, rawRowCheck7467]

def rawRow7468 : Integer.Sparse Key := [(key1119, -6), (key1108, -6), (key1108, -6), (key1146, -6), (key1011, 2), (key995, 2), (key995, 2), (key1119, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1030, 2), (key1146, 2), (key1146, 2), (key1067, 2)]

theorem rawRowCheck7468 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow7468 := by decide +kernel

def row7468 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7468 : row7468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7468 := by decide +kernel

theorem rowEval7468 (x : Key → ℝ) : Integer.Sparse.eval row7468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7468, Integer.Sparse.eval_collectBalanced, rawRowCheck7468]

def rawRow7469 : Integer.Sparse Key := [(key1108, -6), (key1108, -6), (key1146, -6), (key1119, -6), (key1030, 2), (key1030, 2), (key1067, 2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1011, 2), (key1119, 2), (key1119, 2)]

theorem rawRowCheck7469 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow7469 := by decide +kernel

def row7469 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7469 : row7469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7469 := by decide +kernel

theorem rowEval7469 (x : Key → ℝ) : Integer.Sparse.eval row7469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7469, Integer.Sparse.eval_collectBalanced, rawRowCheck7469]

def rawRow7470 : Integer.Sparse Key := [(key1108, -6), (key1146, -6), (key1108, -6), (key1119, -6), (key1030, 2), (key1067, 2), (key1030, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1119, 2), (key1011, 2), (key1119, 2)]

theorem rawRowCheck7470 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow7470 := by decide +kernel

def row7470 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7470 : row7470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7470 := by decide +kernel

theorem rowEval7470 (x : Key → ℝ) : Integer.Sparse.eval row7470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7470, Integer.Sparse.eval_collectBalanced, rawRowCheck7470]

def rawRow7471 : Integer.Sparse Key := [(key1146, -6), (key1108, -6), (key1108, -6), (key1119, -6), (key1067, 2), (key1030, 2), (key1030, 2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1119, 2), (key1119, 2), (key1011, 2)]

theorem rawRowCheck7471 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow7471 := by decide +kernel

def row7471 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7471 : row7471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7471 := by decide +kernel

theorem rowEval7471 (x : Key → ℝ) : Integer.Sparse.eval row7471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7471, Integer.Sparse.eval_collectBalanced, rawRowCheck7471]

def rawRow7472 : Integer.Sparse Key := [(key1108, -6), (key1119, -6), (key1146, -6), (key1108, -6), (key1108, 2), (key1119, 2), (key1146, 2), (key995, 2), (key1011, 2), (key1030, 2), (key1119, 2), (key1067, 2), (key1146, 2), (key995, 2), (key1030, 2), (key1108, 2)]

theorem rawRowCheck7472 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form2 = rawRow7472 := by decide +kernel

def row7472 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7472 : row7472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7472 := by decide +kernel

theorem rowEval7472 (x : Key → ℝ) : Integer.Sparse.eval row7472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7472, Integer.Sparse.eval_collectBalanced, rawRowCheck7472]

def rawRow7473 : Integer.Sparse Key := [(key1119, -6), (key1108, -6), (key1146, -6), (key1108, -6), (key1119, 2), (key1108, 2), (key1146, 2), (key1011, 2), (key995, 2), (key1119, 2), (key1030, 2), (key1146, 2), (key1067, 2), (key995, 2), (key1108, 2), (key1030, 2)]

theorem rawRowCheck7473 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form2 = rawRow7473 := by decide +kernel

def row7473 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7473 : row7473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7473 := by decide +kernel

theorem rowEval7473 (x : Key → ℝ) : Integer.Sparse.eval row7473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7473, Integer.Sparse.eval_collectBalanced, rawRowCheck7473]

def rawRow7474 : Integer.Sparse Key := [(key1108, -6), (key1146, -6), (key1119, -6), (key1108, -6), (key1108, 2), (key1146, 2), (key1119, 2), (key1030, 2), (key1067, 2), (key995, 2), (key1146, 2), (key1011, 2), (key1119, 2), (key1030, 2), (key995, 2), (key1108, 2)]

theorem rawRowCheck7474 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form2 = rawRow7474 := by decide +kernel

def row7474 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7474 : row7474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7474 := by decide +kernel

theorem rowEval7474 (x : Key → ℝ) : Integer.Sparse.eval row7474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7474, Integer.Sparse.eval_collectBalanced, rawRowCheck7474]

def rawRow7475 : Integer.Sparse Key := [(key1146, -6), (key1108, -6), (key1119, -6), (key1108, -6), (key1146, 2), (key1108, 2), (key1119, 2), (key1067, 2), (key1030, 2), (key1146, 2), (key995, 2), (key1119, 2), (key1011, 2), (key1030, 2), (key1108, 2), (key995, 2)]

theorem rawRowCheck7475 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form2 = rawRow7475 := by decide +kernel

def row7475 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7475 : row7475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7475 := by decide +kernel

theorem rowEval7475 (x : Key → ℝ) : Integer.Sparse.eval row7475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7475, Integer.Sparse.eval_collectBalanced, rawRowCheck7475]

def rawRow7476 : Integer.Sparse Key := [(key1119, -6), (key1146, -6), (key1108, -6), (key1108, -6), (key1119, 2), (key1146, 2), (key1108, 2), (key1119, 2), (key1146, 2), (key1011, 2), (key1067, 2), (key995, 2), (key1030, 2), (key1108, 2), (key995, 2), (key1030, 2)]

theorem rawRowCheck7476 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form2 = rawRow7476 := by decide +kernel

def row7476 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7476 : row7476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7476 := by decide +kernel

theorem rowEval7476 (x : Key → ℝ) : Integer.Sparse.eval row7476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7476, Integer.Sparse.eval_collectBalanced, rawRowCheck7476]

def rawRow7477 : Integer.Sparse Key := [(key1146, -6), (key1119, -6), (key1108, -6), (key1108, -6), (key1146, 2), (key1119, 2), (key1108, 2), (key1146, 2), (key1119, 2), (key1067, 2), (key1011, 2), (key1030, 2), (key995, 2), (key1108, 2), (key1030, 2), (key995, 2)]

theorem rawRowCheck7477 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form2 = rawRow7477 := by decide +kernel

def row7477 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

theorem rowCheck7477 : row7477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7477 := by decide +kernel

theorem rowEval7477 (x : Key → ℝ) : Integer.Sparse.eval row7477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7477, Integer.Sparse.eval_collectBalanced, rawRowCheck7477]

def rawRow7478 : Integer.Sparse Key := [(key2606, -6), (key2799, -6), (key2799, -6), (key2799, -6), (key2622, 2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck7478 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7478 := by decide +kernel

def row7478 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2696, 6), (key2799, -18), (key2849, 12)]

theorem rowCheck7478 : row7478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7478 := by decide +kernel

theorem rowEval7478 (x : Key → ℝ) : Integer.Sparse.eval row7478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7478, Integer.Sparse.eval_collectBalanced, rawRowCheck7478]

def rawRow7479 : Integer.Sparse Key := [(key2799, -6), (key2606, -6), (key2799, -6), (key2799, -6), (key2696, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck7479 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3 = rawRow7479 := by decide +kernel

def row7479 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2696, 6), (key2799, -18), (key2849, 12)]

theorem rowCheck7479 : row7479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7479 := by decide +kernel

theorem rowEval7479 (x : Key → ℝ) : Integer.Sparse.eval row7479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7479, Integer.Sparse.eval_collectBalanced, rawRowCheck7479]

def rawRow7480 : Integer.Sparse Key := [(key2799, -6), (key2799, -6), (key2606, -6), (key2799, -6), (key2849, 2), (key2696, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

theorem rawRowCheck7480 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3 = rawRow7480 := by decide +kernel

def row7480 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2696, 6), (key2799, -18), (key2849, 12)]

theorem rowCheck7480 : row7480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7480 := by decide +kernel

theorem rowEval7480 (x : Key → ℝ) : Integer.Sparse.eval row7480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7480, Integer.Sparse.eval_collectBalanced, rawRowCheck7480]

def rawRow7481 : Integer.Sparse Key := [(key2799, -6), (key2799, -6), (key2799, -6), (key2606, -6), (key2849, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

theorem rawRowCheck7481 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3 = rawRow7481 := by decide +kernel

def row7481 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2696, 6), (key2799, -18), (key2849, 12)]

theorem rowCheck7481 : row7481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7481 := by decide +kernel

theorem rowEval7481 (x : Key → ℝ) : Integer.Sparse.eval row7481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7481, Integer.Sparse.eval_collectBalanced, rawRowCheck7481]

def rawRow7482 : Integer.Sparse Key := [(key2622, -6), (key2696, -6), (key2849, -6), (key2849, -6), (key2606, 2), (key2622, 2), (key2622, 2), (key2661, 2), (key2696, 2), (key2696, 2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck7482 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow7482 := by decide +kernel

def row7482 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

theorem rowCheck7482 : row7482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7482 := by decide +kernel

theorem rowEval7482 (x : Key → ℝ) : Integer.Sparse.eval row7482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7482, Integer.Sparse.eval_collectBalanced, rawRowCheck7482]

def rawRow7483 : Integer.Sparse Key := [(key2622, -6), (key2849, -6), (key2696, -6), (key2849, -6), (key2622, 2), (key2606, 2), (key2622, 2), (key2696, 2), (key2661, 2), (key2696, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2776, 2), (key2799, 2)]

theorem rawRowCheck7483 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow7483 := by decide +kernel

def row7483 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

theorem rowCheck7483 : row7483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7483 := by decide +kernel

theorem rowEval7483 (x : Key → ℝ) : Integer.Sparse.eval row7483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7483, Integer.Sparse.eval_collectBalanced, rawRowCheck7483]

def rawRow7484 : Integer.Sparse Key := [(key2622, -6), (key2849, -6), (key2849, -6), (key2696, -6), (key2622, 2), (key2622, 2), (key2606, 2), (key2696, 2), (key2696, 2), (key2661, 2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2799, 2), (key2776, 2)]

theorem rawRowCheck7484 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow7484 := by decide +kernel

def row7484 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

theorem rowCheck7484 : row7484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7484 := by decide +kernel

theorem rowEval7484 (x : Key → ℝ) : Integer.Sparse.eval row7484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7484, Integer.Sparse.eval_collectBalanced, rawRowCheck7484]

def rawRow7485 : Integer.Sparse Key := [(key2696, -6), (key2622, -6), (key2849, -6), (key2849, -6), (key2661, 2), (key2696, 2), (key2696, 2), (key2606, 2), (key2799, 2), (key2799, 2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

theorem rawRowCheck7485 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow7485 := by decide +kernel

def row7485 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, 2), (key2799, 4), (key2849, -8)]

theorem rowCheck7485 : row7485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7485 := by decide +kernel

theorem rowEval7485 (x : Key → ℝ) : Integer.Sparse.eval row7485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7485, Integer.Sparse.eval_collectBalanced, rawRowCheck7485]

def rawRow7486 : Integer.Sparse Key := [(key2696, -6), (key2849, -6), (key2622, -6), (key2849, -6), (key2696, 2), (key2661, 2), (key2696, 2), (key2799, 2), (key2606, 2), (key2799, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

theorem rawRowCheck7486 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow7486 := by decide +kernel

def row7486 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, 2), (key2799, 4), (key2849, -8)]

theorem rowCheck7486 : row7486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7486 := by decide +kernel

theorem rowEval7486 (x : Key → ℝ) : Integer.Sparse.eval row7486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7486, Integer.Sparse.eval_collectBalanced, rawRowCheck7486]

def rawRow7487 : Integer.Sparse Key := [(key2696, -6), (key2849, -6), (key2849, -6), (key2622, -6), (key2696, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2799, 2), (key2606, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

theorem rawRowCheck7487 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow7487 := by decide +kernel

def row7487 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, 2), (key2799, 4), (key2849, -8)]

theorem rowCheck7487 : row7487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7487 := by decide +kernel

theorem rowEval7487 (x : Key → ℝ) : Integer.Sparse.eval row7487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7487, Integer.Sparse.eval_collectBalanced, rawRowCheck7487]

def rawRow7488 : Integer.Sparse Key := [(key2849, -6), (key2622, -6), (key2696, -6), (key2849, -6), (key2776, 2), (key2799, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2849, 2), (key2606, 2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, 2), (key2799, 2)]

theorem rawRowCheck7488 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form3 = rawRow7488 := by decide +kernel

def row7488 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

theorem rowCheck7488 : row7488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7488 := by decide +kernel

theorem rowEval7488 (x : Key → ℝ) : Integer.Sparse.eval row7488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7488, Integer.Sparse.eval_collectBalanced, rawRowCheck7488]

def rawRow7489 : Integer.Sparse Key := [(key2849, -6), (key2622, -6), (key2849, -6), (key2696, -6), (key2776, 2), (key2849, 2), (key2799, 2), (key2622, 2), (key2849, 2), (key2696, 2), (key2622, 2), (key2606, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2776, 2)]

theorem rawRowCheck7489 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form3 = rawRow7489 := by decide +kernel

def row7489 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

theorem rowCheck7489 : row7489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7489 := by decide +kernel

theorem rowEval7489 (x : Key → ℝ) : Integer.Sparse.eval row7489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7489, Integer.Sparse.eval_collectBalanced, rawRowCheck7489]

def rawRow7490 : Integer.Sparse Key := [(key2849, -6), (key2696, -6), (key2622, -6), (key2849, -6), (key2799, 2), (key2776, 2), (key2849, 2), (key2696, 2), (key2622, 2), (key2849, 2), (key2661, 2), (key2696, 2), (key2606, 2), (key2799, 2), (key2622, 2), (key2696, 2)]

theorem rawRowCheck7490 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form3 = rawRow7490 := by decide +kernel

def row7490 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, 2), (key2799, 4), (key2849, -8)]

theorem rowCheck7490 : row7490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7490 := by decide +kernel

theorem rowEval7490 (x : Key → ℝ) : Integer.Sparse.eval row7490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7490, Integer.Sparse.eval_collectBalanced, rawRowCheck7490]

def rawRow7491 : Integer.Sparse Key := [(key2849, -6), (key2696, -6), (key2849, -6), (key2622, -6), (key2799, 2), (key2849, 2), (key2776, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2606, 2), (key2696, 2), (key2622, 2)]

theorem rawRowCheck7491 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form3 = rawRow7491 := by decide +kernel

def row7491 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, 2), (key2799, 4), (key2849, -8)]

theorem rowCheck7491 : row7491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7491 := by decide +kernel

theorem rowEval7491 (x : Key → ℝ) : Integer.Sparse.eval row7491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7491, Integer.Sparse.eval_collectBalanced, rawRowCheck7491]

def rawRow7492 : Integer.Sparse Key := [(key2849, -6), (key2849, -6), (key2622, -6), (key2696, -6), (key2849, 2), (key2776, 2), (key2799, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2776, 2), (key2799, 2), (key2622, 2), (key2696, 2), (key2606, 2), (key2661, 2)]

theorem rawRowCheck7492 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form3 = rawRow7492 := by decide +kernel

def row7492 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

theorem rowCheck7492 : row7492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7492 := by decide +kernel

theorem rowEval7492 (x : Key → ℝ) : Integer.Sparse.eval row7492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7492, Integer.Sparse.eval_collectBalanced, rawRowCheck7492]

def rawRow7493 : Integer.Sparse Key := [(key2849, -6), (key2849, -6), (key2696, -6), (key2622, -6), (key2849, 2), (key2799, 2), (key2776, 2), (key2849, 2), (key2696, 2), (key2622, 2), (key2799, 2), (key2776, 2), (key2696, 2), (key2622, 2), (key2661, 2), (key2606, 2)]

theorem rawRowCheck7493 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form3 = rawRow7493 := by decide +kernel

def row7493 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

theorem rowCheck7493 : row7493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7493 := by decide +kernel

theorem rowEval7493 (x : Key → ℝ) : Integer.Sparse.eval row7493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7493, Integer.Sparse.eval_collectBalanced, rawRowCheck7493]

def rawRow7494 : Integer.Sparse Key := [(key2452, 2), (key2452, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2458, 2), (key2452, 2), (key2519, 2), (key2458, 2), (key2519, 2), (key2528, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2560, -2)]

theorem rawRowCheck7494 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7494 := by decide +kernel

def row7494 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

theorem rowCheck7494 : row7494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7494 := by decide +kernel

theorem rowEval7494 (x : Key → ℝ) : Integer.Sparse.eval row7494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7494, Integer.Sparse.eval_collectBalanced, rawRowCheck7494]

def rawRow7495 : Integer.Sparse Key := [(key2452, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2458, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2519, 2), (key2458, 2), (key2530, -2), (key2528, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2560, -2), (key2530, -2)]

theorem rawRowCheck7495 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7495 := by decide +kernel

def row7495 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

theorem rowCheck7495 : row7495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7495 := by decide +kernel

theorem rowEval7495 (x : Key → ℝ) : Integer.Sparse.eval row7495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7495, Integer.Sparse.eval_collectBalanced, rawRowCheck7495]

def rawRow7496 : Integer.Sparse Key := [(key2458, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2519, 2), (key2458, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2530, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2530, -2)]

theorem rawRowCheck7496 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7496 := by decide +kernel

def row7496 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

theorem rowCheck7496 : row7496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7496 := by decide +kernel

theorem rowEval7496 (x : Key → ℝ) : Integer.Sparse.eval row7496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7496, Integer.Sparse.eval_collectBalanced, rawRowCheck7496]

def rawRow7497 : Integer.Sparse Key := [(key2519, 2), (key2519, 2), (key2519, 2), (key2458, 2), (key2458, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2560, -2), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2528, -2)]

theorem rawRowCheck7497 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7497 := by decide +kernel

def row7497 : Integer.Sparse Key := [(key2452, 12), (key2458, 6), (key2519, 6), (key2528, -6), (key2530, -12), (key2560, -6)]

theorem rowCheck7497 : row7497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7497 := by decide +kernel

theorem rowEval7497 (x : Key → ℝ) : Integer.Sparse.eval row7497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7497, Integer.Sparse.eval_collectBalanced, rawRowCheck7497]

def rawRow7498 : Integer.Sparse Key := [(key2357, 2), (key2357, 2), (key2363, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2528, 2), (key2530, 2), (key2528, 2), (key2560, 2), (key2530, 2), (key2560, 2), (key2357, -2), (key2363, -2), (key2363, -2), (key2452, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2519, -2), (key2530, -2), (key2530, -2), (key2560, -2)]

theorem rawRowCheck7498 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7498 := by decide +kernel

def row7498 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2458, -4), (key2519, -2), (key2528, 4), (key2560, 2)]

theorem rowCheck7498 : row7498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7498 := by decide +kernel

theorem rowEval7498 (x : Key → ℝ) : Integer.Sparse.eval row7498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7498, Integer.Sparse.eval_collectBalanced, rawRowCheck7498]

def rawRow7499 : Integer.Sparse Key := [(key2361, 2), (key2363, 2), (key2357, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2530, 2), (key2528, 2), (key2560, 2), (key2528, 2), (key2560, 2), (key2530, 2), (key2363, -2), (key2357, -2), (key2363, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2530, -2), (key2560, -2), (key2530, -2)]

theorem rawRowCheck7499 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7499 := by decide +kernel

def row7499 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2458, -4), (key2519, -2), (key2528, 4), (key2560, 2)]

theorem rowCheck7499 : row7499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7499 := by decide +kernel

theorem rowEval7499 (x : Key → ℝ) : Integer.Sparse.eval row7499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7499, Integer.Sparse.eval_collectBalanced, rawRowCheck7499]

def rawRow7500 : Integer.Sparse Key := [(key2366, 2), (key2361, 2), (key2361, 2), (key2519, 2), (key2452, 2), (key2452, 2), (key2560, 2), (key2560, 2), (key2530, 2), (key2530, 2), (key2528, 2), (key2528, 2), (key2363, -2), (key2363, -2), (key2357, -2), (key2519, -2), (key2519, -2), (key2458, -2), (key2458, -2), (key2452, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2530, -2)]

theorem rawRowCheck7500 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7500 := by decide +kernel

def row7500 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2458, -4), (key2519, -2), (key2528, 4), (key2560, 2)]

theorem rowCheck7500 : row7500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7500 := by decide +kernel

theorem rowEval7500 (x : Key → ℝ) : Integer.Sparse.eval row7500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7500, Integer.Sparse.eval_collectBalanced, rawRowCheck7500]

def rawRow7501 : Integer.Sparse Key := [(key2456, 2), (key2517, 2), (key2523, 2), (key2357, 2), (key2528, 2), (key2560, 2), (key2357, 2), (key2363, 2), (key2452, 2), (key2519, 2), (key2530, 2), (key2560, 2), (key2452, -2), (key2458, -2), (key2530, -2), (key2357, -2), (key2363, -2), (key2452, -2), (key2519, -2), (key2530, -2), (key2560, -2), (key2363, -2), (key2458, -2), (key2519, -2)]

theorem rawRowCheck7501 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0 = rawRow7501 := by decide +kernel

def row7501 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 2), (key2519, -2), (key2523, 2), (key2528, 2), (key2530, -2), (key2560, 2)]

theorem rowCheck7501 : row7501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7501 := by decide +kernel

theorem rowEval7501 (x : Key → ℝ) : Integer.Sparse.eval row7501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7501, Integer.Sparse.eval_collectBalanced, rawRowCheck7501]

def rawRow7502 : Integer.Sparse Key := [(key2456, 2), (key2523, 2), (key2517, 2), (key2361, 2), (key2560, 2), (key2528, 2), (key2363, 2), (key2357, 2), (key2519, 2), (key2452, 2), (key2560, 2), (key2530, 2), (key2458, -2), (key2452, -2), (key2530, -2), (key2363, -2), (key2357, -2), (key2519, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2363, -2), (key2519, -2), (key2458, -2)]

theorem rawRowCheck7502 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0 = rawRow7502 := by decide +kernel

def row7502 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 2), (key2519, -2), (key2523, 2), (key2528, 2), (key2530, -2), (key2560, 2)]

theorem rowCheck7502 : row7502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7502 := by decide +kernel

theorem rowEval7502 (x : Key → ℝ) : Integer.Sparse.eval row7502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7502, Integer.Sparse.eval_collectBalanced, rawRowCheck7502]

def rawRow7503 : Integer.Sparse Key := [(key2517, 2), (key2456, 2), (key2523, 2), (key2517, 2), (key2357, 2), (key2560, 2), (key2452, 2), (key2530, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2452, -2), (key2530, -2), (key2458, -2), (key2452, -2), (key2530, -2), (key2357, -2), (key2560, -2), (key2363, -2), (key2519, -2), (key2458, -2), (key2363, -2), (key2519, -2)]

theorem rawRowCheck7503 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0 = rawRow7503 := by decide +kernel

def row7503 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2560, 2)]

theorem rowCheck7503 : row7503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7503 := by decide +kernel

theorem rowEval7503 (x : Key → ℝ) : Integer.Sparse.eval row7503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7503, Integer.Sparse.eval_collectBalanced, rawRowCheck7503]

def rawRow7504 : Integer.Sparse Key := [(key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2519, 2), (key2363, 2), (key2530, -2), (key2452, -2), (key2458, -2), (key2530, -2), (key2452, -2), (key2560, -2), (key2357, -2), (key2519, -2), (key2363, -2), (key2458, -2), (key2519, -2), (key2363, -2)]

theorem rawRowCheck7504 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0 = rawRow7504 := by decide +kernel

def row7504 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2560, 2)]

theorem rowCheck7504 : row7504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7504 := by decide +kernel

theorem rowEval7504 (x : Key → ℝ) : Integer.Sparse.eval row7504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7504, Integer.Sparse.eval_collectBalanced, rawRowCheck7504]

def rawRow7505 : Integer.Sparse Key := [(key2523, 2), (key2456, 2), (key2517, 2), (key2579, 2), (key2361, 2), (key2517, 2), (key2519, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2357, 2), (key2452, 2), (key2458, -2), (key2530, -2), (key2452, -2), (key2519, -2), (key2560, -2), (key2363, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2519, -2), (key2363, -2), (key2458, -2)]

theorem rawRowCheck7505 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0 = rawRow7505 := by decide +kernel

def row7505 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2579, 2)]

theorem rowCheck7505 : row7505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7505 := by decide +kernel

theorem rowEval7505 (x : Key → ℝ) : Integer.Sparse.eval row7505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7505, Integer.Sparse.eval_collectBalanced, rawRowCheck7505]

def rawRow7506 : Integer.Sparse Key := [(key2523, 2), (key2517, 2), (key2456, 2), (key2579, 2), (key2517, 2), (key2361, 2), (key2560, 2), (key2519, 2), (key2530, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2530, -2), (key2458, -2), (key2452, -2), (key2560, -2), (key2519, -2), (key2530, -2), (key2363, -2), (key2452, -2), (key2357, -2), (key2519, -2), (key2458, -2), (key2363, -2)]

theorem rawRowCheck7506 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0 = rawRow7506 := by decide +kernel

def row7506 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2579, 2)]

theorem rowCheck7506 : row7506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7506 := by decide +kernel

theorem rowEval7506 (x : Key → ℝ) : Integer.Sparse.eval row7506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7506, Integer.Sparse.eval_collectBalanced, rawRowCheck7506]

def rawRow7507 : Integer.Sparse Key := [(key2567, 2), (key2579, 2), (key2579, 2), (key2366, 2), (key2523, 2), (key2523, 2), (key2361, 2), (key2361, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2519, -2), (key2519, -2), (key2560, -2), (key2363, -2), (key2363, -2), (key2458, -2), (key2458, -2), (key2530, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2452, -2)]

theorem rawRowCheck7507 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7507 := by decide +kernel

def row7507 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2452, -4), (key2456, 4), (key2458, -4), (key2517, 4), (key2519, -4), (key2523, 4), (key2530, -4), (key2560, -2), (key2567, 2), (key2579, 4)]

theorem rowCheck7507 : row7507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7507 := by decide +kernel

theorem rowEval7507 (x : Key → ℝ) : Integer.Sparse.eval row7507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7507, Integer.Sparse.eval_collectBalanced, rawRowCheck7507]

def rawRow7508 : Integer.Sparse Key := [(key2579, 2), (key2567, 2), (key2579, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2519, -2), (key2560, -2), (key2519, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2452, -2), (key2357, -2), (key2452, -2)]

theorem rawRowCheck7508 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7508 := by decide +kernel

def row7508 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2452, -4), (key2456, 4), (key2458, -4), (key2517, 4), (key2519, -4), (key2523, 4), (key2530, -4), (key2560, -2), (key2567, 2), (key2579, 4)]

theorem rowCheck7508 : row7508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7508 := by decide +kernel

theorem rowEval7508 (x : Key → ℝ) : Integer.Sparse.eval row7508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7508, Integer.Sparse.eval_collectBalanced, rawRowCheck7508]

def rawRow7509 : Integer.Sparse Key := [(key2579, 2), (key2579, 2), (key2567, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2517, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2361, 2), (key2560, -2), (key2519, -2), (key2519, -2), (key2530, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2363, -2), (key2452, -2), (key2452, -2), (key2357, -2)]

theorem rawRowCheck7509 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7509 := by decide +kernel

def row7509 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2452, -4), (key2456, 4), (key2458, -4), (key2517, 4), (key2519, -4), (key2523, 4), (key2530, -4), (key2560, -2), (key2567, 2), (key2579, 4)]

theorem rowCheck7509 : row7509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7509 := by decide +kernel

theorem rowEval7509 (x : Key → ℝ) : Integer.Sparse.eval row7509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7509, Integer.Sparse.eval_collectBalanced, rawRowCheck7509]

def rawRow7510 : Integer.Sparse Key := [(key970, -24), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6)]

theorem rawRowCheck7510 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7510 := by decide +kernel

def row7510 : Integer.Sparse Key := [(key970, -24), (key1084, 18), (key1226, 6)]

theorem rowCheck7510 : row7510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7510 := by decide +kernel

theorem rowEval7510 (x : Key → ℝ) : Integer.Sparse.eval row7510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7510, Integer.Sparse.eval_collectBalanced, rawRowCheck7510]

def rawRow7511 : Integer.Sparse Key := [(key970, -24), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6)]

theorem rawRowCheck7511 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7511 := by decide +kernel

def row7511 : Integer.Sparse Key := [(key970, -24), (key1084, 18), (key1226, 6)]

theorem rowCheck7511 : row7511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7511 := by decide +kernel

theorem rowEval7511 (x : Key → ℝ) : Integer.Sparse.eval row7511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7511, Integer.Sparse.eval_collectBalanced, rawRowCheck7511]

def rawRow7512 : Integer.Sparse Key := [(key970, -24), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6)]

theorem rawRowCheck7512 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7512 := by decide +kernel

def row7512 : Integer.Sparse Key := [(key970, -24), (key1084, 18), (key1226, 6)]

theorem rowCheck7512 : row7512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7512 := by decide +kernel

theorem rowEval7512 (x : Key → ℝ) : Integer.Sparse.eval row7512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7512, Integer.Sparse.eval_collectBalanced, rawRowCheck7512]

def rawRow7513 : Integer.Sparse Key := [(key970, -24), (key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6)]

theorem rawRowCheck7513 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7513 := by decide +kernel

def row7513 : Integer.Sparse Key := [(key970, -24), (key1084, 18), (key1226, 6)]

theorem rowCheck7513 : row7513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7513 := by decide +kernel

theorem rowEval7513 (x : Key → ℝ) : Integer.Sparse.eval row7513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7513, Integer.Sparse.eval_collectBalanced, rawRowCheck7513]

def rawRow7514 : Integer.Sparse Key := [(key1084, -24), (key970, 6), (key1084, 6), (key1084, 6), (key1226, 6)]

theorem rawRowCheck7514 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7514 := by decide +kernel

def row7514 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7514 : row7514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7514 := by decide +kernel

theorem rowEval7514 (x : Key → ℝ) : Integer.Sparse.eval row7514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7514, Integer.Sparse.eval_collectBalanced, rawRowCheck7514]

def rawRow7515 : Integer.Sparse Key := [(key1084, -24), (key970, 6), (key1084, 6), (key1226, 6), (key1084, 6)]

theorem rawRowCheck7515 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7515 := by decide +kernel

def row7515 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7515 : row7515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7515 := by decide +kernel

theorem rowEval7515 (x : Key → ℝ) : Integer.Sparse.eval row7515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7515, Integer.Sparse.eval_collectBalanced, rawRowCheck7515]

def rawRow7516 : Integer.Sparse Key := [(key1084, -24), (key970, 6), (key1226, 6), (key1084, 6), (key1084, 6)]

theorem rawRowCheck7516 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7516 := by decide +kernel

def row7516 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7516 : row7516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7516 := by decide +kernel

theorem rowEval7516 (x : Key → ℝ) : Integer.Sparse.eval row7516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7516, Integer.Sparse.eval_collectBalanced, rawRowCheck7516]

def rawRow7517 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key970, 6), (key1084, 6), (key1226, 6)]

theorem rawRowCheck7517 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form1 = rawRow7517 := by decide +kernel

def row7517 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7517 : row7517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7517 := by decide +kernel

theorem rowEval7517 (x : Key → ℝ) : Integer.Sparse.eval row7517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7517, Integer.Sparse.eval_collectBalanced, rawRowCheck7517]

def rawRow7518 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key970, 6), (key1226, 6), (key1084, 6)]

theorem rawRowCheck7518 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form1 = rawRow7518 := by decide +kernel

def row7518 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7518 : row7518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7518 := by decide +kernel

theorem rowEval7518 (x : Key → ℝ) : Integer.Sparse.eval row7518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7518, Integer.Sparse.eval_collectBalanced, rawRowCheck7518]

def rawRow7519 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1084, 6), (key970, 6), (key1226, 6)]

theorem rawRowCheck7519 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form1 = rawRow7519 := by decide +kernel

def row7519 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7519 : row7519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7519 := by decide +kernel

theorem rowEval7519 (x : Key → ℝ) : Integer.Sparse.eval row7519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7519, Integer.Sparse.eval_collectBalanced, rawRowCheck7519]

def rawRow7520 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6)]

theorem rawRowCheck7520 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form1 = rawRow7520 := by decide +kernel

def row7520 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7520 : row7520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7520 := by decide +kernel

theorem rowEval7520 (x : Key → ℝ) : Integer.Sparse.eval row7520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7520, Integer.Sparse.eval_collectBalanced, rawRowCheck7520]

def rawRow7521 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1226, 6), (key970, 6), (key1084, 6)]

theorem rawRowCheck7521 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form1 = rawRow7521 := by decide +kernel

def row7521 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7521 : row7521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7521 := by decide +kernel

theorem rowEval7521 (x : Key → ℝ) : Integer.Sparse.eval row7521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7521, Integer.Sparse.eval_collectBalanced, rawRowCheck7521]

def rawRow7522 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1226, 6), (key1084, 6), (key970, 6)]

theorem rawRowCheck7522 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form1 = rawRow7522 := by decide +kernel

def row7522 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7522 : row7522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7522 := by decide +kernel

theorem rowEval7522 (x : Key → ℝ) : Integer.Sparse.eval row7522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7522, Integer.Sparse.eval_collectBalanced, rawRowCheck7522]

def rawRow7523 : Integer.Sparse Key := [(key1084, -24), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6)]

theorem rawRowCheck7523 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form1 = rawRow7523 := by decide +kernel

def row7523 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7523 : row7523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7523 := by decide +kernel

theorem rowEval7523 (x : Key → ℝ) : Integer.Sparse.eval row7523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7523, Integer.Sparse.eval_collectBalanced, rawRowCheck7523]

def rawRow7524 : Integer.Sparse Key := [(key1084, -24), (key1226, 6), (key1084, 6), (key970, 6), (key1084, 6)]

theorem rawRowCheck7524 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form1 = rawRow7524 := by decide +kernel

def row7524 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7524 : row7524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7524 := by decide +kernel

theorem rowEval7524 (x : Key → ℝ) : Integer.Sparse.eval row7524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7524, Integer.Sparse.eval_collectBalanced, rawRowCheck7524]

def rawRow7525 : Integer.Sparse Key := [(key1084, -24), (key1226, 6), (key1084, 6), (key1084, 6), (key970, 6)]

theorem rawRowCheck7525 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form1 = rawRow7525 := by decide +kernel

def row7525 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

theorem rowCheck7525 : row7525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7525 := by decide +kernel

theorem rowEval7525 (x : Key → ℝ) : Integer.Sparse.eval row7525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7525, Integer.Sparse.eval_collectBalanced, rawRowCheck7525]

def rawRow7526 : Integer.Sparse Key := [(key971, -6), (key979, -6), (key979, -6), (key979, -6), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2)]

theorem rawRowCheck7526 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7526 := by decide +kernel

def row7526 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1228, 6)]

theorem rowCheck7526 : row7526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7526 := by decide +kernel

theorem rowEval7526 (x : Key → ℝ) : Integer.Sparse.eval row7526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7526, Integer.Sparse.eval_collectBalanced, rawRowCheck7526]

def rawRow7527 : Integer.Sparse Key := [(key979, -6), (key971, -6), (key979, -6), (key979, -6), (key1093, 2), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key1093, 2)]

theorem rawRowCheck7527 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7527 := by decide +kernel

def row7527 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1228, 6)]

theorem rowCheck7527 : row7527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7527 := by decide +kernel

theorem rowEval7527 (x : Key → ℝ) : Integer.Sparse.eval row7527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7527, Integer.Sparse.eval_collectBalanced, rawRowCheck7527]

def rawRow7528 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key971, -6), (key979, -6), (key1093, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1093, 2)]

theorem rawRowCheck7528 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7528 := by decide +kernel

def row7528 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1228, 6)]

theorem rowCheck7528 : row7528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7528 := by decide +kernel

theorem rowEval7528 (x : Key → ℝ) : Integer.Sparse.eval row7528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7528, Integer.Sparse.eval_collectBalanced, rawRowCheck7528]

def rawRow7529 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key979, -6), (key971, -6), (key1228, 2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1085, 2)]

theorem rawRowCheck7529 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7529 := by decide +kernel

def row7529 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1228, 6)]

theorem rowCheck7529 : row7529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7529 := by decide +kernel

theorem rowEval7529 (x : Key → ℝ) : Integer.Sparse.eval row7529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7529, Integer.Sparse.eval_collectBalanced, rawRowCheck7529]

def rawRow7530 : Integer.Sparse Key := [(key1085, -6), (key1093, -6), (key1093, -6), (key1164, -6), (key971, 2), (key979, 2), (key979, 2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1164, 2), (key1164, 2), (key1245, 2)]

theorem rawRowCheck7530 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form2 = rawRow7530 := by decide +kernel

def row7530 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7530 : row7530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7530 := by decide +kernel

theorem rowEval7530 (x : Key → ℝ) : Integer.Sparse.eval row7530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7530, Integer.Sparse.eval_collectBalanced, rawRowCheck7530]

def rawRow7531 : Integer.Sparse Key := [(key1093, -6), (key1085, -6), (key1093, -6), (key1164, -6), (key979, 2), (key971, 2), (key979, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1164, 2), (key1245, 2), (key1164, 2)]

theorem rawRowCheck7531 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form2 = rawRow7531 := by decide +kernel

def row7531 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7531 : row7531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7531 := by decide +kernel

theorem rowEval7531 (x : Key → ℝ) : Integer.Sparse.eval row7531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7531, Integer.Sparse.eval_collectBalanced, rawRowCheck7531]

def rawRow7532 : Integer.Sparse Key := [(key1093, -6), (key1093, -6), (key1085, -6), (key1164, -6), (key979, 2), (key979, 2), (key971, 2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1245, 2), (key1164, 2), (key1164, 2)]

theorem rawRowCheck7532 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form2 = rawRow7532 := by decide +kernel

def row7532 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7532 : row7532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7532 := by decide +kernel

theorem rowEval7532 (x : Key → ℝ) : Integer.Sparse.eval row7532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7532, Integer.Sparse.eval_collectBalanced, rawRowCheck7532]

def rawRow7533 : Integer.Sparse Key := [(key1085, -6), (key1093, -6), (key1164, -6), (key1093, -6), (key1085, 2), (key1093, 2), (key1164, 2), (key971, 2), (key979, 2), (key1085, 2), (key1228, 2), (key1164, 2), (key1245, 2), (key979, 2), (key1093, 2), (key1228, 2)]

theorem rawRowCheck7533 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form2 = rawRow7533 := by decide +kernel

def row7533 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7533 : row7533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7533 := by decide +kernel

theorem rowEval7533 (x : Key → ℝ) : Integer.Sparse.eval row7533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7533, Integer.Sparse.eval_collectBalanced, rawRowCheck7533]

def rawRow7534 : Integer.Sparse Key := [(key1093, -6), (key1085, -6), (key1164, -6), (key1093, -6), (key1093, 2), (key1085, 2), (key1164, 2), (key979, 2), (key971, 2), (key1228, 2), (key1085, 2), (key1245, 2), (key1164, 2), (key979, 2), (key1228, 2), (key1093, 2)]

theorem rawRowCheck7534 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form2 = rawRow7534 := by decide +kernel

def row7534 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7534 : row7534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7534 := by decide +kernel

theorem rowEval7534 (x : Key → ℝ) : Integer.Sparse.eval row7534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7534, Integer.Sparse.eval_collectBalanced, rawRowCheck7534]

def rawRow7535 : Integer.Sparse Key := [(key1085, -6), (key1164, -6), (key1093, -6), (key1093, -6), (key1085, 2), (key1164, 2), (key1093, 2), (key1085, 2), (key1164, 2), (key971, 2), (key1245, 2), (key979, 2), (key1228, 2), (key1093, 2), (key979, 2), (key1228, 2)]

theorem rawRowCheck7535 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form2 = rawRow7535 := by decide +kernel

def row7535 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7535 : row7535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7535 := by decide +kernel

theorem rowEval7535 (x : Key → ℝ) : Integer.Sparse.eval row7535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7535, Integer.Sparse.eval_collectBalanced, rawRowCheck7535]

def rawRow7536 : Integer.Sparse Key := [(key1164, -6), (key1085, -6), (key1093, -6), (key1093, -6), (key1164, 2), (key1085, 2), (key1093, 2), (key1164, 2), (key1085, 2), (key1245, 2), (key971, 2), (key1228, 2), (key979, 2), (key1093, 2), (key1228, 2), (key979, 2)]

theorem rawRowCheck7536 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form2 = rawRow7536 := by decide +kernel

def row7536 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7536 : row7536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7536 := by decide +kernel

theorem rowEval7536 (x : Key → ℝ) : Integer.Sparse.eval row7536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7536, Integer.Sparse.eval_collectBalanced, rawRowCheck7536]

def rawRow7537 : Integer.Sparse Key := [(key1093, -6), (key1164, -6), (key1085, -6), (key1093, -6), (key1093, 2), (key1164, 2), (key1085, 2), (key1228, 2), (key1245, 2), (key979, 2), (key1164, 2), (key971, 2), (key1085, 2), (key1228, 2), (key979, 2), (key1093, 2)]

theorem rawRowCheck7537 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form2 = rawRow7537 := by decide +kernel

def row7537 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7537 : row7537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7537 := by decide +kernel

theorem rowEval7537 (x : Key → ℝ) : Integer.Sparse.eval row7537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7537, Integer.Sparse.eval_collectBalanced, rawRowCheck7537]

def rawRow7538 : Integer.Sparse Key := [(key1164, -6), (key1093, -6), (key1085, -6), (key1093, -6), (key1164, 2), (key1093, 2), (key1085, 2), (key1245, 2), (key1228, 2), (key1164, 2), (key979, 2), (key1085, 2), (key971, 2), (key1228, 2), (key1093, 2), (key979, 2)]

theorem rawRowCheck7538 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form2 = rawRow7538 := by decide +kernel

def row7538 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7538 : row7538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7538 := by decide +kernel

theorem rowEval7538 (x : Key → ℝ) : Integer.Sparse.eval row7538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7538, Integer.Sparse.eval_collectBalanced, rawRowCheck7538]

def rawRow7539 : Integer.Sparse Key := [(key1093, -6), (key1093, -6), (key1164, -6), (key1085, -6), (key1228, 2), (key1228, 2), (key1245, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key971, 2), (key1085, 2), (key1085, 2)]

theorem rawRowCheck7539 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form2 = rawRow7539 := by decide +kernel

def row7539 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7539 : row7539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7539 := by decide +kernel

theorem rowEval7539 (x : Key → ℝ) : Integer.Sparse.eval row7539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7539, Integer.Sparse.eval_collectBalanced, rawRowCheck7539]

def rawRow7540 : Integer.Sparse Key := [(key1093, -6), (key1164, -6), (key1093, -6), (key1085, -6), (key1228, 2), (key1245, 2), (key1228, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1085, 2), (key971, 2), (key1085, 2)]

theorem rawRowCheck7540 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form2 = rawRow7540 := by decide +kernel

def row7540 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7540 : row7540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7540 := by decide +kernel

theorem rowEval7540 (x : Key → ℝ) : Integer.Sparse.eval row7540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7540, Integer.Sparse.eval_collectBalanced, rawRowCheck7540]

def rawRow7541 : Integer.Sparse Key := [(key1164, -6), (key1093, -6), (key1093, -6), (key1085, -6), (key1245, 2), (key1228, 2), (key1228, 2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1085, 2), (key1085, 2), (key971, 2)]

theorem rawRowCheck7541 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form2 = rawRow7541 := by decide +kernel

def row7541 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

theorem rowCheck7541 : row7541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7541 := by decide +kernel

theorem rowEval7541 (x : Key → ℝ) : Integer.Sparse.eval row7541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7541, Integer.Sparse.eval_collectBalanced, rawRowCheck7541]

def rawRow7542 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2400, -6), (key2432, -6), (key2466, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2475, 2), (key2498, 2)]

theorem rawRowCheck7542 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7542 := by decide +kernel

def row7542 : Integer.Sparse Key := [(key2400, -18), (key2432, -6), (key2466, 12), (key2475, 6), (key2498, 6)]

theorem rowCheck7542 : row7542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7542 := by decide +kernel

theorem rowEval7542 (x : Key → ℝ) : Integer.Sparse.eval row7542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7542, Integer.Sparse.eval_collectBalanced, rawRowCheck7542]

def rawRow7543 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2432, -6), (key2400, -6), (key2466, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2498, 2), (key2475, 2)]

theorem rawRowCheck7543 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7543 := by decide +kernel

def row7543 : Integer.Sparse Key := [(key2400, -18), (key2432, -6), (key2466, 12), (key2475, 6), (key2498, 6)]

theorem rowCheck7543 : row7543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7543 := by decide +kernel

theorem rowEval7543 (x : Key → ℝ) : Integer.Sparse.eval row7543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7543, Integer.Sparse.eval_collectBalanced, rawRowCheck7543]

def rawRow7544 : Integer.Sparse Key := [(key2400, -6), (key2432, -6), (key2400, -6), (key2400, -6), (key2475, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2475, 2), (key2475, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck7544 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7544 := by decide +kernel

def row7544 : Integer.Sparse Key := [(key2400, -18), (key2432, -6), (key2466, 12), (key2475, 6), (key2498, 6)]

theorem rowCheck7544 : row7544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7544 := by decide +kernel

theorem rowEval7544 (x : Key → ℝ) : Integer.Sparse.eval row7544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7544, Integer.Sparse.eval_collectBalanced, rawRowCheck7544]

def rawRow7545 : Integer.Sparse Key := [(key2432, -6), (key2400, -6), (key2400, -6), (key2400, -6), (key2498, 2), (key2498, 2), (key2498, 2), (key2475, 2), (key2475, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck7545 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7545 := by decide +kernel

def row7545 : Integer.Sparse Key := [(key2400, -18), (key2432, -6), (key2466, 12), (key2475, 6), (key2498, 6)]

theorem rowCheck7545 : row7545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7545 := by decide +kernel

theorem rowEval7545 (x : Key → ℝ) : Integer.Sparse.eval row7545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7545, Integer.Sparse.eval_collectBalanced, rawRowCheck7545]

def rawRow7546 : Integer.Sparse Key := [(key2372, -6), (key2466, -6), (key2466, -6), (key2498, -6), (key2372, 2), (key2372, 2), (key2385, 2), (key2400, 2), (key2400, 2), (key2432, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2475, 2), (key2498, 2)]

theorem rawRowCheck7546 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7546 := by decide +kernel

def row7546 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7546 : row7546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7546 := by decide +kernel

theorem rowEval7546 (x : Key → ℝ) : Integer.Sparse.eval row7546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7546, Integer.Sparse.eval_collectBalanced, rawRowCheck7546]

def rawRow7547 : Integer.Sparse Key := [(key2372, -6), (key2466, -6), (key2498, -6), (key2466, -6), (key2372, 2), (key2385, 2), (key2372, 2), (key2400, 2), (key2432, 2), (key2400, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2498, 2), (key2475, 2)]

theorem rawRowCheck7547 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7547 := by decide +kernel

def row7547 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7547 : row7547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7547 := by decide +kernel

theorem rowEval7547 (x : Key → ℝ) : Integer.Sparse.eval row7547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7547, Integer.Sparse.eval_collectBalanced, rawRowCheck7547]

def rawRow7548 : Integer.Sparse Key := [(key2372, -6), (key2498, -6), (key2466, -6), (key2466, -6), (key2385, 2), (key2372, 2), (key2372, 2), (key2432, 2), (key2400, 2), (key2400, 2), (key2498, 2), (key2498, 2), (key2475, 2), (key2475, 2), (key2466, 2), (key2466, 2)]

theorem rawRowCheck7548 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7548 := by decide +kernel

def row7548 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7548 : row7548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7548 := by decide +kernel

theorem rowEval7548 (x : Key → ℝ) : Integer.Sparse.eval row7548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7548, Integer.Sparse.eval_collectBalanced, rawRowCheck7548]

def rawRow7549 : Integer.Sparse Key := [(key2466, -6), (key2372, -6), (key2466, -6), (key2498, -6), (key2400, 2), (key2466, 2), (key2475, 2), (key2372, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2385, 2), (key2400, 2), (key2432, 2), (key2475, 2), (key2498, 2)]

theorem rawRowCheck7549 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form3 = rawRow7549 := by decide +kernel

def row7549 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7549 : row7549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7549 := by decide +kernel

theorem rowEval7549 (x : Key → ℝ) : Integer.Sparse.eval row7549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7549, Integer.Sparse.eval_collectBalanced, rawRowCheck7549]

def rawRow7550 : Integer.Sparse Key := [(key2466, -6), (key2372, -6), (key2498, -6), (key2466, -6), (key2400, 2), (key2475, 2), (key2466, 2), (key2372, 2), (key2498, 2), (key2466, 2), (key2385, 2), (key2372, 2), (key2432, 2), (key2400, 2), (key2498, 2), (key2475, 2)]

theorem rawRowCheck7550 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form3 = rawRow7550 := by decide +kernel

def row7550 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7550 : row7550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7550 := by decide +kernel

theorem rowEval7550 (x : Key → ℝ) : Integer.Sparse.eval row7550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7550, Integer.Sparse.eval_collectBalanced, rawRowCheck7550]

def rawRow7551 : Integer.Sparse Key := [(key2466, -6), (key2466, -6), (key2372, -6), (key2498, -6), (key2466, 2), (key2400, 2), (key2475, 2), (key2466, 2), (key2372, 2), (key2498, 2), (key2400, 2), (key2475, 2), (key2372, 2), (key2498, 2), (key2385, 2), (key2432, 2)]

theorem rawRowCheck7551 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form3 = rawRow7551 := by decide +kernel

def row7551 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

theorem rowCheck7551 : row7551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7551 := by decide +kernel

theorem rowEval7551 (x : Key → ℝ) : Integer.Sparse.eval row7551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7551, Integer.Sparse.eval_collectBalanced, rawRowCheck7551]

end MUB6.Certificate.GramRows

end OAI

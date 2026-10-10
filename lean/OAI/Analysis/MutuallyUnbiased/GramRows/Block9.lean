import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow384 : Integer.Sparse Key := [(key270, -2), (key275, 1), (key276, 1), (key245, 2), (key266, -1), (key276, -1), (key243, -1), (key245, -1), (key255, 1), (key266, 1), (key334, 2), (key344, -1), (key345, -1), (key311, -2), (key338, 1), (key345, 1), (key309, 1), (key311, 1), (key323, -1), (key334, -1), (key424, -2), (key479, 1), (key485, 1), (key403, 2), (key473, -1), (key485, -1), (key392, -1), (key403, -1), (key413, 1), (key424, 1), (key587, 1), (key588, 1), (key605, -1), (key611, -1), (key576, -1), (key577, -1), (key599, 1), (key611, 1), (key571, 1), (key577, 1), (key581, -1), (key588, -1)]

theorem rawRowCheck384 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form3 = rawRow384 := by decide +kernel

def row384 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck384 : row384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow384 := by decide +kernel

theorem rowEval384 (x : Key → ℝ) : Integer.Sparse.eval row384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck384, Integer.Sparse.eval_collectBalanced, rawRowCheck384]

def rawRow385 : Integer.Sparse Key := [(key270, -2), (key276, 1), (key275, 1), (key245, 2), (key276, -1), (key266, -1), (key245, -1), (key243, -1), (key266, 1), (key255, 1), (key334, 2), (key345, -1), (key344, -1), (key311, -2), (key345, 1), (key338, 1), (key311, 1), (key309, 1), (key334, -1), (key323, -1), (key424, -2), (key485, 1), (key479, 1), (key403, 2), (key485, -1), (key473, -1), (key403, -1), (key392, -1), (key424, 1), (key413, 1), (key588, 1), (key587, 1), (key611, -1), (key605, -1), (key577, -1), (key576, -1), (key611, 1), (key599, 1), (key577, 1), (key571, 1), (key588, -1), (key581, -1)]

theorem rawRowCheck385 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form3 = rawRow385 := by decide +kernel

def row385 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck385 : row385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow385 := by decide +kernel

theorem rowEval385 (x : Key → ℝ) : Integer.Sparse.eval row385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck385, Integer.Sparse.eval_collectBalanced, rawRowCheck385]

def rawRow386 : Integer.Sparse Key := [(key275, -2), (key270, 1), (key276, 1), (key266, 2), (key245, -1), (key276, -1), (key255, -1), (key266, -1), (key243, 1), (key275, 1), (key344, 2), (key334, -1), (key345, -1), (key338, -2), (key311, 1), (key345, 1), (key323, 1), (key338, 1), (key309, -1), (key344, -1), (key479, -2), (key424, 1), (key485, 1), (key473, 2), (key403, -1), (key485, -1), (key413, -1), (key473, -1), (key392, 1), (key479, 1), (key605, 1), (key614, 1), (key587, -1), (key616, -1), (key599, -1), (key613, -1), (key576, 1), (key616, 1), (key581, 1), (key613, 1), (key571, -1), (key614, -1)]

theorem rawRowCheck386 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form3 = rawRow386 := by decide +kernel

def row386 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck386 : row386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow386 := by decide +kernel

theorem rowEval386 (x : Key → ℝ) : Integer.Sparse.eval row386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck386, Integer.Sparse.eval_collectBalanced, rawRowCheck386]

def rawRow387 : Integer.Sparse Key := [(key275, -2), (key276, 1), (key270, 1), (key266, 2), (key276, -1), (key245, -1), (key266, -1), (key255, -1), (key275, 1), (key243, 1), (key344, 2), (key345, -1), (key334, -1), (key338, -2), (key345, 1), (key311, 1), (key338, 1), (key323, 1), (key344, -1), (key309, -1), (key479, -2), (key485, 1), (key424, 1), (key473, 2), (key485, -1), (key403, -1), (key473, -1), (key413, -1), (key479, 1), (key392, 1), (key614, 1), (key605, 1), (key616, -1), (key587, -1), (key613, -1), (key599, -1), (key616, 1), (key576, 1), (key613, 1), (key581, 1), (key614, -1), (key571, -1)]

theorem rawRowCheck387 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form3 = rawRow387 := by decide +kernel

def row387 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck387 : row387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow387 := by decide +kernel

theorem rowEval387 (x : Key → ℝ) : Integer.Sparse.eval row387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck387, Integer.Sparse.eval_collectBalanced, rawRowCheck387]

def rawRow388 : Integer.Sparse Key := [(key309, -2), (key311, 1), (key311, 1), (key323, 2), (key338, -1), (key338, -1), (key334, -1), (key334, -1), (key344, 1), (key344, 1), (key243, 2), (key245, -1), (key245, -1), (key413, -2), (key424, 1), (key424, 1), (key581, 1), (key581, 1), (key587, -1), (key587, -1), (key255, -2), (key266, 1), (key266, 1), (key323, 2), (key334, -1), (key334, -1), (key599, -1), (key599, -1), (key605, 1), (key605, 1), (key270, 1), (key270, 1), (key275, -1), (key275, -1), (key338, -1), (key338, -1), (key344, 1), (key344, 1), (key473, 1), (key473, 1), (key479, -1), (key479, -1)]

theorem rawRowCheck388 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form3 = rawRow388 := by decide +kernel

def row388 : Integer.Sparse Key := [(key243, 2), (key245, -2), (key255, -2), (key266, 2), (key270, 2), (key275, -2), (key309, -2), (key311, 2), (key323, 4), (key334, -4), (key338, -4), (key344, 4), (key413, -2), (key424, 2), (key473, 2), (key479, -2), (key581, 2), (key587, -2), (key599, -2), (key605, 2)]

theorem rowCheck388 : row388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow388 := by decide +kernel

theorem rowEval388 (x : Key → ℝ) : Integer.Sparse.eval row388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck388, Integer.Sparse.eval_collectBalanced, rawRowCheck388]

def rawRow389 : Integer.Sparse Key := [(key311, -2), (key309, 1), (key311, 1), (key338, 2), (key323, -1), (key338, -1), (key344, -1), (key345, -1), (key334, 1), (key345, 1), (key245, 2), (key243, -1), (key245, -1), (key424, -2), (key413, 1), (key424, 1), (key587, 1), (key588, 1), (key581, -1), (key588, -1), (key266, -2), (key255, 1), (key266, 1), (key334, 2), (key323, -1), (key334, -1), (key605, -1), (key611, -1), (key599, 1), (key611, 1), (key275, 1), (key276, 1), (key270, -1), (key276, -1), (key344, -1), (key345, -1), (key338, 1), (key345, 1), (key479, 1), (key485, 1), (key473, -1), (key485, -1)]

theorem rawRowCheck389 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form3 = rawRow389 := by decide +kernel

def row389 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck389 : row389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow389 := by decide +kernel

theorem rowEval389 (x : Key → ℝ) : Integer.Sparse.eval row389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck389, Integer.Sparse.eval_collectBalanced, rawRowCheck389]

def rawRow390 : Integer.Sparse Key := [(key311, -2), (key311, 1), (key309, 1), (key338, 2), (key338, -1), (key323, -1), (key345, -1), (key344, -1), (key345, 1), (key334, 1), (key245, 2), (key245, -1), (key243, -1), (key424, -2), (key424, 1), (key413, 1), (key588, 1), (key587, 1), (key588, -1), (key581, -1), (key266, -2), (key266, 1), (key255, 1), (key334, 2), (key334, -1), (key323, -1), (key611, -1), (key605, -1), (key611, 1), (key599, 1), (key276, 1), (key275, 1), (key276, -1), (key270, -1), (key345, -1), (key344, -1), (key345, 1), (key338, 1), (key485, 1), (key479, 1), (key485, -1), (key473, -1)]

theorem rawRowCheck390 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form3 = rawRow390 := by decide +kernel

def row390 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck390 : row390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow390 := by decide +kernel

theorem rowEval390 (x : Key → ℝ) : Integer.Sparse.eval row390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck390, Integer.Sparse.eval_collectBalanced, rawRowCheck390]

def rawRow391 : Integer.Sparse Key := [(key323, -2), (key334, 1), (key334, 1), (key309, 2), (key344, -1), (key344, -1), (key311, -1), (key311, -1), (key338, 1), (key338, 1), (key413, 2), (key424, -1), (key424, -1), (key243, -2), (key587, 1), (key587, 1), (key245, 1), (key245, 1), (key424, -1), (key424, -1), (key323, -2), (key599, 1), (key599, 1), (key255, 2), (key605, -1), (key605, -1), (key266, -1), (key266, -1), (key334, 1), (key334, 1), (key338, 1), (key338, 1), (key473, -1), (key473, -1), (key270, -1), (key270, -1), (key479, 1), (key479, 1), (key275, 1), (key275, 1), (key344, -1), (key344, -1)]

theorem rawRowCheck391 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form3 = rawRow391 := by decide +kernel

def row391 : Integer.Sparse Key := [(key243, -2), (key245, 2), (key255, 2), (key266, -2), (key270, -2), (key275, 2), (key309, 2), (key311, -2), (key323, -4), (key334, 4), (key338, 4), (key344, -4), (key413, 2), (key424, -4), (key473, -2), (key479, 2), (key587, 2), (key599, 2), (key605, -2)]

theorem rowCheck391 : row391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow391 := by decide +kernel

theorem rowEval391 (x : Key → ℝ) : Integer.Sparse.eval row391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck391, Integer.Sparse.eval_collectBalanced, rawRowCheck391]

def rawRow392 : Integer.Sparse Key := [(key334, -2), (key323, 1), (key334, 1), (key344, 2), (key309, -1), (key344, -1), (key338, -1), (key345, -1), (key311, 1), (key345, 1), (key424, 2), (key413, -1), (key424, -1), (key587, -2), (key243, 1), (key587, 1), (key424, 1), (key588, 1), (key245, -1), (key588, -1), (key599, -2), (key323, 1), (key599, 1), (key605, 2), (key255, -1), (key605, -1), (key334, -1), (key611, -1), (key266, 1), (key611, 1), (key473, 1), (key613, 1), (key338, -1), (key613, -1), (key479, -1), (key614, -1), (key270, 1), (key614, 1), (key344, 1), (key616, 1), (key275, -1), (key616, -1)]

theorem rawRowCheck392 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form3 = rawRow392 := by decide +kernel

def row392 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck392 : row392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow392 := by decide +kernel

theorem rowEval392 (x : Key → ℝ) : Integer.Sparse.eval row392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck392, Integer.Sparse.eval_collectBalanced, rawRowCheck392]

def rawRow393 : Integer.Sparse Key := [(key334, -2), (key334, 1), (key323, 1), (key344, 2), (key344, -1), (key309, -1), (key345, -1), (key338, -1), (key345, 1), (key311, 1), (key424, 2), (key424, -1), (key413, -1), (key587, -2), (key587, 1), (key243, 1), (key588, 1), (key424, 1), (key588, -1), (key245, -1), (key599, -2), (key599, 1), (key323, 1), (key605, 2), (key605, -1), (key255, -1), (key611, -1), (key334, -1), (key611, 1), (key266, 1), (key613, 1), (key473, 1), (key613, -1), (key338, -1), (key614, -1), (key479, -1), (key614, 1), (key270, 1), (key616, 1), (key344, 1), (key616, -1), (key275, -1)]

theorem rawRowCheck393 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form3 = rawRow393 := by decide +kernel

def row393 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck393 : row393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow393 := by decide +kernel

theorem rowEval393 (x : Key → ℝ) : Integer.Sparse.eval row393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck393, Integer.Sparse.eval_collectBalanced, rawRowCheck393]

def rawRow394 : Integer.Sparse Key := [(key338, -2), (key344, 1), (key345, 1), (key311, 2), (key334, -1), (key345, -1), (key309, -1), (key311, -1), (key323, 1), (key338, 1), (key581, 2), (key587, -1), (key588, -1), (key245, -2), (key424, 1), (key588, 1), (key243, 1), (key245, 1), (key413, -1), (key424, -1), (key334, -2), (key605, 1), (key611, 1), (key266, 2), (key599, -1), (key611, -1), (key255, -1), (key266, -1), (key323, 1), (key334, 1), (key344, 1), (key345, 1), (key479, -1), (key485, -1), (key275, -1), (key276, -1), (key473, 1), (key485, 1), (key270, 1), (key276, 1), (key338, -1), (key345, -1)]

theorem rawRowCheck394 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form3 = rawRow394 := by decide +kernel

def row394 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key473, 1), (key479, -1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck394 : row394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow394 := by decide +kernel

theorem rowEval394 (x : Key → ℝ) : Integer.Sparse.eval row394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck394, Integer.Sparse.eval_collectBalanced, rawRowCheck394]

def rawRow395 : Integer.Sparse Key := [(key338, -2), (key345, 1), (key344, 1), (key311, 2), (key345, -1), (key334, -1), (key311, -1), (key309, -1), (key338, 1), (key323, 1), (key581, 2), (key588, -1), (key587, -1), (key245, -2), (key588, 1), (key424, 1), (key245, 1), (key243, 1), (key424, -1), (key413, -1), (key334, -2), (key611, 1), (key605, 1), (key266, 2), (key611, -1), (key599, -1), (key266, -1), (key255, -1), (key334, 1), (key323, 1), (key345, 1), (key344, 1), (key485, -1), (key479, -1), (key276, -1), (key275, -1), (key485, 1), (key473, 1), (key276, 1), (key270, 1), (key345, -1), (key338, -1)]

theorem rawRowCheck395 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form3 = rawRow395 := by decide +kernel

def row395 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key473, 1), (key479, -1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck395 : row395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow395 := by decide +kernel

theorem rowEval395 (x : Key → ℝ) : Integer.Sparse.eval row395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck395, Integer.Sparse.eval_collectBalanced, rawRowCheck395]

def rawRow396 : Integer.Sparse Key := [(key344, -2), (key338, 1), (key345, 1), (key334, 2), (key311, -1), (key345, -1), (key323, -1), (key334, -1), (key309, 1), (key344, 1), (key587, 2), (key581, -1), (key588, -1), (key424, -2), (key245, 1), (key588, 1), (key413, 1), (key424, 1), (key243, -1), (key587, -1), (key605, -2), (key334, 1), (key611, 1), (key599, 2), (key266, -1), (key611, -1), (key323, -1), (key599, -1), (key255, 1), (key605, 1), (key479, 1), (key614, 1), (key344, -1), (key616, -1), (key473, -1), (key613, -1), (key275, 1), (key616, 1), (key338, 1), (key613, 1), (key270, -1), (key614, -1)]

theorem rawRowCheck396 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form3 = rawRow396 := by decide +kernel

def row396 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck396 : row396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow396 := by decide +kernel

theorem rowEval396 (x : Key → ℝ) : Integer.Sparse.eval row396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck396, Integer.Sparse.eval_collectBalanced, rawRowCheck396]

def rawRow397 : Integer.Sparse Key := [(key344, -2), (key345, 1), (key338, 1), (key334, 2), (key345, -1), (key311, -1), (key334, -1), (key323, -1), (key344, 1), (key309, 1), (key587, 2), (key588, -1), (key581, -1), (key424, -2), (key588, 1), (key245, 1), (key424, 1), (key413, 1), (key587, -1), (key243, -1), (key605, -2), (key611, 1), (key334, 1), (key599, 2), (key611, -1), (key266, -1), (key599, -1), (key323, -1), (key605, 1), (key255, 1), (key614, 1), (key479, 1), (key616, -1), (key344, -1), (key613, -1), (key473, -1), (key616, 1), (key275, 1), (key613, 1), (key338, 1), (key614, -1), (key270, -1)]

theorem rawRowCheck397 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form3 = rawRow397 := by decide +kernel

def row397 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck397 : row397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow397 := by decide +kernel

theorem rowEval397 (x : Key → ℝ) : Integer.Sparse.eval row397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck397, Integer.Sparse.eval_collectBalanced, rawRowCheck397]

def rawRow398 : Integer.Sparse Key := [(key392, -2), (key403, 1), (key403, 1), (key413, 2), (key473, -1), (key473, -1), (key424, -1), (key424, -1), (key479, 1), (key479, 1), (key255, 2), (key266, -1), (key266, -1), (key323, -2), (key599, 1), (key599, 1), (key334, 1), (key334, 1), (key605, -1), (key605, -1), (key243, -2), (key275, 1), (key275, 1), (key309, 2), (key344, -1), (key344, -1), (key576, -1), (key576, -1), (key587, 1), (key587, 1), (key245, 1), (key245, 1), (key266, -1), (key266, -1), (key311, -1), (key311, -1), (key334, 1), (key334, 1), (key403, 1), (key403, 1), (key424, -1), (key424, -1)]

theorem rawRowCheck398 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form3 = rawRow398 := by decide +kernel

def row398 : Integer.Sparse Key := [(key243, -2), (key245, 2), (key255, 2), (key266, -4), (key275, 2), (key309, 2), (key311, -2), (key323, -2), (key334, 4), (key344, -2), (key392, -2), (key403, 4), (key413, 2), (key424, -4), (key473, -2), (key479, 2), (key576, -2), (key587, 2), (key599, 2), (key605, -2)]

theorem rowCheck398 : row398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow398 := by decide +kernel

theorem rowEval398 (x : Key → ℝ) : Integer.Sparse.eval row398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck398, Integer.Sparse.eval_collectBalanced, rawRowCheck398]

def rawRow399 : Integer.Sparse Key := [(key403, -2), (key392, 1), (key403, 1), (key473, 2), (key413, -1), (key473, -1), (key479, -1), (key485, -1), (key424, 1), (key485, 1), (key266, 2), (key255, -1), (key266, -1), (key599, -2), (key323, 1), (key599, 1), (key605, 1), (key611, 1), (key334, -1), (key611, -1), (key275, -2), (key243, 1), (key275, 1), (key344, 2), (key309, -1), (key344, -1), (key587, -1), (key616, -1), (key576, 1), (key616, 1), (key266, 1), (key276, 1), (key245, -1), (key276, -1), (key334, -1), (key345, -1), (key311, 1), (key345, 1), (key424, 1), (key485, 1), (key403, -1), (key485, -1)]

theorem rawRowCheck399 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form3 = rawRow399 := by decide +kernel

def row399 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck399 : row399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow399 := by decide +kernel

theorem rowEval399 (x : Key → ℝ) : Integer.Sparse.eval row399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck399, Integer.Sparse.eval_collectBalanced, rawRowCheck399]

def rawRow400 : Integer.Sparse Key := [(key403, -2), (key403, 1), (key392, 1), (key473, 2), (key473, -1), (key413, -1), (key485, -1), (key479, -1), (key485, 1), (key424, 1), (key266, 2), (key266, -1), (key255, -1), (key599, -2), (key599, 1), (key323, 1), (key611, 1), (key605, 1), (key611, -1), (key334, -1), (key275, -2), (key275, 1), (key243, 1), (key344, 2), (key344, -1), (key309, -1), (key616, -1), (key587, -1), (key616, 1), (key576, 1), (key276, 1), (key266, 1), (key276, -1), (key245, -1), (key345, -1), (key334, -1), (key345, 1), (key311, 1), (key485, 1), (key424, 1), (key485, -1), (key403, -1)]

theorem rawRowCheck400 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form3 = rawRow400 := by decide +kernel

def row400 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck400 : row400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow400 := by decide +kernel

theorem rowEval400 (x : Key → ℝ) : Integer.Sparse.eval row400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck400, Integer.Sparse.eval_collectBalanced, rawRowCheck400]

def rawRow401 : Integer.Sparse Key := [(key413, -2), (key424, 1), (key424, 1), (key392, 2), (key479, -1), (key479, -1), (key403, -1), (key403, -1), (key473, 1), (key473, 1), (key323, 2), (key334, -1), (key334, -1), (key255, -2), (key605, 1), (key605, 1), (key266, 1), (key266, 1), (key599, -1), (key599, -1), (key309, -2), (key344, 1), (key344, 1), (key243, 2), (key587, -1), (key587, -1), (key275, -1), (key275, -1), (key344, 1), (key344, 1), (key311, 1), (key311, 1), (key403, -1), (key403, -1), (key245, -1), (key245, -1), (key424, 1), (key424, 1), (key266, 1), (key266, 1), (key334, -1), (key334, -1)]

theorem rawRowCheck401 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form3 = rawRow401 := by decide +kernel

def row401 : Integer.Sparse Key := [(key243, 2), (key245, -2), (key255, -2), (key266, 4), (key275, -2), (key309, -2), (key311, 2), (key323, 2), (key334, -4), (key344, 4), (key392, 2), (key403, -4), (key413, -2), (key424, 4), (key473, 2), (key479, -2), (key587, -2), (key599, -2), (key605, 2)]

theorem rowCheck401 : row401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow401 := by decide +kernel

theorem rowEval401 (x : Key → ℝ) : Integer.Sparse.eval row401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck401, Integer.Sparse.eval_collectBalanced, rawRowCheck401]

def rawRow402 : Integer.Sparse Key := [(key424, -2), (key413, 1), (key424, 1), (key479, 2), (key392, -1), (key479, -1), (key473, -1), (key485, -1), (key403, 1), (key485, 1), (key334, 2), (key323, -1), (key334, -1), (key605, -2), (key255, 1), (key605, 1), (key599, 1), (key611, 1), (key266, -1), (key611, -1), (key344, -2), (key309, 1), (key344, 1), (key587, 2), (key243, -1), (key587, -1), (key344, -1), (key616, -1), (key275, 1), (key616, 1), (key403, 1), (key577, 1), (key311, -1), (key577, -1), (key424, -1), (key588, -1), (key245, 1), (key588, 1), (key334, 1), (key611, 1), (key266, -1), (key611, -1)]

theorem rawRowCheck402 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form3 = rawRow402 := by decide +kernel

def row402 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key344, -2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck402 : row402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow402 := by decide +kernel

theorem rowEval402 (x : Key → ℝ) : Integer.Sparse.eval row402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck402, Integer.Sparse.eval_collectBalanced, rawRowCheck402]

def rawRow403 : Integer.Sparse Key := [(key424, -2), (key424, 1), (key413, 1), (key479, 2), (key479, -1), (key392, -1), (key485, -1), (key473, -1), (key485, 1), (key403, 1), (key334, 2), (key334, -1), (key323, -1), (key605, -2), (key605, 1), (key255, 1), (key611, 1), (key599, 1), (key611, -1), (key266, -1), (key344, -2), (key344, 1), (key309, 1), (key587, 2), (key587, -1), (key243, -1), (key616, -1), (key344, -1), (key616, 1), (key275, 1), (key577, 1), (key403, 1), (key577, -1), (key311, -1), (key588, -1), (key424, -1), (key588, 1), (key245, 1), (key611, 1), (key334, 1), (key611, -1), (key266, -1)]

theorem rawRowCheck403 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form3 = rawRow403 := by decide +kernel

def row403 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key344, -2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck403 : row403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow403 := by decide +kernel

theorem rowEval403 (x : Key → ℝ) : Integer.Sparse.eval row403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck403, Integer.Sparse.eval_collectBalanced, rawRowCheck403]

def rawRow404 : Integer.Sparse Key := [(key473, -2), (key479, 1), (key485, 1), (key403, 2), (key424, -1), (key485, -1), (key392, -1), (key403, -1), (key413, 1), (key473, 1), (key599, 2), (key605, -1), (key611, -1), (key266, -2), (key334, 1), (key611, 1), (key255, 1), (key266, 1), (key323, -1), (key599, -1), (key576, -2), (key587, 1), (key616, 1), (key275, 2), (key344, -1), (key616, -1), (key243, -1), (key275, -1), (key309, 1), (key344, 1), (key334, 1), (key345, 1), (key424, -1), (key485, -1), (key266, -1), (key276, -1), (key403, 1), (key485, 1), (key245, 1), (key276, 1), (key311, -1), (key345, -1)]

theorem rawRowCheck404 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form3 = rawRow404 := by decide +kernel

def row404 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key576, -2), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck404 : row404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow404 := by decide +kernel

theorem rowEval404 (x : Key → ℝ) : Integer.Sparse.eval row404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck404, Integer.Sparse.eval_collectBalanced, rawRowCheck404]

def rawRow405 : Integer.Sparse Key := [(key473, -2), (key485, 1), (key479, 1), (key403, 2), (key485, -1), (key424, -1), (key403, -1), (key392, -1), (key473, 1), (key413, 1), (key599, 2), (key611, -1), (key605, -1), (key266, -2), (key611, 1), (key334, 1), (key266, 1), (key255, 1), (key599, -1), (key323, -1), (key576, -2), (key616, 1), (key587, 1), (key275, 2), (key616, -1), (key344, -1), (key275, -1), (key243, -1), (key344, 1), (key309, 1), (key345, 1), (key334, 1), (key485, -1), (key424, -1), (key276, -1), (key266, -1), (key485, 1), (key403, 1), (key276, 1), (key245, 1), (key345, -1), (key311, -1)]

theorem rawRowCheck405 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form3 = rawRow405 := by decide +kernel

def row405 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key576, -2), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck405 : row405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow405 := by decide +kernel

theorem rowEval405 (x : Key → ℝ) : Integer.Sparse.eval row405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck405, Integer.Sparse.eval_collectBalanced, rawRowCheck405]

def rawRow406 : Integer.Sparse Key := [(key479, -2), (key473, 1), (key485, 1), (key424, 2), (key403, -1), (key485, -1), (key413, -1), (key424, -1), (key392, 1), (key479, 1), (key605, 2), (key599, -1), (key611, -1), (key334, -2), (key266, 1), (key611, 1), (key323, 1), (key334, 1), (key255, -1), (key605, -1), (key587, -2), (key576, 1), (key616, 1), (key344, 2), (key275, -1), (key616, -1), (key309, -1), (key344, -1), (key243, 1), (key587, 1), (key424, 1), (key588, 1), (key334, -1), (key611, -1), (key403, -1), (key577, -1), (key266, 1), (key611, 1), (key311, 1), (key577, 1), (key245, -1), (key588, -1)]

theorem rawRowCheck406 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form3 = rawRow406 := by decide +kernel

def row406 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck406 : row406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow406 := by decide +kernel

theorem rowEval406 (x : Key → ℝ) : Integer.Sparse.eval row406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck406, Integer.Sparse.eval_collectBalanced, rawRowCheck406]

def rawRow407 : Integer.Sparse Key := [(key479, -2), (key485, 1), (key473, 1), (key424, 2), (key485, -1), (key403, -1), (key424, -1), (key413, -1), (key479, 1), (key392, 1), (key605, 2), (key611, -1), (key599, -1), (key334, -2), (key611, 1), (key266, 1), (key334, 1), (key323, 1), (key605, -1), (key255, -1), (key587, -2), (key616, 1), (key576, 1), (key344, 2), (key616, -1), (key275, -1), (key344, -1), (key309, -1), (key587, 1), (key243, 1), (key588, 1), (key424, 1), (key611, -1), (key334, -1), (key577, -1), (key403, -1), (key611, 1), (key266, 1), (key577, 1), (key311, 1), (key588, -1), (key245, -1)]

theorem rawRowCheck407 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form3 = rawRow407 := by decide +kernel

def row407 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck407 : row407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow407 := by decide +kernel

theorem rowEval407 (x : Key → ℝ) : Integer.Sparse.eval row407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck407, Integer.Sparse.eval_collectBalanced, rawRowCheck407]

def rawRow408 : Integer.Sparse Key := [(key571, -2), (key576, 1), (key577, 1), (key581, 2), (key599, -1), (key613, -1), (key587, -1), (key588, -1), (key605, 1), (key614, 1), (key270, 2), (key275, -1), (key276, -1), (key338, -2), (key473, 1), (key613, 1), (key344, 1), (key345, 1), (key479, -1), (key614, -1), (key245, -2), (key266, 1), (key276, 1), (key311, 2), (key403, -1), (key577, -1), (key334, -1), (key345, -1), (key424, 1), (key588, 1), (key243, 1), (key245, 1), (key255, -1), (key266, -1), (key309, -1), (key311, -1), (key323, 1), (key334, 1), (key392, 1), (key403, 1), (key413, -1), (key424, -1)]

theorem rawRowCheck408 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form3 = rawRow408 := by decide +kernel

def row408 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key270, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key338, -2), (key344, 1), (key392, 1), (key413, -1), (key473, 1), (key479, -1), (key571, -2), (key576, 1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck408 : row408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow408 := by decide +kernel

theorem rowEval408 (x : Key → ℝ) : Integer.Sparse.eval row408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck408, Integer.Sparse.eval_collectBalanced, rawRowCheck408]

def rawRow409 : Integer.Sparse Key := [(key571, -2), (key577, 1), (key576, 1), (key581, 2), (key613, -1), (key599, -1), (key588, -1), (key587, -1), (key614, 1), (key605, 1), (key270, 2), (key276, -1), (key275, -1), (key338, -2), (key613, 1), (key473, 1), (key345, 1), (key344, 1), (key614, -1), (key479, -1), (key245, -2), (key276, 1), (key266, 1), (key311, 2), (key577, -1), (key403, -1), (key345, -1), (key334, -1), (key588, 1), (key424, 1), (key245, 1), (key243, 1), (key266, -1), (key255, -1), (key311, -1), (key309, -1), (key334, 1), (key323, 1), (key403, 1), (key392, 1), (key424, -1), (key413, -1)]

theorem rawRowCheck409 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form3 = rawRow409 := by decide +kernel

def row409 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key270, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key338, -2), (key344, 1), (key392, 1), (key413, -1), (key473, 1), (key479, -1), (key571, -2), (key576, 1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck409 : row409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow409 := by decide +kernel

theorem rowEval409 (x : Key → ℝ) : Integer.Sparse.eval row409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck409, Integer.Sparse.eval_collectBalanced, rawRowCheck409]

def rawRow410 : Integer.Sparse Key := [(key576, -2), (key571, 1), (key577, 1), (key599, 2), (key581, -1), (key613, -1), (key605, -1), (key611, -1), (key587, 1), (key616, 1), (key275, 2), (key270, -1), (key276, -1), (key473, -2), (key338, 1), (key613, 1), (key479, 1), (key485, 1), (key344, -1), (key616, -1), (key266, -2), (key245, 1), (key276, 1), (key403, 2), (key311, -1), (key577, -1), (key424, -1), (key485, -1), (key334, 1), (key611, 1), (key255, 1), (key266, 1), (key243, -1), (key275, -1), (key323, -1), (key338, -1), (key309, 1), (key344, 1), (key413, 1), (key473, 1), (key392, -1), (key479, -1)]

theorem rawRowCheck410 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form3 = rawRow410 := by decide +kernel

def row410 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key392, -1), (key403, 2), (key413, 1), (key424, -1), (key473, -1), (key571, 1), (key576, -2), (key581, -1), (key587, 1), (key599, 2), (key605, -1)]

theorem rowCheck410 : row410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow410 := by decide +kernel

theorem rowEval410 (x : Key → ℝ) : Integer.Sparse.eval row410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck410, Integer.Sparse.eval_collectBalanced, rawRowCheck410]

def rawRow411 : Integer.Sparse Key := [(key576, -2), (key577, 1), (key571, 1), (key599, 2), (key613, -1), (key581, -1), (key611, -1), (key605, -1), (key616, 1), (key587, 1), (key275, 2), (key276, -1), (key270, -1), (key473, -2), (key613, 1), (key338, 1), (key485, 1), (key479, 1), (key616, -1), (key344, -1), (key266, -2), (key276, 1), (key245, 1), (key403, 2), (key577, -1), (key311, -1), (key485, -1), (key424, -1), (key611, 1), (key334, 1), (key266, 1), (key255, 1), (key275, -1), (key243, -1), (key338, -1), (key323, -1), (key344, 1), (key309, 1), (key473, 1), (key413, 1), (key479, -1), (key392, -1)]

theorem rawRowCheck411 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form3 = rawRow411 := by decide +kernel

def row411 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key392, -1), (key403, 2), (key413, 1), (key424, -1), (key473, -1), (key571, 1), (key576, -2), (key581, -1), (key587, 1), (key599, 2), (key605, -1)]

theorem rowCheck411 : row411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow411 := by decide +kernel

theorem rowEval411 (x : Key → ℝ) : Integer.Sparse.eval row411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck411, Integer.Sparse.eval_collectBalanced, rawRowCheck411]

def rawRow412 : Integer.Sparse Key := [(key581, -2), (key587, 1), (key588, 1), (key571, 2), (key605, -1), (key614, -1), (key576, -1), (key577, -1), (key599, 1), (key613, 1), (key338, 2), (key344, -1), (key345, -1), (key270, -2), (key479, 1), (key614, 1), (key275, 1), (key276, 1), (key473, -1), (key613, -1), (key311, -2), (key334, 1), (key345, 1), (key245, 2), (key424, -1), (key588, -1), (key266, -1), (key276, -1), (key403, 1), (key577, 1), (key309, 1), (key311, 1), (key323, -1), (key338, -1), (key243, -1), (key245, -1), (key413, 1), (key424, 1), (key255, 1), (key266, 1), (key323, -1), (key334, -1)]

theorem rawRowCheck412 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form3 = rawRow412 := by decide +kernel

def row412 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key338, 1), (key344, -1), (key403, 1), (key413, 1), (key473, -1), (key479, 1), (key571, 2), (key576, -1), (key581, -2), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck412 : row412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow412 := by decide +kernel

theorem rowEval412 (x : Key → ℝ) : Integer.Sparse.eval row412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck412, Integer.Sparse.eval_collectBalanced, rawRowCheck412]

def rawRow413 : Integer.Sparse Key := [(key581, -2), (key588, 1), (key587, 1), (key571, 2), (key614, -1), (key605, -1), (key577, -1), (key576, -1), (key613, 1), (key599, 1), (key338, 2), (key345, -1), (key344, -1), (key270, -2), (key614, 1), (key479, 1), (key276, 1), (key275, 1), (key613, -1), (key473, -1), (key311, -2), (key345, 1), (key334, 1), (key245, 2), (key588, -1), (key424, -1), (key276, -1), (key266, -1), (key577, 1), (key403, 1), (key311, 1), (key309, 1), (key338, -1), (key323, -1), (key245, -1), (key243, -1), (key424, 1), (key413, 1), (key266, 1), (key255, 1), (key334, -1), (key323, -1)]

theorem rawRowCheck413 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form3 = rawRow413 := by decide +kernel

def row413 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key338, 1), (key344, -1), (key403, 1), (key413, 1), (key473, -1), (key479, 1), (key571, 2), (key576, -1), (key581, -2), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck413 : row413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow413 := by decide +kernel

theorem rowEval413 (x : Key → ℝ) : Integer.Sparse.eval row413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck413, Integer.Sparse.eval_collectBalanced, rawRowCheck413]

def rawRow414 : Integer.Sparse Key := [(key587, -2), (key581, 1), (key588, 1), (key605, 2), (key571, -1), (key614, -1), (key599, -1), (key611, -1), (key576, 1), (key616, 1), (key344, 2), (key338, -1), (key345, -1), (key479, -2), (key270, 1), (key614, 1), (key473, 1), (key485, 1), (key275, -1), (key616, -1), (key334, -2), (key311, 1), (key345, 1), (key424, 2), (key245, -1), (key588, -1), (key403, -1), (key485, -1), (key266, 1), (key611, 1), (key323, 1), (key334, 1), (key309, -1), (key344, -1), (key413, -1), (key424, -1), (key243, 1), (key587, 1), (key323, 1), (key599, 1), (key255, -1), (key605, -1)]

theorem rawRowCheck414 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form3 = rawRow414 := by decide +kernel

def row414 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -1), (key338, -1), (key344, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -2), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key605, 1)]

theorem rowCheck414 : row414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow414 := by decide +kernel

theorem rowEval414 (x : Key → ℝ) : Integer.Sparse.eval row414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck414, Integer.Sparse.eval_collectBalanced, rawRowCheck414]

def rawRow415 : Integer.Sparse Key := [(key587, -2), (key588, 1), (key581, 1), (key605, 2), (key614, -1), (key571, -1), (key611, -1), (key599, -1), (key616, 1), (key576, 1), (key344, 2), (key345, -1), (key338, -1), (key479, -2), (key614, 1), (key270, 1), (key485, 1), (key473, 1), (key616, -1), (key275, -1), (key334, -2), (key345, 1), (key311, 1), (key424, 2), (key588, -1), (key245, -1), (key485, -1), (key403, -1), (key611, 1), (key266, 1), (key334, 1), (key323, 1), (key344, -1), (key309, -1), (key424, -1), (key413, -1), (key587, 1), (key243, 1), (key599, 1), (key323, 1), (key605, -1), (key255, -1)]

theorem rawRowCheck415 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form3 = rawRow415 := by decide +kernel

def row415 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -1), (key338, -1), (key344, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -2), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key605, 1)]

theorem rowCheck415 : row415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow415 := by decide +kernel

theorem rowEval415 (x : Key → ℝ) : Integer.Sparse.eval row415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck415, Integer.Sparse.eval_collectBalanced, rawRowCheck415]

end MUB6.Certificate.GramRows

end OAI

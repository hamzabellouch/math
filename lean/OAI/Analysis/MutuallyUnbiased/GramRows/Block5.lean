import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow256 : Integer.Sparse Key := [(key254, -1), (key269, -1), (key254, 2), (key264, 1), (key274, 1), (key242, -1), (key264, -1), (key265, -2), (key244, 1), (key265, 1), (key322, 1), (key337, 1), (key322, -2), (key332, -1), (key343, -1), (key308, 1), (key332, 1), (key333, 2), (key310, -1), (key333, -1), (key446, -1), (key472, -1), (key412, 1), (key446, 1), (key454, 1), (key478, 1), (key391, -1), (key454, -1), (key423, -1), (key462, -1), (key402, 1), (key462, 1), (key598, 2), (key580, -1), (key598, -1), (key604, -2), (key570, 1), (key604, 1), (key586, 1), (key610, 1), (key575, -1), (key610, -1)]

theorem rawRowCheck256 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form0 = rawRow256 := by decide +kernel

def row256 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck256 : row256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow256 := by decide +kernel

theorem rowEval256 (x : Key → ℝ) : Integer.Sparse.eval row256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck256, Integer.Sparse.eval_collectBalanced, rawRowCheck256]

def rawRow257 : Integer.Sparse Key := [(key269, -1), (key254, -1), (key254, 2), (key274, 1), (key264, 1), (key264, -1), (key242, -1), (key265, -2), (key265, 1), (key244, 1), (key337, 1), (key322, 1), (key322, -2), (key343, -1), (key332, -1), (key332, 1), (key308, 1), (key333, 2), (key333, -1), (key310, -1), (key472, -1), (key446, -1), (key446, 1), (key412, 1), (key478, 1), (key454, 1), (key454, -1), (key391, -1), (key462, -1), (key423, -1), (key462, 1), (key402, 1), (key598, 2), (key598, -1), (key580, -1), (key604, -2), (key604, 1), (key570, 1), (key610, 1), (key586, 1), (key610, -1), (key575, -1)]

theorem rawRowCheck257 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form0 = rawRow257 := by decide +kernel

def row257 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck257 : row257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow257 := by decide +kernel

theorem rowEval257 (x : Key → ℝ) : Integer.Sparse.eval row257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck257, Integer.Sparse.eval_collectBalanced, rawRowCheck257]

def rawRow258 : Integer.Sparse Key := [(key264, -1), (key265, -1), (key274, 2), (key242, 1), (key244, 1), (key269, -1), (key274, -1), (key242, -2), (key254, 1), (key264, 1), (key332, 1), (key333, 1), (key343, -2), (key308, -1), (key310, -1), (key337, 1), (key343, 1), (key308, 2), (key322, -1), (key332, -1), (key422, -1), (key423, -1), (key478, 1), (key484, 1), (key401, 1), (key402, 1), (key472, -1), (key484, -1), (key391, -1), (key401, -1), (key412, 1), (key422, 1), (key586, 2), (key604, -1), (key610, -1), (key575, -2), (key598, 1), (key610, 1), (key570, 1), (key575, 1), (key580, -1), (key586, -1)]

theorem rawRowCheck258 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form0 = rawRow258 := by decide +kernel

def row258 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck258 : row258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow258 := by decide +kernel

theorem rowEval258 (x : Key → ℝ) : Integer.Sparse.eval row258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck258, Integer.Sparse.eval_collectBalanced, rawRowCheck258]

def rawRow259 : Integer.Sparse Key := [(key265, -1), (key264, -1), (key274, 2), (key244, 1), (key242, 1), (key274, -1), (key269, -1), (key242, -2), (key264, 1), (key254, 1), (key333, 1), (key332, 1), (key343, -2), (key310, -1), (key308, -1), (key343, 1), (key337, 1), (key308, 2), (key332, -1), (key322, -1), (key423, -1), (key422, -1), (key484, 1), (key478, 1), (key402, 1), (key401, 1), (key484, -1), (key472, -1), (key401, -1), (key391, -1), (key422, 1), (key412, 1), (key586, 2), (key610, -1), (key604, -1), (key575, -2), (key610, 1), (key598, 1), (key575, 1), (key570, 1), (key586, -1), (key580, -1)]

theorem rawRowCheck259 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form0 = rawRow259 := by decide +kernel

def row259 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck259 : row259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow259 := by decide +kernel

theorem rowEval259 (x : Key → ℝ) : Integer.Sparse.eval row259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck259, Integer.Sparse.eval_collectBalanced, rawRowCheck259]

def rawRow260 : Integer.Sparse Key := [(key264, -1), (key274, -1), (key265, 2), (key254, 1), (key269, 1), (key244, -1), (key265, -1), (key254, -2), (key242, 1), (key264, 1), (key332, 1), (key343, 1), (key333, -2), (key322, -1), (key337, -1), (key310, 1), (key333, 1), (key322, 2), (key308, -1), (key332, -1), (key454, -1), (key478, -1), (key423, 1), (key462, 1), (key446, 1), (key472, 1), (key402, -1), (key462, -1), (key412, -1), (key446, -1), (key391, 1), (key454, 1), (key604, 2), (key586, -1), (key610, -1), (key598, -2), (key575, 1), (key610, 1), (key580, 1), (key598, 1), (key570, -1), (key604, -1)]

theorem rawRowCheck260 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form0 = rawRow260 := by decide +kernel

def row260 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck260 : row260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow260 := by decide +kernel

theorem rowEval260 (x : Key → ℝ) : Integer.Sparse.eval row260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck260, Integer.Sparse.eval_collectBalanced, rawRowCheck260]

def rawRow261 : Integer.Sparse Key := [(key274, -1), (key264, -1), (key265, 2), (key269, 1), (key254, 1), (key265, -1), (key244, -1), (key254, -2), (key264, 1), (key242, 1), (key343, 1), (key332, 1), (key333, -2), (key337, -1), (key322, -1), (key333, 1), (key310, 1), (key322, 2), (key332, -1), (key308, -1), (key478, -1), (key454, -1), (key462, 1), (key423, 1), (key472, 1), (key446, 1), (key462, -1), (key402, -1), (key446, -1), (key412, -1), (key454, 1), (key391, 1), (key604, 2), (key610, -1), (key586, -1), (key598, -2), (key610, 1), (key575, 1), (key598, 1), (key580, 1), (key604, -1), (key570, -1)]

theorem rawRowCheck261 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form0 = rawRow261 := by decide +kernel

def row261 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck261 : row261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow261 := by decide +kernel

theorem rowEval261 (x : Key → ℝ) : Integer.Sparse.eval row261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck261, Integer.Sparse.eval_collectBalanced, rawRowCheck261]

def rawRow262 : Integer.Sparse Key := [(key308, -1), (key308, -1), (key310, 2), (key391, 1), (key391, 1), (key402, -1), (key402, -1), (key570, -2), (key575, 1), (key575, 1), (key242, 1), (key242, 1), (key244, -2), (key412, -1), (key412, -1), (key423, 1), (key423, 1), (key580, 2), (key586, -1), (key586, -1), (key254, -1), (key254, -1), (key265, 1), (key265, 1), (key322, 1), (key322, 1), (key333, -1), (key333, -1), (key598, -1), (key598, -1), (key604, 1), (key604, 1), (key269, 2), (key274, -1), (key274, -1), (key337, -2), (key343, 1), (key343, 1), (key472, 1), (key472, 1), (key478, -1), (key478, -1)]

theorem rawRowCheck262 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form0 = rawRow262 := by decide +kernel

def row262 : Integer.Sparse Key := [(key242, 2), (key244, -2), (key254, -2), (key265, 2), (key269, 2), (key274, -2), (key308, -2), (key310, 2), (key322, 2), (key333, -2), (key337, -2), (key343, 2), (key391, 2), (key402, -2), (key412, -2), (key423, 2), (key472, 2), (key478, -2), (key570, -2), (key575, 2), (key580, 2), (key586, -2), (key598, -2), (key604, 2)]

theorem rowCheck262 : row262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow262 := by decide +kernel

theorem rowEval262 (x : Key → ℝ) : Integer.Sparse.eval row262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck262, Integer.Sparse.eval_collectBalanced, rawRowCheck262]

def rawRow263 : Integer.Sparse Key := [(key308, -1), (key310, -1), (key308, 2), (key401, 1), (key402, 1), (key391, -1), (key401, -1), (key575, -2), (key570, 1), (key575, 1), (key242, 1), (key244, 1), (key242, -2), (key422, -1), (key423, -1), (key412, 1), (key422, 1), (key586, 2), (key580, -1), (key586, -1), (key264, -1), (key265, -1), (key254, 1), (key264, 1), (key332, 1), (key333, 1), (key322, -1), (key332, -1), (key604, -1), (key610, -1), (key598, 1), (key610, 1), (key274, 2), (key269, -1), (key274, -1), (key343, -2), (key337, 1), (key343, 1), (key478, 1), (key484, 1), (key472, -1), (key484, -1)]

theorem rawRowCheck263 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form0 = rawRow263 := by decide +kernel

def row263 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck263 : row263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow263 := by decide +kernel

theorem rowEval263 (x : Key → ℝ) : Integer.Sparse.eval row263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck263, Integer.Sparse.eval_collectBalanced, rawRowCheck263]

def rawRow264 : Integer.Sparse Key := [(key310, -1), (key308, -1), (key308, 2), (key402, 1), (key401, 1), (key401, -1), (key391, -1), (key575, -2), (key575, 1), (key570, 1), (key244, 1), (key242, 1), (key242, -2), (key423, -1), (key422, -1), (key422, 1), (key412, 1), (key586, 2), (key586, -1), (key580, -1), (key265, -1), (key264, -1), (key264, 1), (key254, 1), (key333, 1), (key332, 1), (key332, -1), (key322, -1), (key610, -1), (key604, -1), (key610, 1), (key598, 1), (key274, 2), (key274, -1), (key269, -1), (key343, -2), (key343, 1), (key337, 1), (key484, 1), (key478, 1), (key484, -1), (key472, -1)]

theorem rawRowCheck264 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form0 = rawRow264 := by decide +kernel

def row264 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck264 : row264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow264 := by decide +kernel

theorem rowEval264 (x : Key → ℝ) : Integer.Sparse.eval row264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck264, Integer.Sparse.eval_collectBalanced, rawRowCheck264]

def rawRow265 : Integer.Sparse Key := [(key391, -1), (key391, -1), (key570, 2), (key308, 1), (key308, 1), (key575, -1), (key575, -1), (key310, -2), (key402, 1), (key402, 1), (key412, 1), (key412, 1), (key580, -2), (key242, -1), (key242, -1), (key586, 1), (key586, 1), (key244, 2), (key423, -1), (key423, -1), (key322, -1), (key322, -1), (key598, 1), (key598, 1), (key254, 1), (key254, 1), (key604, -1), (key604, -1), (key265, -1), (key265, -1), (key333, 1), (key333, 1), (key337, 2), (key472, -1), (key472, -1), (key269, -2), (key478, 1), (key478, 1), (key274, 1), (key274, 1), (key343, -1), (key343, -1)]

theorem rawRowCheck265 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form0 = rawRow265 := by decide +kernel

def row265 : Integer.Sparse Key := [(key242, -2), (key244, 2), (key254, 2), (key265, -2), (key269, -2), (key274, 2), (key308, 2), (key310, -2), (key322, -2), (key333, 2), (key337, 2), (key343, -2), (key391, -2), (key402, 2), (key412, 2), (key423, -2), (key472, -2), (key478, 2), (key570, 2), (key575, -2), (key580, -2), (key586, 2), (key598, 2), (key604, -2)]

theorem rowCheck265 : row265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow265 := by decide +kernel

theorem rowEval265 (x : Key → ℝ) : Integer.Sparse.eval row265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck265, Integer.Sparse.eval_collectBalanced, rawRowCheck265]

def rawRow266 : Integer.Sparse Key := [(key391, -1), (key570, -1), (key391, 2), (key401, 1), (key575, 1), (key308, -1), (key401, -1), (key402, -2), (key310, 1), (key402, 1), (key412, 1), (key580, 1), (key412, -2), (key422, -1), (key586, -1), (key242, 1), (key422, 1), (key423, 2), (key244, -1), (key423, -1), (key446, -1), (key598, -1), (key322, 1), (key446, 1), (key454, 1), (key604, 1), (key254, -1), (key454, -1), (key333, -1), (key462, -1), (key265, 1), (key462, 1), (key472, 2), (key337, -1), (key472, -1), (key478, -2), (key269, 1), (key478, 1), (key343, 1), (key484, 1), (key274, -1), (key484, -1)]

theorem rawRowCheck266 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form0 = rawRow266 := by decide +kernel

def row266 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck266 : row266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow266 := by decide +kernel

theorem rowEval266 (x : Key → ℝ) : Integer.Sparse.eval row266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck266, Integer.Sparse.eval_collectBalanced, rawRowCheck266]

def rawRow267 : Integer.Sparse Key := [(key570, -1), (key391, -1), (key391, 2), (key575, 1), (key401, 1), (key401, -1), (key308, -1), (key402, -2), (key402, 1), (key310, 1), (key580, 1), (key412, 1), (key412, -2), (key586, -1), (key422, -1), (key422, 1), (key242, 1), (key423, 2), (key423, -1), (key244, -1), (key598, -1), (key446, -1), (key446, 1), (key322, 1), (key604, 1), (key454, 1), (key454, -1), (key254, -1), (key462, -1), (key333, -1), (key462, 1), (key265, 1), (key472, 2), (key472, -1), (key337, -1), (key478, -2), (key478, 1), (key269, 1), (key484, 1), (key343, 1), (key484, -1), (key274, -1)]

theorem rawRowCheck267 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form0 = rawRow267 := by decide +kernel

def row267 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck267 : row267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow267 := by decide +kernel

theorem rowEval267 (x : Key → ℝ) : Integer.Sparse.eval row267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck267, Integer.Sparse.eval_collectBalanced, rawRowCheck267]

def rawRow268 : Integer.Sparse Key := [(key401, -1), (key402, -1), (key575, 2), (key308, 1), (key310, 1), (key570, -1), (key575, -1), (key308, -2), (key391, 1), (key401, 1), (key422, 1), (key423, 1), (key586, -2), (key242, -1), (key244, -1), (key580, 1), (key586, 1), (key242, 2), (key412, -1), (key422, -1), (key332, -1), (key333, -1), (key604, 1), (key610, 1), (key264, 1), (key265, 1), (key598, -1), (key610, -1), (key254, -1), (key264, -1), (key322, 1), (key332, 1), (key343, 2), (key478, -1), (key484, -1), (key274, -2), (key472, 1), (key484, 1), (key269, 1), (key274, 1), (key337, -1), (key343, -1)]

theorem rawRowCheck268 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form0 = rawRow268 := by decide +kernel

def row268 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck268 : row268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow268 := by decide +kernel

theorem rowEval268 (x : Key → ℝ) : Integer.Sparse.eval row268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck268, Integer.Sparse.eval_collectBalanced, rawRowCheck268]

def rawRow269 : Integer.Sparse Key := [(key402, -1), (key401, -1), (key575, 2), (key310, 1), (key308, 1), (key575, -1), (key570, -1), (key308, -2), (key401, 1), (key391, 1), (key423, 1), (key422, 1), (key586, -2), (key244, -1), (key242, -1), (key586, 1), (key580, 1), (key242, 2), (key422, -1), (key412, -1), (key333, -1), (key332, -1), (key610, 1), (key604, 1), (key265, 1), (key264, 1), (key610, -1), (key598, -1), (key264, -1), (key254, -1), (key332, 1), (key322, 1), (key343, 2), (key484, -1), (key478, -1), (key274, -2), (key484, 1), (key472, 1), (key274, 1), (key269, 1), (key343, -1), (key337, -1)]

theorem rawRowCheck269 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form0 = rawRow269 := by decide +kernel

def row269 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck269 : row269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow269 := by decide +kernel

theorem rowEval269 (x : Key → ℝ) : Integer.Sparse.eval row269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck269, Integer.Sparse.eval_collectBalanced, rawRowCheck269]

def rawRow270 : Integer.Sparse Key := [(key401, -1), (key575, -1), (key402, 2), (key391, 1), (key570, 1), (key310, -1), (key402, -1), (key391, -2), (key308, 1), (key401, 1), (key422, 1), (key586, 1), (key423, -2), (key412, -1), (key580, -1), (key244, 1), (key423, 1), (key412, 2), (key242, -1), (key422, -1), (key454, -1), (key604, -1), (key333, 1), (key462, 1), (key446, 1), (key598, 1), (key265, -1), (key462, -1), (key322, -1), (key446, -1), (key254, 1), (key454, 1), (key478, 2), (key343, -1), (key484, -1), (key472, -2), (key274, 1), (key484, 1), (key337, 1), (key472, 1), (key269, -1), (key478, -1)]

theorem rawRowCheck270 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form0 = rawRow270 := by decide +kernel

def row270 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck270 : row270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow270 := by decide +kernel

theorem rowEval270 (x : Key → ℝ) : Integer.Sparse.eval row270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck270, Integer.Sparse.eval_collectBalanced, rawRowCheck270]

def rawRow271 : Integer.Sparse Key := [(key575, -1), (key401, -1), (key402, 2), (key570, 1), (key391, 1), (key402, -1), (key310, -1), (key391, -2), (key401, 1), (key308, 1), (key586, 1), (key422, 1), (key423, -2), (key580, -1), (key412, -1), (key423, 1), (key244, 1), (key412, 2), (key422, -1), (key242, -1), (key604, -1), (key454, -1), (key462, 1), (key333, 1), (key598, 1), (key446, 1), (key462, -1), (key265, -1), (key446, -1), (key322, -1), (key454, 1), (key254, 1), (key478, 2), (key484, -1), (key343, -1), (key472, -2), (key484, 1), (key274, 1), (key472, 1), (key337, 1), (key478, -1), (key269, -1)]

theorem rawRowCheck271 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form0 = rawRow271 := by decide +kernel

def row271 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck271 : row271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow271 := by decide +kernel

theorem rowEval271 (x : Key → ℝ) : Integer.Sparse.eval row271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck271, Integer.Sparse.eval_collectBalanced, rawRowCheck271]

def rawRow272 : Integer.Sparse Key := [(key322, -1), (key322, -1), (key337, 2), (key412, 1), (key412, 1), (key472, -1), (key472, -1), (key580, -2), (key598, 1), (key598, 1), (key254, 1), (key254, 1), (key269, -2), (key391, -1), (key391, -1), (key478, 1), (key478, 1), (key570, 2), (key604, -1), (key604, -1), (key242, -1), (key242, -1), (key274, 1), (key274, 1), (key308, 1), (key308, 1), (key343, -1), (key343, -1), (key575, -1), (key575, -1), (key586, 1), (key586, 1), (key244, 2), (key265, -1), (key265, -1), (key310, -2), (key333, 1), (key333, 1), (key402, 1), (key402, 1), (key423, -1), (key423, -1)]

theorem rawRowCheck272 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form0 = rawRow272 := by decide +kernel

def row272 : Integer.Sparse Key := [(key242, -2), (key244, 2), (key254, 2), (key265, -2), (key269, -2), (key274, 2), (key308, 2), (key310, -2), (key322, -2), (key333, 2), (key337, 2), (key343, -2), (key391, -2), (key402, 2), (key412, 2), (key423, -2), (key472, -2), (key478, 2), (key570, 2), (key575, -2), (key580, -2), (key586, 2), (key598, 2), (key604, -2)]

theorem rowCheck272 : row272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow272 := by decide +kernel

theorem rowEval272 (x : Key → ℝ) : Integer.Sparse.eval row272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck272, Integer.Sparse.eval_collectBalanced, rawRowCheck272]

def rawRow273 : Integer.Sparse Key := [(key322, -1), (key337, -1), (key322, 2), (key446, 1), (key472, 1), (key412, -1), (key446, -1), (key598, -2), (key580, 1), (key598, 1), (key254, 1), (key269, 1), (key254, -2), (key454, -1), (key478, -1), (key391, 1), (key454, 1), (key604, 2), (key570, -1), (key604, -1), (key264, -1), (key274, -1), (key242, 1), (key264, 1), (key332, 1), (key343, 1), (key308, -1), (key332, -1), (key586, -1), (key610, -1), (key575, 1), (key610, 1), (key265, 2), (key244, -1), (key265, -1), (key333, -2), (key310, 1), (key333, 1), (key423, 1), (key462, 1), (key402, -1), (key462, -1)]

theorem rawRowCheck273 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form0 = rawRow273 := by decide +kernel

def row273 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck273 : row273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow273 := by decide +kernel

theorem rowEval273 (x : Key → ℝ) : Integer.Sparse.eval row273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck273, Integer.Sparse.eval_collectBalanced, rawRowCheck273]

def rawRow274 : Integer.Sparse Key := [(key337, -1), (key322, -1), (key322, 2), (key472, 1), (key446, 1), (key446, -1), (key412, -1), (key598, -2), (key598, 1), (key580, 1), (key269, 1), (key254, 1), (key254, -2), (key478, -1), (key454, -1), (key454, 1), (key391, 1), (key604, 2), (key604, -1), (key570, -1), (key274, -1), (key264, -1), (key264, 1), (key242, 1), (key343, 1), (key332, 1), (key332, -1), (key308, -1), (key610, -1), (key586, -1), (key610, 1), (key575, 1), (key265, 2), (key265, -1), (key244, -1), (key333, -2), (key333, 1), (key310, 1), (key462, 1), (key423, 1), (key462, -1), (key402, -1)]

theorem rawRowCheck274 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form0 = rawRow274 := by decide +kernel

def row274 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck274 : row274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow274 := by decide +kernel

theorem rowEval274 (x : Key → ℝ) : Integer.Sparse.eval row274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck274, Integer.Sparse.eval_collectBalanced, rawRowCheck274]

def rawRow275 : Integer.Sparse Key := [(key412, -1), (key412, -1), (key580, 2), (key322, 1), (key322, 1), (key598, -1), (key598, -1), (key337, -2), (key472, 1), (key472, 1), (key391, 1), (key391, 1), (key570, -2), (key254, -1), (key254, -1), (key604, 1), (key604, 1), (key269, 2), (key478, -1), (key478, -1), (key308, -1), (key308, -1), (key575, 1), (key575, 1), (key242, 1), (key242, 1), (key586, -1), (key586, -1), (key274, -1), (key274, -1), (key343, 1), (key343, 1), (key310, 2), (key402, -1), (key402, -1), (key244, -2), (key423, 1), (key423, 1), (key265, 1), (key265, 1), (key333, -1), (key333, -1)]

theorem rawRowCheck275 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form0 = rawRow275 := by decide +kernel

def row275 : Integer.Sparse Key := [(key242, 2), (key244, -2), (key254, -2), (key265, 2), (key269, 2), (key274, -2), (key308, -2), (key310, 2), (key322, 2), (key333, -2), (key337, -2), (key343, 2), (key391, 2), (key402, -2), (key412, -2), (key423, 2), (key472, 2), (key478, -2), (key570, -2), (key575, 2), (key580, 2), (key586, -2), (key598, -2), (key604, 2)]

theorem rowCheck275 : row275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow275 := by decide +kernel

theorem rowEval275 (x : Key → ℝ) : Integer.Sparse.eval row275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck275, Integer.Sparse.eval_collectBalanced, rawRowCheck275]

def rawRow276 : Integer.Sparse Key := [(key412, -1), (key580, -1), (key412, 2), (key446, 1), (key598, 1), (key322, -1), (key446, -1), (key472, -2), (key337, 1), (key472, 1), (key391, 1), (key570, 1), (key391, -2), (key454, -1), (key604, -1), (key254, 1), (key454, 1), (key478, 2), (key269, -1), (key478, -1), (key401, -1), (key575, -1), (key308, 1), (key401, 1), (key422, 1), (key586, 1), (key242, -1), (key422, -1), (key343, -1), (key484, -1), (key274, 1), (key484, 1), (key402, 2), (key310, -1), (key402, -1), (key423, -2), (key244, 1), (key423, 1), (key333, 1), (key462, 1), (key265, -1), (key462, -1)]

theorem rawRowCheck276 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form0 = rawRow276 := by decide +kernel

def row276 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck276 : row276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow276 := by decide +kernel

theorem rowEval276 (x : Key → ℝ) : Integer.Sparse.eval row276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck276, Integer.Sparse.eval_collectBalanced, rawRowCheck276]

def rawRow277 : Integer.Sparse Key := [(key580, -1), (key412, -1), (key412, 2), (key598, 1), (key446, 1), (key446, -1), (key322, -1), (key472, -2), (key472, 1), (key337, 1), (key570, 1), (key391, 1), (key391, -2), (key604, -1), (key454, -1), (key454, 1), (key254, 1), (key478, 2), (key478, -1), (key269, -1), (key575, -1), (key401, -1), (key401, 1), (key308, 1), (key586, 1), (key422, 1), (key422, -1), (key242, -1), (key484, -1), (key343, -1), (key484, 1), (key274, 1), (key402, 2), (key402, -1), (key310, -1), (key423, -2), (key423, 1), (key244, 1), (key462, 1), (key333, 1), (key462, -1), (key265, -1)]

theorem rawRowCheck277 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form0 = rawRow277 := by decide +kernel

def row277 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck277 : row277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow277 := by decide +kernel

theorem rowEval277 (x : Key → ℝ) : Integer.Sparse.eval row277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck277, Integer.Sparse.eval_collectBalanced, rawRowCheck277]

def rawRow278 : Integer.Sparse Key := [(key446, -1), (key472, -1), (key598, 2), (key322, 1), (key337, 1), (key580, -1), (key598, -1), (key322, -2), (key412, 1), (key446, 1), (key454, 1), (key478, 1), (key604, -2), (key254, -1), (key269, -1), (key570, 1), (key604, 1), (key254, 2), (key391, -1), (key454, -1), (key332, -1), (key343, -1), (key586, 1), (key610, 1), (key264, 1), (key274, 1), (key575, -1), (key610, -1), (key242, -1), (key264, -1), (key308, 1), (key332, 1), (key333, 2), (key423, -1), (key462, -1), (key265, -2), (key402, 1), (key462, 1), (key244, 1), (key265, 1), (key310, -1), (key333, -1)]

theorem rawRowCheck278 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form0 = rawRow278 := by decide +kernel

def row278 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck278 : row278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow278 := by decide +kernel

theorem rowEval278 (x : Key → ℝ) : Integer.Sparse.eval row278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck278, Integer.Sparse.eval_collectBalanced, rawRowCheck278]

def rawRow279 : Integer.Sparse Key := [(key472, -1), (key446, -1), (key598, 2), (key337, 1), (key322, 1), (key598, -1), (key580, -1), (key322, -2), (key446, 1), (key412, 1), (key478, 1), (key454, 1), (key604, -2), (key269, -1), (key254, -1), (key604, 1), (key570, 1), (key254, 2), (key454, -1), (key391, -1), (key343, -1), (key332, -1), (key610, 1), (key586, 1), (key274, 1), (key264, 1), (key610, -1), (key575, -1), (key264, -1), (key242, -1), (key332, 1), (key308, 1), (key333, 2), (key462, -1), (key423, -1), (key265, -2), (key462, 1), (key402, 1), (key265, 1), (key244, 1), (key333, -1), (key310, -1)]

theorem rawRowCheck279 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form0 = rawRow279 := by decide +kernel

def row279 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck279 : row279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow279 := by decide +kernel

theorem rowEval279 (x : Key → ℝ) : Integer.Sparse.eval row279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck279, Integer.Sparse.eval_collectBalanced, rawRowCheck279]

def rawRow280 : Integer.Sparse Key := [(key446, -1), (key598, -1), (key472, 2), (key412, 1), (key580, 1), (key337, -1), (key472, -1), (key412, -2), (key322, 1), (key446, 1), (key454, 1), (key604, 1), (key478, -2), (key391, -1), (key570, -1), (key269, 1), (key478, 1), (key391, 2), (key254, -1), (key454, -1), (key422, -1), (key586, -1), (key343, 1), (key484, 1), (key401, 1), (key575, 1), (key274, -1), (key484, -1), (key308, -1), (key401, -1), (key242, 1), (key422, 1), (key423, 2), (key333, -1), (key462, -1), (key402, -2), (key265, 1), (key462, 1), (key310, 1), (key402, 1), (key244, -1), (key423, -1)]

theorem rawRowCheck280 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form0 = rawRow280 := by decide +kernel

def row280 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck280 : row280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow280 := by decide +kernel

theorem rowEval280 (x : Key → ℝ) : Integer.Sparse.eval row280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck280, Integer.Sparse.eval_collectBalanced, rawRowCheck280]

def rawRow281 : Integer.Sparse Key := [(key598, -1), (key446, -1), (key472, 2), (key580, 1), (key412, 1), (key472, -1), (key337, -1), (key412, -2), (key446, 1), (key322, 1), (key604, 1), (key454, 1), (key478, -2), (key570, -1), (key391, -1), (key478, 1), (key269, 1), (key391, 2), (key454, -1), (key254, -1), (key586, -1), (key422, -1), (key484, 1), (key343, 1), (key575, 1), (key401, 1), (key484, -1), (key274, -1), (key401, -1), (key308, -1), (key422, 1), (key242, 1), (key423, 2), (key462, -1), (key333, -1), (key402, -2), (key462, 1), (key265, 1), (key402, 1), (key310, 1), (key423, -1), (key244, -1)]

theorem rawRowCheck281 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form0 = rawRow281 := by decide +kernel

def row281 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck281 : row281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow281 := by decide +kernel

theorem rowEval281 (x : Key → ℝ) : Integer.Sparse.eval row281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck281, Integer.Sparse.eval_collectBalanced, rawRowCheck281]

def rawRow282 : Integer.Sparse Key := [(key332, -1), (key333, -1), (key343, 2), (key422, 1), (key423, 1), (key478, -1), (key484, -1), (key586, -2), (key604, 1), (key610, 1), (key264, 1), (key265, 1), (key274, -2), (key401, -1), (key402, -1), (key472, 1), (key484, 1), (key575, 2), (key598, -1), (key610, -1), (key242, -1), (key244, -1), (key269, 1), (key274, 1), (key308, 1), (key310, 1), (key337, -1), (key343, -1), (key570, -1), (key575, -1), (key580, 1), (key586, 1), (key242, 2), (key254, -1), (key264, -1), (key308, -2), (key322, 1), (key332, 1), (key391, 1), (key401, 1), (key412, -1), (key422, -1)]

theorem rawRowCheck282 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form0 = rawRow282 := by decide +kernel

def row282 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck282 : row282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow282 := by decide +kernel

theorem rowEval282 (x : Key → ℝ) : Integer.Sparse.eval row282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck282, Integer.Sparse.eval_collectBalanced, rawRowCheck282]

def rawRow283 : Integer.Sparse Key := [(key333, -1), (key332, -1), (key343, 2), (key423, 1), (key422, 1), (key484, -1), (key478, -1), (key586, -2), (key610, 1), (key604, 1), (key265, 1), (key264, 1), (key274, -2), (key402, -1), (key401, -1), (key484, 1), (key472, 1), (key575, 2), (key610, -1), (key598, -1), (key244, -1), (key242, -1), (key274, 1), (key269, 1), (key310, 1), (key308, 1), (key343, -1), (key337, -1), (key575, -1), (key570, -1), (key586, 1), (key580, 1), (key242, 2), (key264, -1), (key254, -1), (key308, -2), (key332, 1), (key322, 1), (key401, 1), (key391, 1), (key422, -1), (key412, -1)]

theorem rawRowCheck283 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form0 = rawRow283 := by decide +kernel

def row283 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck283 : row283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow283 := by decide +kernel

theorem rowEval283 (x : Key → ℝ) : Integer.Sparse.eval row283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck283, Integer.Sparse.eval_collectBalanced, rawRowCheck283]

def rawRow284 : Integer.Sparse Key := [(key332, -1), (key343, -1), (key333, 2), (key454, 1), (key478, 1), (key423, -1), (key462, -1), (key604, -2), (key586, 1), (key610, 1), (key264, 1), (key274, 1), (key265, -2), (key446, -1), (key472, -1), (key402, 1), (key462, 1), (key598, 2), (key575, -1), (key610, -1), (key254, -1), (key269, -1), (key244, 1), (key265, 1), (key322, 1), (key337, 1), (key310, -1), (key333, -1), (key580, -1), (key598, -1), (key570, 1), (key604, 1), (key254, 2), (key242, -1), (key264, -1), (key322, -2), (key308, 1), (key332, 1), (key412, 1), (key446, 1), (key391, -1), (key454, -1)]

theorem rawRowCheck284 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form0 = rawRow284 := by decide +kernel

def row284 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck284 : row284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow284 := by decide +kernel

theorem rowEval284 (x : Key → ℝ) : Integer.Sparse.eval row284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck284, Integer.Sparse.eval_collectBalanced, rawRowCheck284]

def rawRow285 : Integer.Sparse Key := [(key343, -1), (key332, -1), (key333, 2), (key478, 1), (key454, 1), (key462, -1), (key423, -1), (key604, -2), (key610, 1), (key586, 1), (key274, 1), (key264, 1), (key265, -2), (key472, -1), (key446, -1), (key462, 1), (key402, 1), (key598, 2), (key610, -1), (key575, -1), (key269, -1), (key254, -1), (key265, 1), (key244, 1), (key337, 1), (key322, 1), (key333, -1), (key310, -1), (key598, -1), (key580, -1), (key604, 1), (key570, 1), (key254, 2), (key264, -1), (key242, -1), (key322, -2), (key332, 1), (key308, 1), (key446, 1), (key412, 1), (key454, -1), (key391, -1)]

theorem rawRowCheck285 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form0 = rawRow285 := by decide +kernel

def row285 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck285 : row285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow285 := by decide +kernel

theorem rowEval285 (x : Key → ℝ) : Integer.Sparse.eval row285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck285, Integer.Sparse.eval_collectBalanced, rawRowCheck285]

def rawRow286 : Integer.Sparse Key := [(key422, -1), (key423, -1), (key586, 2), (key332, 1), (key333, 1), (key604, -1), (key610, -1), (key343, -2), (key478, 1), (key484, 1), (key401, 1), (key402, 1), (key575, -2), (key264, -1), (key265, -1), (key598, 1), (key610, 1), (key274, 2), (key472, -1), (key484, -1), (key308, -1), (key310, -1), (key570, 1), (key575, 1), (key242, 1), (key244, 1), (key580, -1), (key586, -1), (key269, -1), (key274, -1), (key337, 1), (key343, 1), (key308, 2), (key391, -1), (key401, -1), (key242, -2), (key412, 1), (key422, 1), (key254, 1), (key264, 1), (key322, -1), (key332, -1)]

theorem rawRowCheck286 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form0 = rawRow286 := by decide +kernel

def row286 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck286 : row286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow286 := by decide +kernel

theorem rowEval286 (x : Key → ℝ) : Integer.Sparse.eval row286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck286, Integer.Sparse.eval_collectBalanced, rawRowCheck286]

def rawRow287 : Integer.Sparse Key := [(key423, -1), (key422, -1), (key586, 2), (key333, 1), (key332, 1), (key610, -1), (key604, -1), (key343, -2), (key484, 1), (key478, 1), (key402, 1), (key401, 1), (key575, -2), (key265, -1), (key264, -1), (key610, 1), (key598, 1), (key274, 2), (key484, -1), (key472, -1), (key310, -1), (key308, -1), (key575, 1), (key570, 1), (key244, 1), (key242, 1), (key586, -1), (key580, -1), (key274, -1), (key269, -1), (key343, 1), (key337, 1), (key308, 2), (key401, -1), (key391, -1), (key242, -2), (key422, 1), (key412, 1), (key264, 1), (key254, 1), (key332, -1), (key322, -1)]

theorem rawRowCheck287 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form0 = rawRow287 := by decide +kernel

def row287 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck287 : row287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow287 := by decide +kernel

theorem rowEval287 (x : Key → ℝ) : Integer.Sparse.eval row287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck287, Integer.Sparse.eval_collectBalanced, rawRowCheck287]

end MUB6.Certificate.GramRows

end OAI

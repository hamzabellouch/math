import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10496 : Integer.Sparse Key := [(key1430, -6), (key1430, -6), (key1627, -6), (key1430, -6), (key1402, 2), (key1430, 2), (key1402, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1579, 2), (key1430, 2)]

theorem rawRowCheck10496 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form10 = rawRow10496 := by decide +kernel

def row10496 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

theorem rowCheck10496 : row10496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10496 := by decide +kernel

theorem rowEval10496 (x : Key → ℝ) : Integer.Sparse.eval row10496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10496, Integer.Sparse.eval_collectBalanced, rawRowCheck10496]

def rawRow10497 : Integer.Sparse Key := [(key1430, -6), (key1627, -6), (key1430, -6), (key1430, -6), (key1430, 2), (key1402, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1402, 2), (key1579, 2), (key1579, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1402, 2)]

theorem rawRowCheck10497 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form10 = rawRow10497 := by decide +kernel

def row10497 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

theorem rowCheck10497 : row10497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10497 := by decide +kernel

theorem rowEval10497 (x : Key → ℝ) : Integer.Sparse.eval row10497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10497, Integer.Sparse.eval_collectBalanced, rawRowCheck10497]

def rawRow10498 : Integer.Sparse Key := [(key1627, -6), (key1430, -6), (key1430, -6), (key1430, -6), (key1579, 2), (key1579, 2), (key1579, 2), (key1430, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1402, 2), (key1402, 2), (key1402, 2), (key1402, 2), (key1402, 2)]

theorem rawRowCheck10498 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form10 = rawRow10498 := by decide +kernel

def row10498 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

theorem rowCheck10498 : row10498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10498 := by decide +kernel

theorem rowEval10498 (x : Key → ℝ) : Integer.Sparse.eval row10498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10498, Integer.Sparse.eval_collectBalanced, rawRowCheck10498]

def rawRow10499 : Integer.Sparse Key := [(key2413, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2422, -6), (key2422, -6), (key2490, -6), (key2490, -6)]

theorem rawRowCheck10499 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form11 = rawRow10499 := by decide +kernel

def row10499 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

theorem rowCheck10499 : row10499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10499 := by decide +kernel

theorem rowEval10499 (x : Key → ℝ) : Integer.Sparse.eval row10499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10499, Integer.Sparse.eval_collectBalanced, rawRowCheck10499]

def rawRow10500 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2422, -6), (key2490, -6), (key2422, -6), (key2490, -6)]

theorem rawRowCheck10500 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form11 = rawRow10500 := by decide +kernel

def row10500 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

theorem rowCheck10500 : row10500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10500 := by decide +kernel

theorem rowEval10500 (x : Key → ℝ) : Integer.Sparse.eval row10500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10500, Integer.Sparse.eval_collectBalanced, rawRowCheck10500]

def rawRow10501 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2413, 6), (key2422, 6), (key2422, -6), (key2490, -6), (key2490, -6), (key2422, -6)]

theorem rawRowCheck10501 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form11 = rawRow10501 := by decide +kernel

def row10501 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

theorem rowCheck10501 : row10501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10501 := by decide +kernel

theorem rowEval10501 (x : Key → ℝ) : Integer.Sparse.eval row10501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10501, Integer.Sparse.eval_collectBalanced, rawRowCheck10501]

def rawRow10502 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2490, -6), (key2422, -6), (key2422, -6), (key2490, -6)]

theorem rawRowCheck10502 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form11 = rawRow10502 := by decide +kernel

def row10502 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

theorem rowCheck10502 : row10502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10502 := by decide +kernel

theorem rowEval10502 (x : Key → ℝ) : Integer.Sparse.eval row10502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10502, Integer.Sparse.eval_collectBalanced, rawRowCheck10502]

def rawRow10503 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, -6), (key2422, -6), (key2490, -6), (key2422, -6)]

theorem rawRowCheck10503 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form11 = rawRow10503 := by decide +kernel

def row10503 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

theorem rowCheck10503 : row10503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10503 := by decide +kernel

theorem rowEval10503 (x : Key → ℝ) : Integer.Sparse.eval row10503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10503, Integer.Sparse.eval_collectBalanced, rawRowCheck10503]

def rawRow10504 : Integer.Sparse Key := [(key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, -6), (key2490, -6), (key2422, -6), (key2422, -6)]

theorem rawRowCheck10504 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form11 = rawRow10504 := by decide +kernel

def row10504 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

theorem rowCheck10504 : row10504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10504 := by decide +kernel

theorem rowEval10504 (x : Key → ℝ) : Integer.Sparse.eval row10504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10504, Integer.Sparse.eval_collectBalanced, rawRowCheck10504]

def rawRow10505 : Integer.Sparse Key := [(key2486, 6), (key2490, 6), (key2490, 6), (key2490, 6), (key2413, -6), (key2413, -6), (key2413, -6), (key2486, -6)]

theorem rawRowCheck10505 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form11 = rawRow10505 := by decide +kernel

def row10505 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

theorem rowCheck10505 : row10505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10505 := by decide +kernel

theorem rowEval10505 (x : Key → ℝ) : Integer.Sparse.eval row10505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck10505, Integer.Sparse.eval_collectBalanced, rawRowCheck10505]

def rawRow10506 : Integer.Sparse Key := [(key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2413, -6), (key2413, -6), (key2486, -6), (key2413, -6)]

theorem rawRowCheck10506 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form11 = rawRow10506 := by decide +kernel

def row10506 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

theorem rowCheck10506 : row10506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10506 := by decide +kernel

theorem rowEval10506 (x : Key → ℝ) : Integer.Sparse.eval row10506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10506, Integer.Sparse.eval_collectBalanced, rawRowCheck10506]

def rawRow10507 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2413, -6), (key2486, -6), (key2413, -6), (key2413, -6)]

theorem rawRowCheck10507 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form11 = rawRow10507 := by decide +kernel

def row10507 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

theorem rowCheck10507 : row10507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10507 := by decide +kernel

theorem rowEval10507 (x : Key → ℝ) : Integer.Sparse.eval row10507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10507, Integer.Sparse.eval_collectBalanced, rawRowCheck10507]

def rawRow10508 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2490, 6), (key2486, 6), (key2486, -6), (key2413, -6), (key2413, -6), (key2413, -6)]

theorem rawRowCheck10508 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form11 = rawRow10508 := by decide +kernel

def row10508 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

theorem rowCheck10508 : row10508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10508 := by decide +kernel

theorem rowEval10508 (x : Key → ℝ) : Integer.Sparse.eval row10508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck10508, Integer.Sparse.eval_collectBalanced, rawRowCheck10508]

def rawRow10509 : Integer.Sparse Key := [(key2416, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2423, -6), (key2423, -6), (key2491, -6), (key2491, -6)]

theorem rawRowCheck10509 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form12 = rawRow10509 := by decide +kernel

def row10509 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

theorem rowCheck10509 : row10509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10509 := by decide +kernel

theorem rowEval10509 (x : Key → ℝ) : Integer.Sparse.eval row10509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10509, Integer.Sparse.eval_collectBalanced, rawRowCheck10509]

def rawRow10510 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2423, -6), (key2491, -6), (key2423, -6), (key2491, -6)]

theorem rawRowCheck10510 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form12 = rawRow10510 := by decide +kernel

def row10510 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

theorem rowCheck10510 : row10510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10510 := by decide +kernel

theorem rowEval10510 (x : Key → ℝ) : Integer.Sparse.eval row10510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10510, Integer.Sparse.eval_collectBalanced, rawRowCheck10510]

def rawRow10511 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2416, 6), (key2423, 6), (key2423, -6), (key2491, -6), (key2491, -6), (key2423, -6)]

theorem rawRowCheck10511 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form12 = rawRow10511 := by decide +kernel

def row10511 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

theorem rowCheck10511 : row10511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10511 := by decide +kernel

theorem rowEval10511 (x : Key → ℝ) : Integer.Sparse.eval row10511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10511, Integer.Sparse.eval_collectBalanced, rawRowCheck10511]

def rawRow10512 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2491, -6), (key2423, -6), (key2423, -6), (key2491, -6)]

theorem rawRowCheck10512 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form12 = rawRow10512 := by decide +kernel

def row10512 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

theorem rowCheck10512 : row10512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10512 := by decide +kernel

theorem rowEval10512 (x : Key → ℝ) : Integer.Sparse.eval row10512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10512, Integer.Sparse.eval_collectBalanced, rawRowCheck10512]

def rawRow10513 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, -6), (key2423, -6), (key2491, -6), (key2423, -6)]

theorem rawRowCheck10513 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form12 = rawRow10513 := by decide +kernel

def row10513 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

theorem rowCheck10513 : row10513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10513 := by decide +kernel

theorem rowEval10513 (x : Key → ℝ) : Integer.Sparse.eval row10513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10513, Integer.Sparse.eval_collectBalanced, rawRowCheck10513]

def rawRow10514 : Integer.Sparse Key := [(key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, -6), (key2491, -6), (key2423, -6), (key2423, -6)]

theorem rawRowCheck10514 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form12 = rawRow10514 := by decide +kernel

def row10514 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

theorem rowCheck10514 : row10514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10514 := by decide +kernel

theorem rowEval10514 (x : Key → ℝ) : Integer.Sparse.eval row10514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10514, Integer.Sparse.eval_collectBalanced, rawRowCheck10514]

def rawRow10515 : Integer.Sparse Key := [(key2489, 6), (key2491, 6), (key2491, 6), (key2491, 6), (key2416, -6), (key2416, -6), (key2416, -6), (key2489, -6)]

theorem rawRowCheck10515 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form12 = rawRow10515 := by decide +kernel

def row10515 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

theorem rowCheck10515 : row10515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10515 := by decide +kernel

theorem rowEval10515 (x : Key → ℝ) : Integer.Sparse.eval row10515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck10515, Integer.Sparse.eval_collectBalanced, rawRowCheck10515]

def rawRow10516 : Integer.Sparse Key := [(key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2416, -6), (key2416, -6), (key2489, -6), (key2416, -6)]

theorem rawRowCheck10516 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form12 = rawRow10516 := by decide +kernel

def row10516 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

theorem rowCheck10516 : row10516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10516 := by decide +kernel

theorem rowEval10516 (x : Key → ℝ) : Integer.Sparse.eval row10516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10516, Integer.Sparse.eval_collectBalanced, rawRowCheck10516]

def rawRow10517 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2416, -6), (key2489, -6), (key2416, -6), (key2416, -6)]

theorem rawRowCheck10517 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form12 = rawRow10517 := by decide +kernel

def row10517 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

theorem rowCheck10517 : row10517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10517 := by decide +kernel

theorem rowEval10517 (x : Key → ℝ) : Integer.Sparse.eval row10517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10517, Integer.Sparse.eval_collectBalanced, rawRowCheck10517]

def rawRow10518 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2491, 6), (key2489, 6), (key2489, -6), (key2416, -6), (key2416, -6), (key2416, -6)]

theorem rawRowCheck10518 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form12 = rawRow10518 := by decide +kernel

def row10518 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

theorem rowCheck10518 : row10518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10518 := by decide +kernel

theorem rowEval10518 (x : Key → ℝ) : Integer.Sparse.eval row10518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck10518, Integer.Sparse.eval_collectBalanced, rawRowCheck10518]

def rawRow10519 : Integer.Sparse Key := [(key2204, -6), (key2204, -6), (key2205, -6), (key2205, -6), (key2204, 2), (key2204, 2), (key2205, 2), (key2204, 2), (key2204, 2), (key2319, 2), (key2319, 2), (key2320, 2), (key2320, 2), (key2205, 2), (key2320, 2), (key2320, 2)]

theorem rawRowCheck10519 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form13 = rawRow10519 := by decide +kernel

def row10519 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

theorem rowCheck10519 : row10519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10519 := by decide +kernel

theorem rowEval10519 (x : Key → ℝ) : Integer.Sparse.eval row10519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10519, Integer.Sparse.eval_collectBalanced, rawRowCheck10519]

def rawRow10520 : Integer.Sparse Key := [(key2204, -6), (key2205, -6), (key2204, -6), (key2205, -6), (key2204, 2), (key2205, 2), (key2204, 2), (key2319, 2), (key2320, 2), (key2204, 2), (key2320, 2), (key2204, 2), (key2319, 2), (key2320, 2), (key2205, 2), (key2320, 2)]

theorem rawRowCheck10520 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form13 = rawRow10520 := by decide +kernel

def row10520 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

theorem rowCheck10520 : row10520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10520 := by decide +kernel

theorem rowEval10520 (x : Key → ℝ) : Integer.Sparse.eval row10520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10520, Integer.Sparse.eval_collectBalanced, rawRowCheck10520]

def rawRow10521 : Integer.Sparse Key := [(key2205, -6), (key2204, -6), (key2204, -6), (key2205, -6), (key2205, 2), (key2204, 2), (key2204, 2), (key2320, 2), (key2319, 2), (key2320, 2), (key2204, 2), (key2319, 2), (key2204, 2), (key2320, 2), (key2320, 2), (key2205, 2)]

theorem rawRowCheck10521 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form13 = rawRow10521 := by decide +kernel

def row10521 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

theorem rowCheck10521 : row10521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10521 := by decide +kernel

theorem rowEval10521 (x : Key → ℝ) : Integer.Sparse.eval row10521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10521, Integer.Sparse.eval_collectBalanced, rawRowCheck10521]

def rawRow10522 : Integer.Sparse Key := [(key2204, -6), (key2205, -6), (key2205, -6), (key2204, -6), (key2319, 2), (key2320, 2), (key2320, 2), (key2204, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2320, 2), (key2204, 2), (key2204, 2), (key2319, 2)]

theorem rawRowCheck10522 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form13 = rawRow10522 := by decide +kernel

def row10522 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

theorem rowCheck10522 : row10522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10522 := by decide +kernel

theorem rowEval10522 (x : Key → ℝ) : Integer.Sparse.eval row10522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10522, Integer.Sparse.eval_collectBalanced, rawRowCheck10522]

def rawRow10523 : Integer.Sparse Key := [(key2205, -6), (key2204, -6), (key2205, -6), (key2204, -6), (key2320, 2), (key2319, 2), (key2320, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2204, 2), (key2319, 2), (key2204, 2)]

theorem rawRowCheck10523 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form13 = rawRow10523 := by decide +kernel

def row10523 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

theorem rowCheck10523 : row10523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10523 := by decide +kernel

theorem rowEval10523 (x : Key → ℝ) : Integer.Sparse.eval row10523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10523, Integer.Sparse.eval_collectBalanced, rawRowCheck10523]

def rawRow10524 : Integer.Sparse Key := [(key2205, -6), (key2205, -6), (key2204, -6), (key2204, -6), (key2320, 2), (key2320, 2), (key2319, 2), (key2320, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2204, 2), (key2319, 2), (key2204, 2), (key2204, 2)]

theorem rawRowCheck10524 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form13 = rawRow10524 := by decide +kernel

def row10524 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

theorem rowCheck10524 : row10524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10524 := by decide +kernel

theorem rowEval10524 (x : Key → ℝ) : Integer.Sparse.eval row10524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10524, Integer.Sparse.eval_collectBalanced, rawRowCheck10524]

def rawRow10525 : Integer.Sparse Key := [(key2319, -6), (key2320, -6), (key2320, -6), (key2320, -6), (key2204, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2320, 2)]

theorem rawRowCheck10525 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form13 = rawRow10525 := by decide +kernel

def row10525 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

theorem rowCheck10525 : row10525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10525 := by decide +kernel

theorem rowEval10525 (x : Key → ℝ) : Integer.Sparse.eval row10525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck10525, Integer.Sparse.eval_collectBalanced, rawRowCheck10525]

def rawRow10526 : Integer.Sparse Key := [(key2320, -6), (key2319, -6), (key2320, -6), (key2320, -6), (key2205, 2), (key2204, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2320, 2), (key2205, 2)]

theorem rawRowCheck10526 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form13 = rawRow10526 := by decide +kernel

def row10526 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

theorem rowCheck10526 : row10526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10526 := by decide +kernel

theorem rowEval10526 (x : Key → ℝ) : Integer.Sparse.eval row10526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10526, Integer.Sparse.eval_collectBalanced, rawRowCheck10526]

def rawRow10527 : Integer.Sparse Key := [(key2320, -6), (key2320, -6), (key2319, -6), (key2320, -6), (key2205, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2205, 2)]

theorem rawRowCheck10527 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form13 = rawRow10527 := by decide +kernel

def row10527 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

theorem rowCheck10527 : row10527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10527 := by decide +kernel

theorem rowEval10527 (x : Key → ℝ) : Integer.Sparse.eval row10527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10527, Integer.Sparse.eval_collectBalanced, rawRowCheck10527]

def rawRow10528 : Integer.Sparse Key := [(key2320, -6), (key2320, -6), (key2320, -6), (key2319, -6), (key2320, 2), (key2320, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2205, 2), (key2205, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2204, 2), (key2204, 2)]

theorem rawRowCheck10528 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form13 = rawRow10528 := by decide +kernel

def row10528 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

theorem rowCheck10528 : row10528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10528 := by decide +kernel

theorem rowEval10528 (x : Key → ℝ) : Integer.Sparse.eval row10528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck10528, Integer.Sparse.eval_collectBalanced, rawRowCheck10528]

def rawRow10529 : Integer.Sparse Key := [(key1050, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1058, -6), (key1058, -6), (key1138, -6), (key1138, -6)]

theorem rawRowCheck10529 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form14 = rawRow10529 := by decide +kernel

def row10529 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

theorem rowCheck10529 : row10529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10529 := by decide +kernel

theorem rowEval10529 (x : Key → ℝ) : Integer.Sparse.eval row10529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10529, Integer.Sparse.eval_collectBalanced, rawRowCheck10529]

def rawRow10530 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1058, -6), (key1138, -6), (key1058, -6), (key1138, -6)]

theorem rawRowCheck10530 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form14 = rawRow10530 := by decide +kernel

def row10530 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

theorem rowCheck10530 : row10530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10530 := by decide +kernel

theorem rowEval10530 (x : Key → ℝ) : Integer.Sparse.eval row10530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10530, Integer.Sparse.eval_collectBalanced, rawRowCheck10530]

def rawRow10531 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1050, 6), (key1058, 6), (key1058, -6), (key1138, -6), (key1138, -6), (key1058, -6)]

theorem rawRowCheck10531 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form14 = rawRow10531 := by decide +kernel

def row10531 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

theorem rowCheck10531 : row10531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10531 := by decide +kernel

theorem rowEval10531 (x : Key → ℝ) : Integer.Sparse.eval row10531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10531, Integer.Sparse.eval_collectBalanced, rawRowCheck10531]

def rawRow10532 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1138, -6), (key1058, -6), (key1058, -6), (key1138, -6)]

theorem rawRowCheck10532 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form14 = rawRow10532 := by decide +kernel

def row10532 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

theorem rowCheck10532 : row10532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10532 := by decide +kernel

theorem rowEval10532 (x : Key → ℝ) : Integer.Sparse.eval row10532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10532, Integer.Sparse.eval_collectBalanced, rawRowCheck10532]

def rawRow10533 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, -6), (key1058, -6), (key1138, -6), (key1058, -6)]

theorem rawRowCheck10533 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form14 = rawRow10533 := by decide +kernel

def row10533 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

theorem rowCheck10533 : row10533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10533 := by decide +kernel

theorem rowEval10533 (x : Key → ℝ) : Integer.Sparse.eval row10533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10533, Integer.Sparse.eval_collectBalanced, rawRowCheck10533]

def rawRow10534 : Integer.Sparse Key := [(key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, -6), (key1138, -6), (key1058, -6), (key1058, -6)]

theorem rawRowCheck10534 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form14 = rawRow10534 := by decide +kernel

def row10534 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

theorem rowCheck10534 : row10534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10534 := by decide +kernel

theorem rowEval10534 (x : Key → ℝ) : Integer.Sparse.eval row10534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10534, Integer.Sparse.eval_collectBalanced, rawRowCheck10534]

def rawRow10535 : Integer.Sparse Key := [(key1136, 6), (key1138, 6), (key1138, 6), (key1138, 6), (key1050, -6), (key1050, -6), (key1050, -6), (key1136, -6)]

theorem rawRowCheck10535 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form14 = rawRow10535 := by decide +kernel

def row10535 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

theorem rowCheck10535 : row10535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10535 := by decide +kernel

theorem rowEval10535 (x : Key → ℝ) : Integer.Sparse.eval row10535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck10535, Integer.Sparse.eval_collectBalanced, rawRowCheck10535]

def rawRow10536 : Integer.Sparse Key := [(key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1050, -6), (key1050, -6), (key1136, -6), (key1050, -6)]

theorem rawRowCheck10536 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form14 = rawRow10536 := by decide +kernel

def row10536 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

theorem rowCheck10536 : row10536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10536 := by decide +kernel

theorem rowEval10536 (x : Key → ℝ) : Integer.Sparse.eval row10536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10536, Integer.Sparse.eval_collectBalanced, rawRowCheck10536]

def rawRow10537 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1050, -6), (key1136, -6), (key1050, -6), (key1050, -6)]

theorem rawRowCheck10537 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form14 = rawRow10537 := by decide +kernel

def row10537 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

theorem rowCheck10537 : row10537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10537 := by decide +kernel

theorem rowEval10537 (x : Key → ℝ) : Integer.Sparse.eval row10537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10537, Integer.Sparse.eval_collectBalanced, rawRowCheck10537]

def rawRow10538 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1138, 6), (key1136, 6), (key1136, -6), (key1050, -6), (key1050, -6), (key1050, -6)]

theorem rawRowCheck10538 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form14 = rawRow10538 := by decide +kernel

def row10538 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

theorem rowCheck10538 : row10538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10538 := by decide +kernel

theorem rowEval10538 (x : Key → ℝ) : Integer.Sparse.eval row10538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck10538, Integer.Sparse.eval_collectBalanced, rawRowCheck10538]

def rawRow10539 : Integer.Sparse Key := [(key2413, -6), (key2413, -6), (key2422, -6), (key2422, -6), (key2413, 2), (key2413, 2), (key2422, 2), (key2413, 2), (key2413, 2), (key2486, 2), (key2486, 2), (key2490, 2), (key2490, 2), (key2422, 2), (key2490, 2), (key2490, 2)]

theorem rawRowCheck10539 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form15 = rawRow10539 := by decide +kernel

def row10539 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

theorem rowCheck10539 : row10539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10539 := by decide +kernel

theorem rowEval10539 (x : Key → ℝ) : Integer.Sparse.eval row10539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10539, Integer.Sparse.eval_collectBalanced, rawRowCheck10539]

def rawRow10540 : Integer.Sparse Key := [(key2413, -6), (key2422, -6), (key2413, -6), (key2422, -6), (key2413, 2), (key2422, 2), (key2413, 2), (key2486, 2), (key2490, 2), (key2413, 2), (key2490, 2), (key2413, 2), (key2486, 2), (key2490, 2), (key2422, 2), (key2490, 2)]

theorem rawRowCheck10540 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form15 = rawRow10540 := by decide +kernel

def row10540 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

theorem rowCheck10540 : row10540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10540 := by decide +kernel

theorem rowEval10540 (x : Key → ℝ) : Integer.Sparse.eval row10540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10540, Integer.Sparse.eval_collectBalanced, rawRowCheck10540]

def rawRow10541 : Integer.Sparse Key := [(key2422, -6), (key2413, -6), (key2413, -6), (key2422, -6), (key2422, 2), (key2413, 2), (key2413, 2), (key2490, 2), (key2486, 2), (key2490, 2), (key2413, 2), (key2486, 2), (key2413, 2), (key2490, 2), (key2490, 2), (key2422, 2)]

theorem rawRowCheck10541 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form15 = rawRow10541 := by decide +kernel

def row10541 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

theorem rowCheck10541 : row10541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10541 := by decide +kernel

theorem rowEval10541 (x : Key → ℝ) : Integer.Sparse.eval row10541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10541, Integer.Sparse.eval_collectBalanced, rawRowCheck10541]

def rawRow10542 : Integer.Sparse Key := [(key2413, -6), (key2422, -6), (key2422, -6), (key2413, -6), (key2486, 2), (key2490, 2), (key2490, 2), (key2413, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2490, 2), (key2413, 2), (key2413, 2), (key2486, 2)]

theorem rawRowCheck10542 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form15 = rawRow10542 := by decide +kernel

def row10542 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

theorem rowCheck10542 : row10542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10542 := by decide +kernel

theorem rowEval10542 (x : Key → ℝ) : Integer.Sparse.eval row10542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10542, Integer.Sparse.eval_collectBalanced, rawRowCheck10542]

def rawRow10543 : Integer.Sparse Key := [(key2422, -6), (key2413, -6), (key2422, -6), (key2413, -6), (key2490, 2), (key2486, 2), (key2490, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2413, 2), (key2486, 2), (key2413, 2)]

theorem rawRowCheck10543 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form15 = rawRow10543 := by decide +kernel

def row10543 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

theorem rowCheck10543 : row10543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10543 := by decide +kernel

theorem rowEval10543 (x : Key → ℝ) : Integer.Sparse.eval row10543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10543, Integer.Sparse.eval_collectBalanced, rawRowCheck10543]

def rawRow10544 : Integer.Sparse Key := [(key2422, -6), (key2422, -6), (key2413, -6), (key2413, -6), (key2490, 2), (key2490, 2), (key2486, 2), (key2490, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2413, 2), (key2486, 2), (key2413, 2), (key2413, 2)]

theorem rawRowCheck10544 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form15 = rawRow10544 := by decide +kernel

def row10544 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

theorem rowCheck10544 : row10544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10544 := by decide +kernel

theorem rowEval10544 (x : Key → ℝ) : Integer.Sparse.eval row10544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10544, Integer.Sparse.eval_collectBalanced, rawRowCheck10544]

def rawRow10545 : Integer.Sparse Key := [(key2486, -6), (key2490, -6), (key2490, -6), (key2490, -6), (key2413, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2490, 2)]

theorem rawRowCheck10545 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form15 = rawRow10545 := by decide +kernel

def row10545 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

theorem rowCheck10545 : row10545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10545 := by decide +kernel

theorem rowEval10545 (x : Key → ℝ) : Integer.Sparse.eval row10545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck10545, Integer.Sparse.eval_collectBalanced, rawRowCheck10545]

def rawRow10546 : Integer.Sparse Key := [(key2490, -6), (key2486, -6), (key2490, -6), (key2490, -6), (key2422, 2), (key2413, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2490, 2), (key2422, 2)]

theorem rawRowCheck10546 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form15 = rawRow10546 := by decide +kernel

def row10546 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

theorem rowCheck10546 : row10546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10546 := by decide +kernel

theorem rowEval10546 (x : Key → ℝ) : Integer.Sparse.eval row10546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10546, Integer.Sparse.eval_collectBalanced, rawRowCheck10546]

def rawRow10547 : Integer.Sparse Key := [(key2490, -6), (key2490, -6), (key2486, -6), (key2490, -6), (key2422, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2422, 2)]

theorem rawRowCheck10547 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form15 = rawRow10547 := by decide +kernel

def row10547 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

theorem rowCheck10547 : row10547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10547 := by decide +kernel

theorem rowEval10547 (x : Key → ℝ) : Integer.Sparse.eval row10547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10547, Integer.Sparse.eval_collectBalanced, rawRowCheck10547]

def rawRow10548 : Integer.Sparse Key := [(key2490, -6), (key2490, -6), (key2490, -6), (key2486, -6), (key2490, 2), (key2490, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2422, 2), (key2422, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2413, 2), (key2413, 2)]

theorem rawRowCheck10548 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form15 = rawRow10548 := by decide +kernel

def row10548 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

theorem rowCheck10548 : row10548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10548 := by decide +kernel

theorem rowEval10548 (x : Key → ℝ) : Integer.Sparse.eval row10548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck10548, Integer.Sparse.eval_collectBalanced, rawRowCheck10548]

def rawRow10549 : Integer.Sparse Key := [(key2677, -6), (key2677, -6), (key2708, -6), (key2708, -6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6)]

theorem rawRowCheck10549 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form16 = rawRow10549 := by decide +kernel

def row10549 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key3045, 6), (key3094, 12)]

theorem rowCheck10549 : row10549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10549 := by decide +kernel

theorem rowEval10549 (x : Key → ℝ) : Integer.Sparse.eval row10549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10549, Integer.Sparse.eval_collectBalanced, rawRowCheck10549]

def rawRow10550 : Integer.Sparse Key := [(key2677, -6), (key2708, -6), (key2677, -6), (key2708, -6), (key2677, 6), (key3094, 6), (key3045, 6), (key3094, 6)]

theorem rawRowCheck10550 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form16 = rawRow10550 := by decide +kernel

def row10550 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key3045, 6), (key3094, 12)]

theorem rowCheck10550 : row10550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10550 := by decide +kernel

theorem rowEval10550 (x : Key → ℝ) : Integer.Sparse.eval row10550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10550, Integer.Sparse.eval_collectBalanced, rawRowCheck10550]

def rawRow10551 : Integer.Sparse Key := [(key2677, -6), (key2708, -6), (key2708, -6), (key2677, -6), (key2677, 6), (key3094, 6), (key3094, 6), (key3045, 6)]

theorem rawRowCheck10551 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form16 = rawRow10551 := by decide +kernel

def row10551 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key3045, 6), (key3094, 12)]

theorem rowCheck10551 : row10551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10551 := by decide +kernel

theorem rowEval10551 (x : Key → ℝ) : Integer.Sparse.eval row10551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10551, Integer.Sparse.eval_collectBalanced, rawRowCheck10551]

def rawRow10552 : Integer.Sparse Key := [(key2708, -6), (key2677, -6), (key2677, -6), (key2708, -6), (key2811, 6), (key2677, 6), (key3045, 6), (key3094, 6)]

theorem rawRowCheck10552 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form16 = rawRow10552 := by decide +kernel

def row10552 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key2811, 6), (key3045, 6), (key3094, 6)]

theorem rowCheck10552 : row10552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10552 := by decide +kernel

theorem rowEval10552 (x : Key → ℝ) : Integer.Sparse.eval row10552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10552, Integer.Sparse.eval_collectBalanced, rawRowCheck10552]

def rawRow10553 : Integer.Sparse Key := [(key2708, -6), (key2677, -6), (key2708, -6), (key2677, -6), (key2811, 6), (key2677, 6), (key3094, 6), (key3045, 6)]

theorem rawRowCheck10553 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form16 = rawRow10553 := by decide +kernel

def row10553 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key2811, 6), (key3045, 6), (key3094, 6)]

theorem rowCheck10553 : row10553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10553 := by decide +kernel

theorem rowEval10553 (x : Key → ℝ) : Integer.Sparse.eval row10553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10553, Integer.Sparse.eval_collectBalanced, rawRowCheck10553]

def rawRow10554 : Integer.Sparse Key := [(key2708, -6), (key2708, -6), (key2677, -6), (key2677, -6), (key2811, 6), (key2811, 6), (key2677, 6), (key3045, 6)]

theorem rawRowCheck10554 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form16 = rawRow10554 := by decide +kernel

def row10554 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key2811, 12), (key3045, 6)]

theorem rowCheck10554 : row10554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10554 := by decide +kernel

theorem rowEval10554 (x : Key → ℝ) : Integer.Sparse.eval row10554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10554, Integer.Sparse.eval_collectBalanced, rawRowCheck10554]

def rawRow10555 : Integer.Sparse Key := [(key2811, -6), (key2811, -6), (key2811, -6), (key2861, -6), (key2708, 6), (key2708, 6), (key2708, 6), (key2861, 6)]

theorem rawRowCheck10555 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form16 = rawRow10555 := by decide +kernel

def row10555 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

theorem rowCheck10555 : row10555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10555 := by decide +kernel

theorem rowEval10555 (x : Key → ℝ) : Integer.Sparse.eval row10555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck10555, Integer.Sparse.eval_collectBalanced, rawRowCheck10555]

def rawRow10556 : Integer.Sparse Key := [(key2811, -6), (key2811, -6), (key2861, -6), (key2811, -6), (key2708, 6), (key2708, 6), (key2861, 6), (key2708, 6)]

theorem rawRowCheck10556 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form16 = rawRow10556 := by decide +kernel

def row10556 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

theorem rowCheck10556 : row10556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10556 := by decide +kernel

theorem rowEval10556 (x : Key → ℝ) : Integer.Sparse.eval row10556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10556, Integer.Sparse.eval_collectBalanced, rawRowCheck10556]

def rawRow10557 : Integer.Sparse Key := [(key2811, -6), (key2861, -6), (key2811, -6), (key2811, -6), (key2708, 6), (key2861, 6), (key2708, 6), (key2708, 6)]

theorem rawRowCheck10557 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form16 = rawRow10557 := by decide +kernel

def row10557 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

theorem rowCheck10557 : row10557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10557 := by decide +kernel

theorem rowEval10557 (x : Key → ℝ) : Integer.Sparse.eval row10557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10557, Integer.Sparse.eval_collectBalanced, rawRowCheck10557]

def rawRow10558 : Integer.Sparse Key := [(key2861, -6), (key2811, -6), (key2811, -6), (key2811, -6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6)]

theorem rawRowCheck10558 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form16 = rawRow10558 := by decide +kernel

def row10558 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

theorem rowCheck10558 : row10558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10558 := by decide +kernel

theorem rowEval10558 (x : Key → ℝ) : Integer.Sparse.eval row10558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck10558, Integer.Sparse.eval_collectBalanced, rawRowCheck10558]

def rawRow10559 : Integer.Sparse Key := [(key2685, -2), (key2692, -2), (key2692, -2), (key2685, -2), (key2821, -2), (key2821, -2), (key2692, -2), (key2692, -2), (key2821, -2), (key2821, -2), (key2830, -2), (key2830, -2), (key2685, 2), (key2718, 2), (key2718, 2), (key2685, 2), (key2821, 2), (key2821, 2), (key2718, 2), (key2718, 2), (key2821, 2), (key2821, 2), (key2871, 2), (key2871, 2)]

theorem rawRowCheck10559 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form17 = rawRow10559 := by decide +kernel

def row10559 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

theorem rowCheck10559 : row10559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10559 := by decide +kernel

theorem rowEval10559 (x : Key → ℝ) : Integer.Sparse.eval row10559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10559, Integer.Sparse.eval_collectBalanced, rawRowCheck10559]

def rawRow10560 : Integer.Sparse Key := [(key2692, -2), (key2685, -2), (key2692, -2), (key2821, -2), (key2685, -2), (key2821, -2), (key2821, -2), (key2830, -2), (key2692, -2), (key2830, -2), (key2692, -2), (key2821, -2), (key2718, 2), (key2685, 2), (key2718, 2), (key2821, 2), (key2685, 2), (key2821, 2), (key2821, 2), (key2871, 2), (key2718, 2), (key2871, 2), (key2718, 2), (key2821, 2)]

theorem rawRowCheck10560 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form17 = rawRow10560 := by decide +kernel

def row10560 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

theorem rowCheck10560 : row10560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10560 := by decide +kernel

theorem rowEval10560 (x : Key → ℝ) : Integer.Sparse.eval row10560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10560, Integer.Sparse.eval_collectBalanced, rawRowCheck10560]

def rawRow10561 : Integer.Sparse Key := [(key2692, -2), (key2692, -2), (key2685, -2), (key2821, -2), (key2821, -2), (key2685, -2), (key2830, -2), (key2821, -2), (key2830, -2), (key2692, -2), (key2821, -2), (key2692, -2), (key2718, 2), (key2718, 2), (key2685, 2), (key2821, 2), (key2821, 2), (key2685, 2), (key2871, 2), (key2821, 2), (key2871, 2), (key2718, 2), (key2821, 2), (key2718, 2)]

theorem rawRowCheck10561 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form17 = rawRow10561 := by decide +kernel

def row10561 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

theorem rowCheck10561 : row10561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10561 := by decide +kernel

theorem rowEval10561 (x : Key → ℝ) : Integer.Sparse.eval row10561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10561, Integer.Sparse.eval_collectBalanced, rawRowCheck10561]

def rawRow10562 : Integer.Sparse Key := [(key2821, -2), (key2821, -2), (key2830, -2), (key2692, -2), (key2692, -2), (key2830, -2), (key2685, -2), (key2692, -2), (key2685, -2), (key2821, -2), (key2692, -2), (key2821, -2), (key2821, 2), (key2821, 2), (key2871, 2), (key2718, 2), (key2718, 2), (key2871, 2), (key2685, 2), (key2718, 2), (key2685, 2), (key2821, 2), (key2718, 2), (key2821, 2)]

theorem rawRowCheck10562 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form17 = rawRow10562 := by decide +kernel

def row10562 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

theorem rowCheck10562 : row10562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10562 := by decide +kernel

theorem rowEval10562 (x : Key → ℝ) : Integer.Sparse.eval row10562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10562, Integer.Sparse.eval_collectBalanced, rawRowCheck10562]

def rawRow10563 : Integer.Sparse Key := [(key2821, -2), (key2830, -2), (key2821, -2), (key2692, -2), (key2830, -2), (key2692, -2), (key2692, -2), (key2685, -2), (key2821, -2), (key2685, -2), (key2821, -2), (key2692, -2), (key2821, 2), (key2871, 2), (key2821, 2), (key2718, 2), (key2871, 2), (key2718, 2), (key2718, 2), (key2685, 2), (key2821, 2), (key2685, 2), (key2821, 2), (key2718, 2)]

theorem rawRowCheck10563 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form17 = rawRow10563 := by decide +kernel

def row10563 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

theorem rowCheck10563 : row10563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10563 := by decide +kernel

theorem rowEval10563 (x : Key → ℝ) : Integer.Sparse.eval row10563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10563, Integer.Sparse.eval_collectBalanced, rawRowCheck10563]

def rawRow10564 : Integer.Sparse Key := [(key2830, -2), (key2821, -2), (key2821, -2), (key2830, -2), (key2692, -2), (key2692, -2), (key2821, -2), (key2821, -2), (key2692, -2), (key2692, -2), (key2685, -2), (key2685, -2), (key2871, 2), (key2821, 2), (key2821, 2), (key2871, 2), (key2718, 2), (key2718, 2), (key2821, 2), (key2821, 2), (key2718, 2), (key2718, 2), (key2685, 2), (key2685, 2)]

theorem rawRowCheck10564 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form17 = rawRow10564 := by decide +kernel

def row10564 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

theorem rowCheck10564 : row10564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10564 := by decide +kernel

theorem rowEval10564 (x : Key → ℝ) : Integer.Sparse.eval row10564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10564, Integer.Sparse.eval_collectBalanced, rawRowCheck10564]

def rawRow10565 : Integer.Sparse Key := [(key2718, -2), (key2718, -2), (key2727, -2), (key2718, -2), (key2718, -2), (key2871, -2), (key2718, -2), (key2727, -2), (key2718, -2), (key2871, -2), (key2727, -2), (key2871, -2), (key2692, 2), (key2692, 2), (key2727, 2), (key2692, 2), (key2692, 2), (key2830, 2), (key2692, 2), (key2727, 2), (key2692, 2), (key2830, 2), (key2727, 2), (key2830, 2)]

theorem rawRowCheck10565 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form17 = rawRow10565 := by decide +kernel

def row10565 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

theorem rowCheck10565 : row10565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10565 := by decide +kernel

theorem rowEval10565 (x : Key → ℝ) : Integer.Sparse.eval row10565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck10565, Integer.Sparse.eval_collectBalanced, rawRowCheck10565]

def rawRow10566 : Integer.Sparse Key := [(key2718, -2), (key2727, -2), (key2718, -2), (key2718, -2), (key2871, -2), (key2718, -2), (key2727, -2), (key2718, -2), (key2871, -2), (key2718, -2), (key2871, -2), (key2727, -2), (key2692, 2), (key2727, 2), (key2692, 2), (key2692, 2), (key2830, 2), (key2692, 2), (key2727, 2), (key2692, 2), (key2830, 2), (key2692, 2), (key2830, 2), (key2727, 2)]

theorem rawRowCheck10566 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form17 = rawRow10566 := by decide +kernel

def row10566 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

theorem rowCheck10566 : row10566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10566 := by decide +kernel

theorem rowEval10566 (x : Key → ℝ) : Integer.Sparse.eval row10566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10566, Integer.Sparse.eval_collectBalanced, rawRowCheck10566]

def rawRow10567 : Integer.Sparse Key := [(key2727, -2), (key2718, -2), (key2718, -2), (key2871, -2), (key2718, -2), (key2718, -2), (key2871, -2), (key2871, -2), (key2727, -2), (key2727, -2), (key2718, -2), (key2718, -2), (key2727, 2), (key2692, 2), (key2692, 2), (key2830, 2), (key2692, 2), (key2692, 2), (key2830, 2), (key2830, 2), (key2727, 2), (key2727, 2), (key2692, 2), (key2692, 2)]

theorem rawRowCheck10567 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form17 = rawRow10567 := by decide +kernel

def row10567 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

theorem rowCheck10567 : row10567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10567 := by decide +kernel

theorem rowEval10567 (x : Key → ℝ) : Integer.Sparse.eval row10567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10567, Integer.Sparse.eval_collectBalanced, rawRowCheck10567]

def rawRow10568 : Integer.Sparse Key := [(key2871, -2), (key2871, -2), (key2871, -2), (key2727, -2), (key2727, -2), (key2727, -2), (key2718, -2), (key2718, -2), (key2718, -2), (key2718, -2), (key2718, -2), (key2718, -2), (key2830, 2), (key2830, 2), (key2830, 2), (key2727, 2), (key2727, 2), (key2727, 2), (key2692, 2), (key2692, 2), (key2692, 2), (key2692, 2), (key2692, 2), (key2692, 2)]

theorem rawRowCheck10568 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form17 = rawRow10568 := by decide +kernel

def row10568 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

theorem rowCheck10568 : row10568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10568 := by decide +kernel

theorem rowEval10568 (x : Key → ℝ) : Integer.Sparse.eval row10568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form17) x := by
  rw [rowCheck10568, Integer.Sparse.eval_collectBalanced, rawRowCheck10568]

def rawRow10569 : Integer.Sparse Key := [(key1055, 2), (key1063, 2), (key1063, 2), (key1055, 2), (key1143, 2), (key1143, 2), (key1063, 2), (key1063, 2), (key1143, 2), (key1143, 2), (key1153, 2), (key1153, 2), (key1063, -2), (key1063, -2), (key1074, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1153, -2), (key1153, -2), (key1074, -2), (key1153, -2), (key1153, -2)]

theorem rawRowCheck10569 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form18 = rawRow10569 := by decide +kernel

def row10569 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

theorem rowCheck10569 : row10569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10569 := by decide +kernel

theorem rowEval10569 (x : Key → ℝ) : Integer.Sparse.eval row10569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10569, Integer.Sparse.eval_collectBalanced, rawRowCheck10569]

def rawRow10570 : Integer.Sparse Key := [(key1063, 2), (key1055, 2), (key1063, 2), (key1143, 2), (key1055, 2), (key1143, 2), (key1143, 2), (key1153, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1143, 2), (key1063, -2), (key1074, -2), (key1063, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1153, -2), (key1074, -2), (key1153, -2)]

theorem rawRowCheck10570 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form18 = rawRow10570 := by decide +kernel

def row10570 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

theorem rowCheck10570 : row10570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10570 := by decide +kernel

theorem rowEval10570 (x : Key → ℝ) : Integer.Sparse.eval row10570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10570, Integer.Sparse.eval_collectBalanced, rawRowCheck10570]

def rawRow10571 : Integer.Sparse Key := [(key1063, 2), (key1063, 2), (key1055, 2), (key1143, 2), (key1143, 2), (key1055, 2), (key1153, 2), (key1143, 2), (key1153, 2), (key1063, 2), (key1143, 2), (key1063, 2), (key1074, -2), (key1063, -2), (key1063, -2), (key1153, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1153, -2), (key1153, -2), (key1074, -2)]

theorem rawRowCheck10571 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form18 = rawRow10571 := by decide +kernel

def row10571 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

theorem rowCheck10571 : row10571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10571 := by decide +kernel

theorem rowEval10571 (x : Key → ℝ) : Integer.Sparse.eval row10571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10571, Integer.Sparse.eval_collectBalanced, rawRowCheck10571]

def rawRow10572 : Integer.Sparse Key := [(key1143, 2), (key1143, 2), (key1153, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1055, 2), (key1063, 2), (key1055, 2), (key1143, 2), (key1063, 2), (key1143, 2), (key1143, -2), (key1153, -2), (key1153, -2), (key1063, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1153, -2), (key1063, -2), (key1063, -2), (key1143, -2)]

theorem rawRowCheck10572 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form18 = rawRow10572 := by decide +kernel

def row10572 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

theorem rowCheck10572 : row10572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10572 := by decide +kernel

theorem rowEval10572 (x : Key → ℝ) : Integer.Sparse.eval row10572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10572, Integer.Sparse.eval_collectBalanced, rawRowCheck10572]

def rawRow10573 : Integer.Sparse Key := [(key1143, 2), (key1153, 2), (key1143, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1063, 2), (key1055, 2), (key1143, 2), (key1055, 2), (key1143, 2), (key1063, 2), (key1153, -2), (key1143, -2), (key1153, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1063, -2), (key1143, -2), (key1063, -2)]

theorem rawRowCheck10573 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form18 = rawRow10573 := by decide +kernel

def row10573 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

theorem rowCheck10573 : row10573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10573 := by decide +kernel

theorem rowEval10573 (x : Key → ℝ) : Integer.Sparse.eval row10573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10573, Integer.Sparse.eval_collectBalanced, rawRowCheck10573]

def rawRow10574 : Integer.Sparse Key := [(key1153, 2), (key1143, 2), (key1143, 2), (key1153, 2), (key1063, 2), (key1063, 2), (key1143, 2), (key1143, 2), (key1063, 2), (key1063, 2), (key1055, 2), (key1055, 2), (key1153, -2), (key1153, -2), (key1143, -2), (key1153, -2), (key1153, -2), (key1074, -2), (key1074, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1063, -2)]

theorem rawRowCheck10574 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form18 = rawRow10574 := by decide +kernel

def row10574 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

theorem rowCheck10574 : row10574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10574 := by decide +kernel

theorem rowEval10574 (x : Key → ℝ) : Integer.Sparse.eval row10574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10574, Integer.Sparse.eval_collectBalanced, rawRowCheck10574]

def rawRow10575 : Integer.Sparse Key := [(key1063, 2), (key1063, 2), (key1074, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1074, 2), (key1063, 2), (key1153, 2), (key1074, 2), (key1153, 2), (key1055, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1143, -2)]

theorem rawRowCheck10575 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form18 = rawRow10575 := by decide +kernel

def row10575 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

theorem rowCheck10575 : row10575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10575 := by decide +kernel

theorem rowEval10575 (x : Key → ℝ) : Integer.Sparse.eval row10575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10575, Integer.Sparse.eval_collectBalanced, rawRowCheck10575]

def rawRow10576 : Integer.Sparse Key := [(key1063, 2), (key1074, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1074, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1153, 2), (key1074, 2), (key1063, -2), (key1055, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1063, -2)]

theorem rawRowCheck10576 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form18 = rawRow10576 := by decide +kernel

def row10576 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

theorem rowCheck10576 : row10576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10576 := by decide +kernel

theorem rowEval10576 (x : Key → ℝ) : Integer.Sparse.eval row10576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10576, Integer.Sparse.eval_collectBalanced, rawRowCheck10576]

def rawRow10577 : Integer.Sparse Key := [(key1074, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1153, 2), (key1074, 2), (key1074, 2), (key1063, 2), (key1063, 2), (key1063, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1063, -2)]

theorem rawRowCheck10577 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form18 = rawRow10577 := by decide +kernel

def row10577 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

theorem rowCheck10577 : row10577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10577 := by decide +kernel

theorem rowEval10577 (x : Key → ℝ) : Integer.Sparse.eval row10577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10577, Integer.Sparse.eval_collectBalanced, rawRowCheck10577]

def rawRow10578 : Integer.Sparse Key := [(key1153, 2), (key1153, 2), (key1153, 2), (key1074, 2), (key1074, 2), (key1074, 2), (key1063, 2), (key1063, 2), (key1063, 2), (key1063, 2), (key1063, 2), (key1063, 2), (key1143, -2), (key1143, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1055, -2), (key1055, -2)]

theorem rawRowCheck10578 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form18 = rawRow10578 := by decide +kernel

def row10578 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

theorem rowCheck10578 : row10578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10578 := by decide +kernel

theorem rowEval10578 (x : Key → ℝ) : Integer.Sparse.eval row10578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10578, Integer.Sparse.eval_collectBalanced, rawRowCheck10578]

def rawRow10579 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, 6), (key3084, 6), (key3099, 6), (key3099, 6)]

theorem rawRowCheck10579 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form19 = rawRow10579 := by decide +kernel

def row10579 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

theorem rowCheck10579 : row10579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10579 := by decide +kernel

theorem rowEval10579 (x : Key → ℝ) : Integer.Sparse.eval row10579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10579, Integer.Sparse.eval_collectBalanced, rawRowCheck10579]

def rawRow10580 : Integer.Sparse Key := [(key3084, -4), (key3079, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3084, 6), (key3099, 6), (key3084, 6), (key3099, 6)]

theorem rawRowCheck10580 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form19 = rawRow10580 := by decide +kernel

def row10580 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

theorem rowCheck10580 : row10580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10580 := by decide +kernel

theorem rowEval10580 (x : Key → ℝ) : Integer.Sparse.eval row10580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10580, Integer.Sparse.eval_collectBalanced, rawRowCheck10580]

def rawRow10581 : Integer.Sparse Key := [(key3084, -4), (key3084, -4), (key3079, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, 6), (key3084, 6), (key3084, 6), (key3099, 6)]

theorem rawRowCheck10581 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form19 = rawRow10581 := by decide +kernel

def row10581 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

theorem rowCheck10581 : row10581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10581 := by decide +kernel

theorem rowEval10581 (x : Key → ℝ) : Integer.Sparse.eval row10581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10581, Integer.Sparse.eval_collectBalanced, rawRowCheck10581]

def rawRow10582 : Integer.Sparse Key := [(key3084, -4), (key3084, -4), (key3099, -4), (key3079, -4), (key3084, -4), (key3084, -4), (key3084, 6), (key3099, 6), (key3099, 6), (key3084, 6)]

theorem rawRowCheck10582 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form19 = rawRow10582 := by decide +kernel

def row10582 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

theorem rowCheck10582 : row10582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10582 := by decide +kernel

theorem rowEval10582 (x : Key → ℝ) : Integer.Sparse.eval row10582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10582, Integer.Sparse.eval_collectBalanced, rawRowCheck10582]

def rawRow10583 : Integer.Sparse Key := [(key3084, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3079, -4), (key3084, -4), (key3099, 6), (key3084, 6), (key3099, 6), (key3084, 6)]

theorem rawRowCheck10583 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form19 = rawRow10583 := by decide +kernel

def row10583 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

theorem rowCheck10583 : row10583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10583 := by decide +kernel

theorem rowEval10583 (x : Key → ℝ) : Integer.Sparse.eval row10583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10583, Integer.Sparse.eval_collectBalanced, rawRowCheck10583]

def rawRow10584 : Integer.Sparse Key := [(key3099, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3079, -4), (key3099, 6), (key3099, 6), (key3084, 6), (key3084, 6)]

theorem rawRowCheck10584 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form19 = rawRow10584 := by decide +kernel

def row10584 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

theorem rowCheck10584 : row10584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10584 := by decide +kernel

theorem rowEval10584 (x : Key → ℝ) : Integer.Sparse.eval row10584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10584, Integer.Sparse.eval_collectBalanced, rawRowCheck10584]

def rawRow10585 : Integer.Sparse Key := [(key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3099, -4), (key3099, -4), (key3079, 6), (key3084, 6), (key3084, 6), (key3084, 6)]

theorem rawRowCheck10585 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form19 = rawRow10585 := by decide +kernel

def row10585 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

theorem rowCheck10585 : row10585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10585 := by decide +kernel

theorem rowEval10585 (x : Key → ℝ) : Integer.Sparse.eval row10585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck10585, Integer.Sparse.eval_collectBalanced, rawRowCheck10585]

def rawRow10586 : Integer.Sparse Key := [(key3084, -4), (key3099, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3099, -4), (key3084, 6), (key3079, 6), (key3084, 6), (key3084, 6)]

theorem rawRowCheck10586 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form19 = rawRow10586 := by decide +kernel

def row10586 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

theorem rowCheck10586 : row10586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10586 := by decide +kernel

theorem rowEval10586 (x : Key → ℝ) : Integer.Sparse.eval row10586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10586, Integer.Sparse.eval_collectBalanced, rawRowCheck10586]

def rawRow10587 : Integer.Sparse Key := [(key3099, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3099, -4), (key3084, -4), (key3084, 6), (key3084, 6), (key3079, 6), (key3084, 6)]

theorem rawRowCheck10587 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form19 = rawRow10587 := by decide +kernel

def row10587 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

theorem rowCheck10587 : row10587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10587 := by decide +kernel

theorem rowEval10587 (x : Key → ℝ) : Integer.Sparse.eval row10587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10587, Integer.Sparse.eval_collectBalanced, rawRowCheck10587]

def rawRow10588 : Integer.Sparse Key := [(key3099, -4), (key3099, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, 6), (key3084, 6), (key3084, 6), (key3079, 6)]

theorem rawRowCheck10588 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form19 = rawRow10588 := by decide +kernel

def row10588 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

theorem rowCheck10588 : row10588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10588 := by decide +kernel

theorem rowEval10588 (x : Key → ℝ) : Integer.Sparse.eval row10588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form19) x := by
  rw [rowCheck10588, Integer.Sparse.eval_collectBalanced, rawRowCheck10588]

def rawRow10589 : Integer.Sparse Key := [(key1851, 2), (key1851, 2), (key1855, 2), (key1851, 2), (key1851, 2), (key1886, 2), (key1851, 2), (key1855, 2), (key1851, 2), (key1886, 2), (key1855, 2), (key1886, 2), (key1851, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1886, -2)]

theorem rawRowCheck10589 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow10589 := by decide +kernel

def row10589 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

theorem rowCheck10589 : row10589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10589 := by decide +kernel

theorem rowEval10589 (x : Key → ℝ) : Integer.Sparse.eval row10589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck10589, Integer.Sparse.eval_collectBalanced, rawRowCheck10589]

def rawRow10590 : Integer.Sparse Key := [(key1851, 2), (key1855, 2), (key1851, 2), (key1851, 2), (key1886, 2), (key1851, 2), (key1855, 2), (key1851, 2), (key1886, 2), (key1851, 2), (key1886, 2), (key1855, 2), (key1855, -2), (key1851, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1886, -2), (key1855, -2)]

theorem rawRowCheck10590 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow10590 := by decide +kernel

def row10590 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

theorem rowCheck10590 : row10590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10590 := by decide +kernel

theorem rowEval10590 (x : Key → ℝ) : Integer.Sparse.eval row10590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10590, Integer.Sparse.eval_collectBalanced, rawRowCheck10590]

def rawRow10591 : Integer.Sparse Key := [(key1855, 2), (key1851, 2), (key1851, 2), (key1886, 2), (key1851, 2), (key1851, 2), (key1886, 2), (key1886, 2), (key1855, 2), (key1855, 2), (key1851, 2), (key1851, 2), (key1855, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1855, -2)]

theorem rawRowCheck10591 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow10591 := by decide +kernel

def row10591 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

theorem rowCheck10591 : row10591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10591 := by decide +kernel

theorem rowEval10591 (x : Key → ℝ) : Integer.Sparse.eval row10591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10591, Integer.Sparse.eval_collectBalanced, rawRowCheck10591]

def rawRow10592 : Integer.Sparse Key := [(key1886, 2), (key1886, 2), (key1886, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1886, -2), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1851, -2)]

theorem rawRowCheck10592 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow10592 := by decide +kernel

def row10592 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

theorem rowCheck10592 : row10592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10592 := by decide +kernel

theorem rowEval10592 (x : Key → ℝ) : Integer.Sparse.eval row10592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10592, Integer.Sparse.eval_collectBalanced, rawRowCheck10592]

def rawRow10593 : Integer.Sparse Key := [(key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2)]

theorem rawRowCheck10593 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow10593 := by decide +kernel

def row10593 : Integer.Sparse Key := [(key1851, -24), (key1855, 24)]

theorem rowCheck10593 : row10593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10593 := by decide +kernel

theorem rowEval10593 (x : Key → ℝ) : Integer.Sparse.eval row10593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10593, Integer.Sparse.eval_collectBalanced, rawRowCheck10593]

def rawRow10594 : Integer.Sparse Key := [(key685, -24), (key685, 6), (key685, 6), (key685, 6), (key692, 6)]

theorem rawRowCheck10594 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow10594 := by decide +kernel

def row10594 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

theorem rowCheck10594 : row10594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10594 := by decide +kernel

theorem rowEval10594 (x : Key → ℝ) : Integer.Sparse.eval row10594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck10594, Integer.Sparse.eval_collectBalanced, rawRowCheck10594]

def rawRow10595 : Integer.Sparse Key := [(key685, -24), (key685, 6), (key685, 6), (key692, 6), (key685, 6)]

theorem rawRowCheck10595 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow10595 := by decide +kernel

def row10595 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

theorem rowCheck10595 : row10595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10595 := by decide +kernel

theorem rowEval10595 (x : Key → ℝ) : Integer.Sparse.eval row10595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10595, Integer.Sparse.eval_collectBalanced, rawRowCheck10595]

def rawRow10596 : Integer.Sparse Key := [(key685, -24), (key685, 6), (key692, 6), (key685, 6), (key685, 6)]

theorem rawRowCheck10596 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow10596 := by decide +kernel

def row10596 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

theorem rowCheck10596 : row10596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10596 := by decide +kernel

theorem rowEval10596 (x : Key → ℝ) : Integer.Sparse.eval row10596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10596, Integer.Sparse.eval_collectBalanced, rawRowCheck10596]

def rawRow10597 : Integer.Sparse Key := [(key685, -24), (key692, 6), (key685, 6), (key685, 6), (key685, 6)]

theorem rawRowCheck10597 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow10597 := by decide +kernel

def row10597 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

theorem rowCheck10597 : row10597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10597 := by decide +kernel

theorem rowEval10597 (x : Key → ℝ) : Integer.Sparse.eval row10597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10597, Integer.Sparse.eval_collectBalanced, rawRowCheck10597]

def rawRow10598 : Integer.Sparse Key := [(key692, -24), (key685, 6), (key685, 6), (key685, 6), (key685, 6)]

theorem rawRowCheck10598 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow10598 := by decide +kernel

def row10598 : Integer.Sparse Key := [(key685, 24), (key692, -24)]

theorem rowCheck10598 : row10598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10598 := by decide +kernel

theorem rowEval10598 (x : Key → ℝ) : Integer.Sparse.eval row10598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10598, Integer.Sparse.eval_collectBalanced, rawRowCheck10598]

def rawRow10599 : Integer.Sparse Key := [(key617, -6), (key619, -6), (key619, -6), (key619, -6), (key617, 2), (key619, 2), (key619, 2), (key617, 2), (key619, 2), (key617, 2), (key645, 2), (key619, 2), (key645, 2), (key619, 2), (key619, 2), (key645, 2)]

theorem rawRowCheck10599 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow10599 := by decide +kernel

def row10599 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

theorem rowCheck10599 : row10599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10599 := by decide +kernel

theorem rowEval10599 (x : Key → ℝ) : Integer.Sparse.eval row10599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck10599, Integer.Sparse.eval_collectBalanced, rawRowCheck10599]

def rawRow10600 : Integer.Sparse Key := [(key619, -6), (key617, -6), (key619, -6), (key619, -6), (key619, 2), (key617, 2), (key619, 2), (key619, 2), (key617, 2), (key645, 2), (key617, 2), (key645, 2), (key619, 2), (key619, 2), (key645, 2), (key619, 2)]

theorem rawRowCheck10600 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow10600 := by decide +kernel

def row10600 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

theorem rowCheck10600 : row10600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10600 := by decide +kernel

theorem rowEval10600 (x : Key → ℝ) : Integer.Sparse.eval row10600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10600, Integer.Sparse.eval_collectBalanced, rawRowCheck10600]

def rawRow10601 : Integer.Sparse Key := [(key619, -6), (key619, -6), (key617, -6), (key619, -6), (key619, 2), (key619, 2), (key617, 2), (key645, 2), (key645, 2), (key619, 2), (key619, 2), (key617, 2), (key617, 2), (key645, 2), (key619, 2), (key619, 2)]

theorem rawRowCheck10601 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow10601 := by decide +kernel

def row10601 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

theorem rowCheck10601 : row10601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10601 := by decide +kernel

theorem rowEval10601 (x : Key → ℝ) : Integer.Sparse.eval row10601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10601, Integer.Sparse.eval_collectBalanced, rawRowCheck10601]

def rawRow10602 : Integer.Sparse Key := [(key619, -6), (key619, -6), (key619, -6), (key617, -6), (key645, 2), (key645, 2), (key645, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key617, 2), (key617, 2), (key617, 2)]

theorem rawRowCheck10602 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow10602 := by decide +kernel

def row10602 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

theorem rowCheck10602 : row10602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10602 := by decide +kernel

theorem rowEval10602 (x : Key → ℝ) : Integer.Sparse.eval row10602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10602, Integer.Sparse.eval_collectBalanced, rawRowCheck10602]

def rawRow10603 : Integer.Sparse Key := [(key645, -6), (key645, -6), (key645, -6), (key645, -6), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2)]

theorem rawRowCheck10603 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form2 = rawRow10603 := by decide +kernel

def row10603 : Integer.Sparse Key := [(key619, 24), (key645, -24)]

theorem rowCheck10603 : row10603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10603 := by decide +kernel

theorem rowEval10603 (x : Key → ℝ) : Integer.Sparse.eval row10603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10603, Integer.Sparse.eval_collectBalanced, rawRowCheck10603]

def rawRow10604 : Integer.Sparse Key := [(key1958, -6), (key1958, -6), (key1958, -6), (key1966, -6), (key1958, 2), (key1958, 2), (key1960, 2), (key1958, 2), (key1958, 2), (key1966, 2), (key1958, 2), (key1960, 2), (key1958, 2), (key1966, 2), (key1960, 2), (key1966, 2)]

theorem rawRowCheck10604 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow10604 := by decide +kernel

def row10604 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

theorem rowCheck10604 : row10604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10604 := by decide +kernel

theorem rowEval10604 (x : Key → ℝ) : Integer.Sparse.eval row10604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck10604, Integer.Sparse.eval_collectBalanced, rawRowCheck10604]

def rawRow10605 : Integer.Sparse Key := [(key1958, -6), (key1958, -6), (key1966, -6), (key1958, -6), (key1958, 2), (key1960, 2), (key1958, 2), (key1958, 2), (key1966, 2), (key1958, 2), (key1960, 2), (key1958, 2), (key1966, 2), (key1958, 2), (key1966, 2), (key1960, 2)]

theorem rawRowCheck10605 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow10605 := by decide +kernel

def row10605 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

theorem rowCheck10605 : row10605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10605 := by decide +kernel

theorem rowEval10605 (x : Key → ℝ) : Integer.Sparse.eval row10605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10605, Integer.Sparse.eval_collectBalanced, rawRowCheck10605]

def rawRow10606 : Integer.Sparse Key := [(key1958, -6), (key1966, -6), (key1958, -6), (key1958, -6), (key1960, 2), (key1958, 2), (key1958, 2), (key1966, 2), (key1958, 2), (key1958, 2), (key1966, 2), (key1966, 2), (key1960, 2), (key1960, 2), (key1958, 2), (key1958, 2)]

theorem rawRowCheck10606 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow10606 := by decide +kernel

def row10606 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

theorem rowCheck10606 : row10606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10606 := by decide +kernel

theorem rowEval10606 (x : Key → ℝ) : Integer.Sparse.eval row10606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10606, Integer.Sparse.eval_collectBalanced, rawRowCheck10606]

def rawRow10607 : Integer.Sparse Key := [(key1966, -6), (key1958, -6), (key1958, -6), (key1958, -6), (key1966, 2), (key1966, 2), (key1966, 2), (key1960, 2), (key1960, 2), (key1960, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2)]

theorem rawRowCheck10607 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow10607 := by decide +kernel

def row10607 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

theorem rowCheck10607 : row10607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10607 := by decide +kernel

theorem rowEval10607 (x : Key → ℝ) : Integer.Sparse.eval row10607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10607, Integer.Sparse.eval_collectBalanced, rawRowCheck10607]

def rawRow10608 : Integer.Sparse Key := [(key1960, -6), (key1960, -6), (key1960, -6), (key1960, -6), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2)]

theorem rawRowCheck10608 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form3 = rawRow10608 := by decide +kernel

def row10608 : Integer.Sparse Key := [(key1958, 24), (key1960, -24)]

theorem rowCheck10608 : row10608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10608 := by decide +kernel

theorem rowEval10608 (x : Key → ℝ) : Integer.Sparse.eval row10608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10608, Integer.Sparse.eval_collectBalanced, rawRowCheck10608]

def rawRow10609 : Integer.Sparse Key := [(key1850, -6), (key1852, -6), (key1852, -6), (key1852, -6), (key1850, 2), (key1852, 2), (key1852, 2), (key1850, 2), (key1852, 2), (key1850, 2), (key1884, 2), (key1852, 2), (key1884, 2), (key1852, 2), (key1852, 2), (key1884, 2)]

theorem rawRowCheck10609 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow10609 := by decide +kernel

def row10609 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

theorem rowCheck10609 : row10609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10609 := by decide +kernel

theorem rowEval10609 (x : Key → ℝ) : Integer.Sparse.eval row10609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck10609, Integer.Sparse.eval_collectBalanced, rawRowCheck10609]

def rawRow10610 : Integer.Sparse Key := [(key1852, -6), (key1850, -6), (key1852, -6), (key1852, -6), (key1852, 2), (key1850, 2), (key1852, 2), (key1852, 2), (key1850, 2), (key1884, 2), (key1850, 2), (key1884, 2), (key1852, 2), (key1852, 2), (key1884, 2), (key1852, 2)]

theorem rawRowCheck10610 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow10610 := by decide +kernel

def row10610 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

theorem rowCheck10610 : row10610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10610 := by decide +kernel

theorem rowEval10610 (x : Key → ℝ) : Integer.Sparse.eval row10610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10610, Integer.Sparse.eval_collectBalanced, rawRowCheck10610]

def rawRow10611 : Integer.Sparse Key := [(key1852, -6), (key1852, -6), (key1850, -6), (key1852, -6), (key1852, 2), (key1852, 2), (key1850, 2), (key1884, 2), (key1884, 2), (key1852, 2), (key1852, 2), (key1850, 2), (key1850, 2), (key1884, 2), (key1852, 2), (key1852, 2)]

theorem rawRowCheck10611 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow10611 := by decide +kernel

def row10611 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

theorem rowCheck10611 : row10611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10611 := by decide +kernel

theorem rowEval10611 (x : Key → ℝ) : Integer.Sparse.eval row10611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10611, Integer.Sparse.eval_collectBalanced, rawRowCheck10611]

def rawRow10612 : Integer.Sparse Key := [(key1852, -6), (key1852, -6), (key1852, -6), (key1850, -6), (key1884, 2), (key1884, 2), (key1884, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1850, 2), (key1850, 2), (key1850, 2)]

theorem rawRowCheck10612 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow10612 := by decide +kernel

def row10612 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

theorem rowCheck10612 : row10612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10612 := by decide +kernel

theorem rowEval10612 (x : Key → ℝ) : Integer.Sparse.eval row10612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10612, Integer.Sparse.eval_collectBalanced, rawRowCheck10612]

def rawRow10613 : Integer.Sparse Key := [(key1884, -6), (key1884, -6), (key1884, -6), (key1884, -6), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2)]

theorem rawRowCheck10613 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form4 = rawRow10613 := by decide +kernel

def row10613 : Integer.Sparse Key := [(key1852, 24), (key1884, -24)]

theorem rowCheck10613 : row10613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10613 := by decide +kernel

theorem rowEval10613 (x : Key → ℝ) : Integer.Sparse.eval row10613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10613, Integer.Sparse.eval_collectBalanced, rawRowCheck10613]

def rawRow10614 : Integer.Sparse Key := [(key1859, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1861, -2), (key1859, -2), (key1877, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1859, 1), (key1861, 1), (key1859, 1), (key1867, 1), (key1861, 1), (key1867, 1), (key1859, 1), (key1861, 1), (key1859, 1), (key1877, 1), (key1861, 1), (key1877, 1), (key1859, 1), (key1867, 1), (key1859, 1), (key1877, 1), (key1867, 1), (key1877, 1), (key1861, 1), (key1867, 1), (key1861, 1), (key1877, 1), (key1867, 1), (key1877, 1)]

theorem rawRowCheck10614 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form5 = rawRow10614 := by decide +kernel

def row10614 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

theorem rowCheck10614 : row10614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10614 := by decide +kernel

theorem rowEval10614 (x : Key → ℝ) : Integer.Sparse.eval row10614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck10614, Integer.Sparse.eval_collectBalanced, rawRowCheck10614]

def rawRow10615 : Integer.Sparse Key := [(key1861, -2), (key1859, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1877, -2), (key1859, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1861, 1), (key1859, 1), (key1867, 1), (key1859, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1877, 1), (key1859, 1), (key1877, 1), (key1861, 1), (key1867, 1), (key1859, 1), (key1877, 1), (key1859, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1877, 1), (key1861, 1), (key1877, 1), (key1867, 1)]

theorem rawRowCheck10615 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form5 = rawRow10615 := by decide +kernel

def row10615 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

theorem rowCheck10615 : row10615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10615 := by decide +kernel

theorem rowEval10615 (x : Key → ℝ) : Integer.Sparse.eval row10615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10615, Integer.Sparse.eval_collectBalanced, rawRowCheck10615]

def rawRow10616 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1859, -2), (key1877, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1859, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1)]

theorem rawRowCheck10616 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form5 = rawRow10616 := by decide +kernel

def row10616 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

theorem rowCheck10616 : row10616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10616 := by decide +kernel

theorem rowEval10616 (x : Key → ℝ) : Integer.Sparse.eval row10616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10616, Integer.Sparse.eval_collectBalanced, rawRowCheck10616]

def rawRow10617 : Integer.Sparse Key := [(key1877, -2), (key1877, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1)]

theorem rawRowCheck10617 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow10617 := by decide +kernel

def row10617 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

theorem rowCheck10617 : row10617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10617 := by decide +kernel

theorem rowEval10617 (x : Key → ℝ) : Integer.Sparse.eval row10617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10617, Integer.Sparse.eval_collectBalanced, rawRowCheck10617]

def rawRow10618 : Integer.Sparse Key := [(key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1)]

theorem rawRowCheck10618 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form5 = rawRow10618 := by decide +kernel

def row10618 : Integer.Sparse Key := [(key1861, 24), (key1867, -24)]

theorem rowCheck10618 : row10618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10618 := by decide +kernel

theorem rowEval10618 (x : Key → ℝ) : Integer.Sparse.eval row10618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10618, Integer.Sparse.eval_collectBalanced, rawRowCheck10618]

def rawRow10619 : Integer.Sparse Key := [(key1957, -24), (key1957, 6), (key1957, 6), (key1957, 6), (key1969, 6)]

theorem rawRowCheck10619 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form6 = rawRow10619 := by decide +kernel

def row10619 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

theorem rowCheck10619 : row10619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10619 := by decide +kernel

theorem rowEval10619 (x : Key → ℝ) : Integer.Sparse.eval row10619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck10619, Integer.Sparse.eval_collectBalanced, rawRowCheck10619]

def rawRow10620 : Integer.Sparse Key := [(key1957, -24), (key1957, 6), (key1957, 6), (key1969, 6), (key1957, 6)]

theorem rawRowCheck10620 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form6 = rawRow10620 := by decide +kernel

def row10620 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

theorem rowCheck10620 : row10620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10620 := by decide +kernel

theorem rowEval10620 (x : Key → ℝ) : Integer.Sparse.eval row10620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10620, Integer.Sparse.eval_collectBalanced, rawRowCheck10620]

def rawRow10621 : Integer.Sparse Key := [(key1957, -24), (key1957, 6), (key1969, 6), (key1957, 6), (key1957, 6)]

theorem rawRowCheck10621 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form6 = rawRow10621 := by decide +kernel

def row10621 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

theorem rowCheck10621 : row10621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10621 := by decide +kernel

theorem rowEval10621 (x : Key → ℝ) : Integer.Sparse.eval row10621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10621, Integer.Sparse.eval_collectBalanced, rawRowCheck10621]

def rawRow10622 : Integer.Sparse Key := [(key1957, -24), (key1969, 6), (key1957, 6), (key1957, 6), (key1957, 6)]

theorem rawRowCheck10622 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow10622 := by decide +kernel

def row10622 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

theorem rowCheck10622 : row10622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10622 := by decide +kernel

theorem rowEval10622 (x : Key → ℝ) : Integer.Sparse.eval row10622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10622, Integer.Sparse.eval_collectBalanced, rawRowCheck10622]

def rawRow10623 : Integer.Sparse Key := [(key1969, -24), (key1957, 6), (key1957, 6), (key1957, 6), (key1957, 6)]

theorem rawRowCheck10623 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form6 = rawRow10623 := by decide +kernel

def row10623 : Integer.Sparse Key := [(key1957, 24), (key1969, -24)]

theorem rowCheck10623 : row10623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10623 := by decide +kernel

theorem rowEval10623 (x : Key → ℝ) : Integer.Sparse.eval row10623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10623, Integer.Sparse.eval_collectBalanced, rawRowCheck10623]

end MUB6.Certificate.GramRows

end OAI

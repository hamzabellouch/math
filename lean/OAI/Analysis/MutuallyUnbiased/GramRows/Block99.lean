import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
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

def rawRow9600 : Integer.Sparse Key := [(key2402, -6), (key2402, -6), (key2439, -6), (key2408, -6), (key2847, 2), (key2847, 2), (key3020, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2596, 2), (key2884, 2), (key2884, 2)]

theorem rawRowCheck9600 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form4 = rawRow9600 := by decide +kernel

def row9600 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9600 : row9600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9600 := by decide +kernel

theorem rowEval9600 (x : Key → ℝ) : Integer.Sparse.eval row9600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9600, Integer.Sparse.eval_collectBalanced, rawRowCheck9600]

def rawRow9601 : Integer.Sparse Key := [(key2402, -6), (key2439, -6), (key2402, -6), (key2408, -6), (key2847, 2), (key3020, 2), (key2847, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2884, 2), (key2596, 2), (key2884, 2)]

theorem rawRowCheck9601 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form4 = rawRow9601 := by decide +kernel

def row9601 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9601 : row9601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9601 := by decide +kernel

theorem rowEval9601 (x : Key → ℝ) : Integer.Sparse.eval row9601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9601, Integer.Sparse.eval_collectBalanced, rawRowCheck9601]

def rawRow9602 : Integer.Sparse Key := [(key2439, -6), (key2402, -6), (key2402, -6), (key2408, -6), (key3020, 2), (key2847, 2), (key2847, 2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2884, 2), (key2884, 2), (key2596, 2)]

theorem rawRowCheck9602 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form4 = rawRow9602 := by decide +kernel

def row9602 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9602 : row9602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9602 := by decide +kernel

theorem rowEval9602 (x : Key → ℝ) : Integer.Sparse.eval row9602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9602, Integer.Sparse.eval_collectBalanced, rawRowCheck9602]

def rawRow9603 : Integer.Sparse Key := [(key2402, -6), (key2408, -6), (key2439, -6), (key2402, -6), (key2878, 2), (key2884, 2), (key3029, 2), (key2591, 2), (key2596, 2), (key2847, 2), (key2884, 2), (key3020, 2), (key3029, 2), (key2591, 2), (key2847, 2), (key2878, 2)]

theorem rawRowCheck9603 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form4 = rawRow9603 := by decide +kernel

def row9603 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9603 : row9603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9603 := by decide +kernel

theorem rowEval9603 (x : Key → ℝ) : Integer.Sparse.eval row9603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9603, Integer.Sparse.eval_collectBalanced, rawRowCheck9603]

def rawRow9604 : Integer.Sparse Key := [(key2408, -6), (key2402, -6), (key2439, -6), (key2402, -6), (key2884, 2), (key2878, 2), (key3029, 2), (key2596, 2), (key2591, 2), (key2884, 2), (key2847, 2), (key3029, 2), (key3020, 2), (key2591, 2), (key2878, 2), (key2847, 2)]

theorem rawRowCheck9604 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form4 = rawRow9604 := by decide +kernel

def row9604 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9604 : row9604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9604 := by decide +kernel

theorem rowEval9604 (x : Key → ℝ) : Integer.Sparse.eval row9604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9604, Integer.Sparse.eval_collectBalanced, rawRowCheck9604]

def rawRow9605 : Integer.Sparse Key := [(key2402, -6), (key2439, -6), (key2408, -6), (key2402, -6), (key2878, 2), (key3029, 2), (key2884, 2), (key2847, 2), (key3020, 2), (key2591, 2), (key3029, 2), (key2596, 2), (key2884, 2), (key2847, 2), (key2591, 2), (key2878, 2)]

theorem rawRowCheck9605 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form4 = rawRow9605 := by decide +kernel

def row9605 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9605 : row9605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9605 := by decide +kernel

theorem rowEval9605 (x : Key → ℝ) : Integer.Sparse.eval row9605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9605, Integer.Sparse.eval_collectBalanced, rawRowCheck9605]

def rawRow9606 : Integer.Sparse Key := [(key2439, -6), (key2402, -6), (key2408, -6), (key2402, -6), (key3029, 2), (key2878, 2), (key2884, 2), (key3020, 2), (key2847, 2), (key3029, 2), (key2591, 2), (key2884, 2), (key2596, 2), (key2847, 2), (key2878, 2), (key2591, 2)]

theorem rawRowCheck9606 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form4 = rawRow9606 := by decide +kernel

def row9606 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9606 : row9606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9606 := by decide +kernel

theorem rowEval9606 (x : Key → ℝ) : Integer.Sparse.eval row9606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9606, Integer.Sparse.eval_collectBalanced, rawRowCheck9606]

def rawRow9607 : Integer.Sparse Key := [(key2408, -6), (key2439, -6), (key2402, -6), (key2402, -6), (key2884, 2), (key3029, 2), (key2878, 2), (key2884, 2), (key3029, 2), (key2596, 2), (key3020, 2), (key2591, 2), (key2847, 2), (key2878, 2), (key2591, 2), (key2847, 2)]

theorem rawRowCheck9607 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form4 = rawRow9607 := by decide +kernel

def row9607 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9607 : row9607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9607 := by decide +kernel

theorem rowEval9607 (x : Key → ℝ) : Integer.Sparse.eval row9607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9607, Integer.Sparse.eval_collectBalanced, rawRowCheck9607]

def rawRow9608 : Integer.Sparse Key := [(key2439, -6), (key2408, -6), (key2402, -6), (key2402, -6), (key3029, 2), (key2884, 2), (key2878, 2), (key3029, 2), (key2884, 2), (key3020, 2), (key2596, 2), (key2847, 2), (key2591, 2), (key2878, 2), (key2847, 2), (key2591, 2)]

theorem rawRowCheck9608 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form4 = rawRow9608 := by decide +kernel

def row9608 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9608 : row9608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9608 := by decide +kernel

theorem rowEval9608 (x : Key → ℝ) : Integer.Sparse.eval row9608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9608, Integer.Sparse.eval_collectBalanced, rawRowCheck9608]

def rawRow9609 : Integer.Sparse Key := [(key2468, -6), (key2468, -6), (key2481, -6), (key2505, -6), (key2374, 2), (key2374, 2), (key2391, 2), (key2770, 2), (key2770, 2), (key2878, 2), (key2878, 2), (key2926, 2), (key2926, 2), (key3006, 2), (key3029, 2), (key3029, 2)]

theorem rawRowCheck9609 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form4 = rawRow9609 := by decide +kernel

def row9609 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2770, 4), (key2878, 4), (key2926, 4), (key3006, 2), (key3029, 4)]

theorem rowCheck9609 : row9609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9609 := by decide +kernel

theorem rowEval9609 (x : Key → ℝ) : Integer.Sparse.eval row9609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9609, Integer.Sparse.eval_collectBalanced, rawRowCheck9609]

def rawRow9610 : Integer.Sparse Key := [(key2468, -6), (key2481, -6), (key2468, -6), (key2505, -6), (key2374, 2), (key2391, 2), (key2374, 2), (key2878, 2), (key2926, 2), (key2770, 2), (key2926, 2), (key2770, 2), (key2878, 2), (key3029, 2), (key3006, 2), (key3029, 2)]

theorem rawRowCheck9610 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form4 = rawRow9610 := by decide +kernel

def row9610 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2770, 4), (key2878, 4), (key2926, 4), (key3006, 2), (key3029, 4)]

theorem rowCheck9610 : row9610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9610 := by decide +kernel

theorem rowEval9610 (x : Key → ℝ) : Integer.Sparse.eval row9610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9610, Integer.Sparse.eval_collectBalanced, rawRowCheck9610]

def rawRow9611 : Integer.Sparse Key := [(key2481, -6), (key2468, -6), (key2468, -6), (key2505, -6), (key2391, 2), (key2374, 2), (key2374, 2), (key2926, 2), (key2878, 2), (key2926, 2), (key2770, 2), (key2878, 2), (key2770, 2), (key3029, 2), (key3029, 2), (key3006, 2)]

theorem rawRowCheck9611 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form4 = rawRow9611 := by decide +kernel

def row9611 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2770, 4), (key2878, 4), (key2926, 4), (key3006, 2), (key3029, 4)]

theorem rowCheck9611 : row9611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9611 := by decide +kernel

theorem rowEval9611 (x : Key → ℝ) : Integer.Sparse.eval row9611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9611, Integer.Sparse.eval_collectBalanced, rawRowCheck9611]

def rawRow9612 : Integer.Sparse Key := [(key2468, -6), (key2468, -6), (key2505, -6), (key2481, -6), (key2402, 2), (key2402, 2), (key2439, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2605, 2), (key2926, 2), (key2926, 2)]

theorem rawRowCheck9612 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form4 = rawRow9612 := by decide +kernel

def row9612 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2591, 4), (key2605, 2), (key2878, 4), (key2926, 4), (key3029, 4)]

theorem rowCheck9612 : row9612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9612 := by decide +kernel

theorem rowEval9612 (x : Key → ℝ) : Integer.Sparse.eval row9612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9612, Integer.Sparse.eval_collectBalanced, rawRowCheck9612]

def rawRow9613 : Integer.Sparse Key := [(key2468, -6), (key2505, -6), (key2468, -6), (key2481, -6), (key2402, 2), (key2439, 2), (key2402, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2926, 2), (key2605, 2), (key2926, 2)]

theorem rawRowCheck9613 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form4 = rawRow9613 := by decide +kernel

def row9613 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2591, 4), (key2605, 2), (key2878, 4), (key2926, 4), (key3029, 4)]

theorem rowCheck9613 : row9613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9613 := by decide +kernel

theorem rowEval9613 (x : Key → ℝ) : Integer.Sparse.eval row9613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9613, Integer.Sparse.eval_collectBalanced, rawRowCheck9613]

def rawRow9614 : Integer.Sparse Key := [(key2505, -6), (key2468, -6), (key2468, -6), (key2481, -6), (key2439, 2), (key2402, 2), (key2402, 2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2926, 2), (key2926, 2), (key2605, 2)]

theorem rawRowCheck9614 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form4 = rawRow9614 := by decide +kernel

def row9614 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2591, 4), (key2605, 2), (key2878, 4), (key2926, 4), (key3029, 4)]

theorem rowCheck9614 : row9614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9614 := by decide +kernel

theorem rowEval9614 (x : Key → ℝ) : Integer.Sparse.eval row9614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9614, Integer.Sparse.eval_collectBalanced, rawRowCheck9614]

def rawRow9615 : Integer.Sparse Key := [(key2468, -6), (key2481, -6), (key2505, -6), (key2468, -6), (key2535, 2), (key2542, 2), (key2553, 2), (key2374, 2), (key2391, 2), (key2402, 2), (key2542, 2), (key2439, 2), (key2553, 2), (key2591, 2), (key2770, 2), (key2878, 2)]

theorem rawRowCheck9615 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form4 = rawRow9615 := by decide +kernel

def row9615 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

theorem rowCheck9615 : row9615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9615 := by decide +kernel

theorem rowEval9615 (x : Key → ℝ) : Integer.Sparse.eval row9615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9615, Integer.Sparse.eval_collectBalanced, rawRowCheck9615]

def rawRow9616 : Integer.Sparse Key := [(key2481, -6), (key2468, -6), (key2505, -6), (key2468, -6), (key2542, 2), (key2535, 2), (key2553, 2), (key2391, 2), (key2374, 2), (key2542, 2), (key2402, 2), (key2553, 2), (key2439, 2), (key2591, 2), (key2878, 2), (key2770, 2)]

theorem rawRowCheck9616 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form4 = rawRow9616 := by decide +kernel

def row9616 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

theorem rowCheck9616 : row9616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9616 := by decide +kernel

theorem rowEval9616 (x : Key → ℝ) : Integer.Sparse.eval row9616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9616, Integer.Sparse.eval_collectBalanced, rawRowCheck9616]

def rawRow9617 : Integer.Sparse Key := [(key2468, -6), (key2505, -6), (key2481, -6), (key2468, -6), (key2535, 2), (key2553, 2), (key2542, 2), (key2402, 2), (key2439, 2), (key2374, 2), (key2553, 2), (key2391, 2), (key2542, 2), (key2770, 2), (key2591, 2), (key2878, 2)]

theorem rawRowCheck9617 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form4 = rawRow9617 := by decide +kernel

def row9617 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

theorem rowCheck9617 : row9617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9617 := by decide +kernel

theorem rowEval9617 (x : Key → ℝ) : Integer.Sparse.eval row9617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9617, Integer.Sparse.eval_collectBalanced, rawRowCheck9617]

def rawRow9618 : Integer.Sparse Key := [(key2505, -6), (key2468, -6), (key2481, -6), (key2468, -6), (key2553, 2), (key2535, 2), (key2542, 2), (key2439, 2), (key2402, 2), (key2553, 2), (key2374, 2), (key2542, 2), (key2391, 2), (key2770, 2), (key2878, 2), (key2591, 2)]

theorem rawRowCheck9618 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form4 = rawRow9618 := by decide +kernel

def row9618 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

theorem rowCheck9618 : row9618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9618 := by decide +kernel

theorem rowEval9618 (x : Key → ℝ) : Integer.Sparse.eval row9618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9618, Integer.Sparse.eval_collectBalanced, rawRowCheck9618]

def rawRow9619 : Integer.Sparse Key := [(key2481, -6), (key2505, -6), (key2468, -6), (key2468, -6), (key2542, 2), (key2553, 2), (key2535, 2), (key2542, 2), (key2553, 2), (key2391, 2), (key2439, 2), (key2374, 2), (key2402, 2), (key2878, 2), (key2591, 2), (key2770, 2)]

theorem rawRowCheck9619 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form4 = rawRow9619 := by decide +kernel

def row9619 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

theorem rowCheck9619 : row9619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9619 := by decide +kernel

theorem rowEval9619 (x : Key → ℝ) : Integer.Sparse.eval row9619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9619, Integer.Sparse.eval_collectBalanced, rawRowCheck9619]

def rawRow9620 : Integer.Sparse Key := [(key2505, -6), (key2481, -6), (key2468, -6), (key2468, -6), (key2553, 2), (key2542, 2), (key2535, 2), (key2553, 2), (key2542, 2), (key2439, 2), (key2391, 2), (key2402, 2), (key2374, 2), (key2878, 2), (key2770, 2), (key2591, 2)]

theorem rawRowCheck9620 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form4 = rawRow9620 := by decide +kernel

def row9620 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, -12), (key2481, -6), (key2505, -6), (key2535, 2), (key2542, 4), (key2553, 4), (key2591, 2), (key2770, 2), (key2878, 2)]

theorem rowCheck9620 : row9620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9620 := by decide +kernel

theorem rowEval9620 (x : Key → ℝ) : Integer.Sparse.eval row9620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck9620, Integer.Sparse.eval_collectBalanced, rawRowCheck9620]

def rawRow9621 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2809, -2), (key2809, -2), (key2829, -2), (key2829, -2), (key2835, -2), (key2835, -2), (key3012, -2), (key3017, -2), (key3017, -2), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2644, 1), (key2644, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1), (key2860, 1), (key2860, 1), (key2870, 1), (key2870, 1), (key2885, 1), (key2885, 1), (key3023, 1), (key3023, 1), (key3026, 1), (key3026, 1), (key3030, 1), (key3030, 1)]

theorem rawRowCheck9621 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form5 = rawRow9621 := by decide +kernel

def row9621 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2809, -4), (key2829, -4), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9621 : row9621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9621 := by decide +kernel

theorem rowEval9621 (x : Key → ℝ) : Integer.Sparse.eval row9621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9621, Integer.Sparse.eval_collectBalanced, rawRowCheck9621]

def rawRow9622 : Integer.Sparse Key := [(key2612, -2), (key2618, -2), (key2616, -2), (key2829, -2), (key2835, -2), (key2809, -2), (key2835, -2), (key2809, -2), (key2829, -2), (key3017, -2), (key3012, -2), (key3017, -2), (key2640, 1), (key2644, 1), (key2632, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3030, 1), (key3023, 1), (key3026, 1)]

theorem rawRowCheck9622 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form5 = rawRow9622 := by decide +kernel

def row9622 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2809, -4), (key2829, -4), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9622 : row9622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9622 := by decide +kernel

theorem rowEval9622 (x : Key → ℝ) : Integer.Sparse.eval row9622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9622, Integer.Sparse.eval_collectBalanced, rawRowCheck9622]

def rawRow9623 : Integer.Sparse Key := [(key2618, -2), (key2612, -2), (key2616, -2), (key2835, -2), (key2829, -2), (key2835, -2), (key2809, -2), (key2829, -2), (key2809, -2), (key3017, -2), (key3017, -2), (key3012, -2), (key2644, 1), (key2640, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key2885, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key2860, 1), (key3030, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key3023, 1)]

theorem rawRowCheck9623 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form5 = rawRow9623 := by decide +kernel

def row9623 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2809, -4), (key2829, -4), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9623 : row9623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9623 := by decide +kernel

theorem rowEval9623 (x : Key → ℝ) : Integer.Sparse.eval row9623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9623, Integer.Sparse.eval_collectBalanced, rawRowCheck9623]

def rawRow9624 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2612, -2), (key2616, -2), (key2829, -2), (key2829, -2), (key3017, -2), (key3017, -2), (key2621, -2), (key2835, -2), (key2835, -2), (key2706, 1), (key2706, 1), (key2860, 1), (key2860, 1), (key3023, 1), (key3023, 1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2644, 1), (key2644, 1), (key2732, 1), (key2732, 1), (key2885, 1), (key2885, 1)]

theorem rawRowCheck9624 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form5 = rawRow9624 := by decide +kernel

def row9624 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -4), (key2829, -4), (key2831, -2), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9624 : row9624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9624 := by decide +kernel

theorem rowEval9624 (x : Key → ℝ) : Integer.Sparse.eval row9624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9624, Integer.Sparse.eval_collectBalanced, rawRowCheck9624]

def rawRow9625 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2948, -2), (key2960, -2), (key2612, -2), (key2960, -2), (key2616, -2), (key2829, -2), (key2835, -2), (key2621, -2), (key2835, -2), (key2860, 1), (key3023, 1), (key2706, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2885, 1), (key2644, 1), (key2732, 1)]

theorem rawRowCheck9625 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form5 = rawRow9625 := by decide +kernel

def row9625 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -4), (key2829, -2), (key2831, -2), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9625 : row9625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9625 := by decide +kernel

theorem rowEval9625 (x : Key → ℝ) : Integer.Sparse.eval row9625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9625, Integer.Sparse.eval_collectBalanced, rawRowCheck9625]

def rawRow9626 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2960, -2), (key2948, -2), (key2960, -2), (key2612, -2), (key2829, -2), (key2616, -2), (key2835, -2), (key2835, -2), (key2621, -2), (key3023, 1), (key2860, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2885, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2644, 1)]

theorem rawRowCheck9626 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form5 = rawRow9626 := by decide +kernel

def row9626 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -4), (key2829, -2), (key2831, -2), (key2835, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9626 : row9626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9626 := by decide +kernel

theorem rowEval9626 (x : Key → ℝ) : Integer.Sparse.eval row9626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9626, Integer.Sparse.eval_collectBalanced, rawRowCheck9626]

def rawRow9627 : Integer.Sparse Key := [(key2948, -2), (key2950, -2), (key2960, -2), (key2612, -2), (key2618, -2), (key2805, -2), (key2950, -2), (key2831, -2), (key2960, -2), (key2616, -2), (key2809, -2), (key2829, -2), (key2726, 1), (key2732, 1), (key2870, 1), (key2885, 1), (key3026, 1), (key3030, 1), (key2640, 1), (key2644, 1), (key2860, 1), (key2885, 1), (key3023, 1), (key3030, 1), (key2632, 1), (key2644, 1), (key2706, 1), (key2732, 1), (key3023, 1), (key3026, 1), (key2632, 1), (key2640, 1), (key2706, 1), (key2726, 1), (key2860, 1), (key2870, 1)]

theorem rawRowCheck9627 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form5 = rawRow9627 := by decide +kernel

def row9627 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9627 : row9627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9627 := by decide +kernel

theorem rowEval9627 (x : Key → ℝ) : Integer.Sparse.eval row9627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9627, Integer.Sparse.eval_collectBalanced, rawRowCheck9627]

def rawRow9628 : Integer.Sparse Key := [(key2950, -2), (key2948, -2), (key2960, -2), (key2618, -2), (key2612, -2), (key2950, -2), (key2805, -2), (key2960, -2), (key2831, -2), (key2616, -2), (key2829, -2), (key2809, -2), (key2732, 1), (key2726, 1), (key2885, 1), (key2870, 1), (key3030, 1), (key3026, 1), (key2644, 1), (key2640, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key3023, 1), (key2644, 1), (key2632, 1), (key2732, 1), (key2706, 1), (key3026, 1), (key3023, 1), (key2640, 1), (key2632, 1), (key2726, 1), (key2706, 1), (key2870, 1), (key2860, 1)]

theorem rawRowCheck9628 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form5 = rawRow9628 := by decide +kernel

def row9628 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9628 : row9628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9628 := by decide +kernel

theorem rowEval9628 (x : Key → ℝ) : Integer.Sparse.eval row9628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9628, Integer.Sparse.eval_collectBalanced, rawRowCheck9628]

def rawRow9629 : Integer.Sparse Key := [(key2948, -2), (key2960, -2), (key2950, -2), (key2805, -2), (key2831, -2), (key2612, -2), (key2960, -2), (key2618, -2), (key2950, -2), (key2809, -2), (key2616, -2), (key2829, -2), (key2870, 1), (key3026, 1), (key2726, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2860, 1), (key3023, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2706, 1), (key3023, 1), (key2632, 1), (key3026, 1), (key2644, 1), (key2732, 1), (key2706, 1), (key2860, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2726, 1)]

theorem rawRowCheck9629 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form5 = rawRow9629 := by decide +kernel

def row9629 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9629 : row9629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9629 := by decide +kernel

theorem rowEval9629 (x : Key → ℝ) : Integer.Sparse.eval row9629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9629, Integer.Sparse.eval_collectBalanced, rawRowCheck9629]

def rawRow9630 : Integer.Sparse Key := [(key2960, -2), (key2948, -2), (key2950, -2), (key2831, -2), (key2805, -2), (key2960, -2), (key2612, -2), (key2950, -2), (key2618, -2), (key2809, -2), (key2829, -2), (key2616, -2), (key3026, 1), (key2870, 1), (key3030, 1), (key2726, 1), (key2885, 1), (key2732, 1), (key3023, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key2885, 1), (key2644, 1), (key3023, 1), (key2706, 1), (key3026, 1), (key2632, 1), (key2732, 1), (key2644, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2726, 1), (key2640, 1)]

theorem rawRowCheck9630 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form5 = rawRow9630 := by decide +kernel

def row9630 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9630 : row9630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9630 := by decide +kernel

theorem rowEval9630 (x : Key → ℝ) : Integer.Sparse.eval row9630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9630, Integer.Sparse.eval_collectBalanced, rawRowCheck9630]

def rawRow9631 : Integer.Sparse Key := [(key2950, -2), (key2960, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2618, -2), (key2831, -2), (key2612, -2), (key2805, -2), (key2829, -2), (key2616, -2), (key2809, -2), (key2885, 1), (key3030, 1), (key2732, 1), (key3026, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2640, 1), (key2860, 1), (key2732, 1), (key3026, 1), (key2644, 1), (key3023, 1), (key2632, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2632, 1), (key2706, 1)]

theorem rawRowCheck9631 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form5 = rawRow9631 := by decide +kernel

def row9631 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9631 : row9631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9631 := by decide +kernel

theorem rowEval9631 (x : Key → ℝ) : Integer.Sparse.eval row9631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9631, Integer.Sparse.eval_collectBalanced, rawRowCheck9631]

def rawRow9632 : Integer.Sparse Key := [(key2960, -2), (key2950, -2), (key2948, -2), (key2960, -2), (key2950, -2), (key2831, -2), (key2618, -2), (key2805, -2), (key2612, -2), (key2829, -2), (key2809, -2), (key2616, -2), (key3030, 1), (key2885, 1), (key3026, 1), (key2732, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2885, 1), (key3023, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key3026, 1), (key2732, 1), (key3023, 1), (key2644, 1), (key2706, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key2860, 1), (key2640, 1), (key2706, 1), (key2632, 1)]

theorem rawRowCheck9632 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form5 = rawRow9632 := by decide +kernel

def row9632 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2805, -2), (key2809, -2), (key2829, -2), (key2831, -2), (key2860, 2), (key2870, 2), (key2885, 2), (key2948, -2), (key2950, -4), (key2960, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9632 : row9632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9632 := by decide +kernel

theorem rowEval9632 (x : Key → ℝ) : Integer.Sparse.eval row9632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9632, Integer.Sparse.eval_collectBalanced, rawRowCheck9632]

def rawRow9633 : Integer.Sparse Key := [(key2628, -2), (key2628, -2), (key2641, -2), (key2702, -2), (key2702, -2), (key2972, -2), (key2972, -2), (key2976, -2), (key2976, -2), (key2728, -2), (key2983, -2), (key2983, -2), (key2612, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2660, 1), (key2660, 1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1), (key2794, 1), (key2794, 1), (key2829, 1), (key2829, 1), (key2927, 1), (key2927, 1), (key3010, 1), (key3010, 1), (key3017, 1), (key3017, 1), (key3030, 1), (key3030, 1)]

theorem rawRowCheck9633 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form5 = rawRow9633 := by decide +kernel

def row9633 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2671, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2758, 2), (key2794, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck9633 : row9633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9633 := by decide +kernel

theorem rowEval9633 (x : Key → ℝ) : Integer.Sparse.eval row9633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9633, Integer.Sparse.eval_collectBalanced, rawRowCheck9633]

def rawRow9634 : Integer.Sparse Key := [(key2628, -2), (key2641, -2), (key2628, -2), (key2972, -2), (key2976, -2), (key2702, -2), (key2976, -2), (key2702, -2), (key2972, -2), (key2983, -2), (key2728, -2), (key2983, -2), (key2646, 1), (key2653, 1), (key2612, 1), (key2653, 1), (key2616, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3017, 1)]

theorem rawRowCheck9634 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form5 = rawRow9634 := by decide +kernel

def row9634 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2758, 2), (key2794, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck9634 : row9634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9634 := by decide +kernel

theorem rowEval9634 (x : Key → ℝ) : Integer.Sparse.eval row9634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9634, Integer.Sparse.eval_collectBalanced, rawRowCheck9634]

def rawRow9635 : Integer.Sparse Key := [(key2641, -2), (key2628, -2), (key2628, -2), (key2976, -2), (key2972, -2), (key2976, -2), (key2702, -2), (key2972, -2), (key2702, -2), (key2983, -2), (key2983, -2), (key2728, -2), (key2653, 1), (key2646, 1), (key2653, 1), (key2612, 1), (key2640, 1), (key2616, 1), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2927, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key2794, 1), (key3030, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key3010, 1)]

theorem rawRowCheck9635 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form5 = rawRow9635 := by decide +kernel

def row9635 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2758, 2), (key2794, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck9635 : row9635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9635 := by decide +kernel

theorem rowEval9635 (x : Key → ℝ) : Integer.Sparse.eval row9635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9635, Integer.Sparse.eval_collectBalanced, rawRowCheck9635]

def rawRow9636 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2628, -2), (key2628, -2), (key2972, -2), (key2972, -2), (key2983, -2), (key2983, -2), (key2641, -2), (key2976, -2), (key2976, -2), (key2667, 1), (key2667, 1), (key2735, 1), (key2735, 1), (key2747, 1), (key2747, 1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2660, 1), (key2660, 1), (key2758, 1), (key2758, 1), (key2927, 1), (key2927, 1)]

theorem rawRowCheck9636 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form5 = rawRow9636 := by decide +kernel

def row9636 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2667, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2735, 2), (key2747, 2), (key2758, 2), (key2829, 2), (key2927, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3017, 2), (key3030, 2)]

theorem rowCheck9636 : row9636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9636 := by decide +kernel

theorem rowEval9636 (x : Key → ℝ) : Integer.Sparse.eval row9636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9636, Integer.Sparse.eval_collectBalanced, rawRowCheck9636]

def rawRow9637 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2972, -2), (key2983, -2), (key2628, -2), (key2983, -2), (key2628, -2), (key2972, -2), (key2976, -2), (key2641, -2), (key2976, -2), (key2735, 1), (key2747, 1), (key2667, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2758, 1)]

theorem rawRowCheck9637 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form5 = rawRow9637 := by decide +kernel

def row9637 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2667, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2735, 2), (key2747, 2), (key2758, 2), (key2829, 1), (key2927, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3030, 2)]

theorem rowCheck9637 : row9637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9637 := by decide +kernel

theorem rowEval9637 (x : Key → ℝ) : Integer.Sparse.eval row9637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9637, Integer.Sparse.eval_collectBalanced, rawRowCheck9637]

def rawRow9638 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2983, -2), (key2972, -2), (key2983, -2), (key2628, -2), (key2972, -2), (key2628, -2), (key2976, -2), (key2976, -2), (key2641, -2), (key2747, 1), (key2735, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2667, 1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2927, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2660, 1)]

theorem rawRowCheck9638 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form5 = rawRow9638 := by decide +kernel

def row9638 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2667, 2), (key2702, -4), (key2726, 2), (key2728, -2), (key2735, 2), (key2747, 2), (key2758, 2), (key2829, 1), (key2927, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key3030, 2)]

theorem rowCheck9638 : row9638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9638 := by decide +kernel

theorem rowEval9638 (x : Key → ℝ) : Integer.Sparse.eval row9638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9638, Integer.Sparse.eval_collectBalanced, rawRowCheck9638]

def rawRow9639 : Integer.Sparse Key := [(key2972, -2), (key2976, -2), (key2983, -2), (key2628, -2), (key2641, -2), (key2702, -2), (key2976, -2), (key2728, -2), (key2983, -2), (key2628, -2), (key2702, -2), (key2972, -2), (key2936, 1), (key2943, 1), (key2948, 1), (key2998, 1), (key2960, 1), (key3000, 1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2612, 1), (key2653, 1), (key2667, 1), (key2943, 1), (key2747, 1), (key2960, 1), (key2616, 1), (key2640, 1), (key2671, 1), (key2726, 1), (key2794, 1), (key2829, 1)]

theorem rawRowCheck9639 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form5 = rawRow9639 := by decide +kernel

def row9639 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

theorem rowCheck9639 : row9639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9639 := by decide +kernel

theorem rowEval9639 (x : Key → ℝ) : Integer.Sparse.eval row9639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9639, Integer.Sparse.eval_collectBalanced, rawRowCheck9639]

def rawRow9640 : Integer.Sparse Key := [(key2976, -2), (key2972, -2), (key2983, -2), (key2641, -2), (key2628, -2), (key2976, -2), (key2702, -2), (key2983, -2), (key2728, -2), (key2628, -2), (key2972, -2), (key2702, -2), (key2943, 1), (key2936, 1), (key2998, 1), (key2948, 1), (key3000, 1), (key2960, 1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2653, 1), (key2612, 1), (key2943, 1), (key2667, 1), (key2960, 1), (key2747, 1), (key2640, 1), (key2616, 1), (key2726, 1), (key2671, 1), (key2829, 1), (key2794, 1)]

theorem rawRowCheck9640 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form5 = rawRow9640 := by decide +kernel

def row9640 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

theorem rowCheck9640 : row9640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9640 := by decide +kernel

theorem rowEval9640 (x : Key → ℝ) : Integer.Sparse.eval row9640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9640, Integer.Sparse.eval_collectBalanced, rawRowCheck9640]

def rawRow9641 : Integer.Sparse Key := [(key2972, -2), (key2983, -2), (key2976, -2), (key2702, -2), (key2728, -2), (key2628, -2), (key2983, -2), (key2641, -2), (key2976, -2), (key2702, -2), (key2628, -2), (key2972, -2), (key2948, 1), (key2960, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2667, 1), (key2747, 1), (key2612, 1), (key2960, 1), (key2653, 1), (key2943, 1), (key2671, 1), (key2794, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2726, 1)]

theorem rawRowCheck9641 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form5 = rawRow9641 := by decide +kernel

def row9641 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

theorem rowCheck9641 : row9641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9641 := by decide +kernel

theorem rowEval9641 (x : Key → ℝ) : Integer.Sparse.eval row9641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9641, Integer.Sparse.eval_collectBalanced, rawRowCheck9641]

def rawRow9642 : Integer.Sparse Key := [(key2983, -2), (key2972, -2), (key2976, -2), (key2728, -2), (key2702, -2), (key2983, -2), (key2628, -2), (key2976, -2), (key2641, -2), (key2702, -2), (key2972, -2), (key2628, -2), (key2960, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2998, 1), (key2943, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2747, 1), (key2667, 1), (key2960, 1), (key2612, 1), (key2943, 1), (key2653, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2726, 1), (key2640, 1)]

theorem rawRowCheck9642 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form5 = rawRow9642 := by decide +kernel

def row9642 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

theorem rowCheck9642 : row9642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9642 := by decide +kernel

theorem rowEval9642 (x : Key → ℝ) : Integer.Sparse.eval row9642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9642, Integer.Sparse.eval_collectBalanced, rawRowCheck9642]

def rawRow9643 : Integer.Sparse Key := [(key2976, -2), (key2983, -2), (key2972, -2), (key2976, -2), (key2983, -2), (key2641, -2), (key2728, -2), (key2628, -2), (key2702, -2), (key2972, -2), (key2628, -2), (key2702, -2), (key2998, 1), (key3000, 1), (key2943, 1), (key2960, 1), (key2936, 1), (key2948, 1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2943, 1), (key2960, 1), (key2653, 1), (key2747, 1), (key2612, 1), (key2667, 1), (key2726, 1), (key2829, 1), (key2640, 1), (key2794, 1), (key2616, 1), (key2671, 1)]

theorem rawRowCheck9643 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form5 = rawRow9643 := by decide +kernel

def row9643 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

theorem rowCheck9643 : row9643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9643 := by decide +kernel

theorem rowEval9643 (x : Key → ℝ) : Integer.Sparse.eval row9643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9643, Integer.Sparse.eval_collectBalanced, rawRowCheck9643]

def rawRow9644 : Integer.Sparse Key := [(key2983, -2), (key2976, -2), (key2972, -2), (key2983, -2), (key2976, -2), (key2728, -2), (key2641, -2), (key2702, -2), (key2628, -2), (key2972, -2), (key2702, -2), (key2628, -2), (key3000, 1), (key2998, 1), (key2960, 1), (key2943, 1), (key2948, 1), (key2936, 1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2960, 1), (key2943, 1), (key2747, 1), (key2653, 1), (key2667, 1), (key2612, 1), (key2829, 1), (key2726, 1), (key2794, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

theorem rawRowCheck9644 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form5 = rawRow9644 := by decide +kernel

def row9644 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2702, -4), (key2726, 1), (key2728, -2), (key2735, 1), (key2747, 2), (key2794, 1), (key2829, 1), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2972, -4), (key2976, -4), (key2983, -4), (key2998, 2), (key3000, 2)]

theorem rowCheck9644 : row9644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9644 := by decide +kernel

theorem rowEval9644 (x : Key → ℝ) : Integer.Sparse.eval row9644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck9644, Integer.Sparse.eval_collectBalanced, rawRowCheck9644]

def rawRow9645 : Integer.Sparse Key := [(key2769, -24), (key2590, 6), (key2846, 6), (key2877, 6), (key2877, 6)]

theorem rawRowCheck9645 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form6 = rawRow9645 := by decide +kernel

def row9645 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9645 : row9645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9645 := by decide +kernel

theorem rowEval9645 (x : Key → ℝ) : Integer.Sparse.eval row9645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9645, Integer.Sparse.eval_collectBalanced, rawRowCheck9645]

def rawRow9646 : Integer.Sparse Key := [(key2769, -24), (key2590, 6), (key2877, 6), (key2846, 6), (key2877, 6)]

theorem rawRowCheck9646 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form6 = rawRow9646 := by decide +kernel

def row9646 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9646 : row9646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9646 := by decide +kernel

theorem rowEval9646 (x : Key → ℝ) : Integer.Sparse.eval row9646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9646, Integer.Sparse.eval_collectBalanced, rawRowCheck9646]

def rawRow9647 : Integer.Sparse Key := [(key2769, -24), (key2590, 6), (key2877, 6), (key2877, 6), (key2846, 6)]

theorem rawRowCheck9647 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form6 = rawRow9647 := by decide +kernel

def row9647 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9647 : row9647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9647 := by decide +kernel

theorem rowEval9647 (x : Key → ℝ) : Integer.Sparse.eval row9647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9647, Integer.Sparse.eval_collectBalanced, rawRowCheck9647]

def rawRow9648 : Integer.Sparse Key := [(key2769, -24), (key2846, 6), (key2590, 6), (key2877, 6), (key2877, 6)]

theorem rawRowCheck9648 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form6 = rawRow9648 := by decide +kernel

def row9648 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9648 : row9648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9648 := by decide +kernel

theorem rowEval9648 (x : Key → ℝ) : Integer.Sparse.eval row9648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9648, Integer.Sparse.eval_collectBalanced, rawRowCheck9648]

def rawRow9649 : Integer.Sparse Key := [(key2769, -24), (key2846, 6), (key2877, 6), (key2590, 6), (key2877, 6)]

theorem rawRowCheck9649 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form6 = rawRow9649 := by decide +kernel

def row9649 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9649 : row9649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9649 := by decide +kernel

theorem rowEval9649 (x : Key → ℝ) : Integer.Sparse.eval row9649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9649, Integer.Sparse.eval_collectBalanced, rawRowCheck9649]

def rawRow9650 : Integer.Sparse Key := [(key2769, -24), (key2846, 6), (key2877, 6), (key2877, 6), (key2590, 6)]

theorem rawRowCheck9650 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form6 = rawRow9650 := by decide +kernel

def row9650 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9650 : row9650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9650 := by decide +kernel

theorem rowEval9650 (x : Key → ℝ) : Integer.Sparse.eval row9650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9650, Integer.Sparse.eval_collectBalanced, rawRowCheck9650]

def rawRow9651 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2590, 6), (key2846, 6), (key2877, 6)]

theorem rawRowCheck9651 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form6 = rawRow9651 := by decide +kernel

def row9651 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9651 : row9651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9651 := by decide +kernel

theorem rowEval9651 (x : Key → ℝ) : Integer.Sparse.eval row9651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9651, Integer.Sparse.eval_collectBalanced, rawRowCheck9651]

def rawRow9652 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2590, 6), (key2877, 6), (key2846, 6)]

theorem rawRowCheck9652 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form6 = rawRow9652 := by decide +kernel

def row9652 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9652 : row9652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9652 := by decide +kernel

theorem rowEval9652 (x : Key → ℝ) : Integer.Sparse.eval row9652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9652, Integer.Sparse.eval_collectBalanced, rawRowCheck9652]

def rawRow9653 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2846, 6), (key2590, 6), (key2877, 6)]

theorem rawRowCheck9653 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form6 = rawRow9653 := by decide +kernel

def row9653 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9653 : row9653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9653 := by decide +kernel

theorem rowEval9653 (x : Key → ℝ) : Integer.Sparse.eval row9653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9653, Integer.Sparse.eval_collectBalanced, rawRowCheck9653]

def rawRow9654 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2846, 6), (key2877, 6), (key2590, 6)]

theorem rawRowCheck9654 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form6 = rawRow9654 := by decide +kernel

def row9654 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9654 : row9654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9654 := by decide +kernel

theorem rowEval9654 (x : Key → ℝ) : Integer.Sparse.eval row9654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9654, Integer.Sparse.eval_collectBalanced, rawRowCheck9654]

def rawRow9655 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2877, 6), (key2590, 6), (key2846, 6)]

theorem rawRowCheck9655 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form6 = rawRow9655 := by decide +kernel

def row9655 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9655 : row9655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9655 := by decide +kernel

theorem rowEval9655 (x : Key → ℝ) : Integer.Sparse.eval row9655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9655, Integer.Sparse.eval_collectBalanced, rawRowCheck9655]

def rawRow9656 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2877, 6), (key2846, 6), (key2590, 6)]

theorem rawRowCheck9656 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form6 = rawRow9656 := by decide +kernel

def row9656 : Integer.Sparse Key := [(key2590, 6), (key2769, -24), (key2846, 6), (key2877, 12)]

theorem rowCheck9656 : row9656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9656 := by decide +kernel

theorem rowEval9656 (x : Key → ℝ) : Integer.Sparse.eval row9656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9656, Integer.Sparse.eval_collectBalanced, rawRowCheck9656]

def rawRow9657 : Integer.Sparse Key := [(key2846, -24), (key2590, 6), (key2769, 6), (key2877, 6), (key2877, 6)]

theorem rawRowCheck9657 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form6 = rawRow9657 := by decide +kernel

def row9657 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9657 : row9657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9657 := by decide +kernel

theorem rowEval9657 (x : Key → ℝ) : Integer.Sparse.eval row9657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9657, Integer.Sparse.eval_collectBalanced, rawRowCheck9657]

def rawRow9658 : Integer.Sparse Key := [(key2846, -24), (key2590, 6), (key2877, 6), (key2769, 6), (key2877, 6)]

theorem rawRowCheck9658 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form6 = rawRow9658 := by decide +kernel

def row9658 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9658 : row9658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9658 := by decide +kernel

theorem rowEval9658 (x : Key → ℝ) : Integer.Sparse.eval row9658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9658, Integer.Sparse.eval_collectBalanced, rawRowCheck9658]

def rawRow9659 : Integer.Sparse Key := [(key2846, -24), (key2590, 6), (key2877, 6), (key2877, 6), (key2769, 6)]

theorem rawRowCheck9659 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form6 = rawRow9659 := by decide +kernel

def row9659 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9659 : row9659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9659 := by decide +kernel

theorem rowEval9659 (x : Key → ℝ) : Integer.Sparse.eval row9659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9659, Integer.Sparse.eval_collectBalanced, rawRowCheck9659]

def rawRow9660 : Integer.Sparse Key := [(key2846, -24), (key2769, 6), (key2590, 6), (key2877, 6), (key2877, 6)]

theorem rawRowCheck9660 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form6 = rawRow9660 := by decide +kernel

def row9660 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9660 : row9660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9660 := by decide +kernel

theorem rowEval9660 (x : Key → ℝ) : Integer.Sparse.eval row9660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9660, Integer.Sparse.eval_collectBalanced, rawRowCheck9660]

def rawRow9661 : Integer.Sparse Key := [(key2846, -24), (key2769, 6), (key2877, 6), (key2590, 6), (key2877, 6)]

theorem rawRowCheck9661 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form6 = rawRow9661 := by decide +kernel

def row9661 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9661 : row9661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9661 := by decide +kernel

theorem rowEval9661 (x : Key → ℝ) : Integer.Sparse.eval row9661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9661, Integer.Sparse.eval_collectBalanced, rawRowCheck9661]

def rawRow9662 : Integer.Sparse Key := [(key2846, -24), (key2769, 6), (key2877, 6), (key2877, 6), (key2590, 6)]

theorem rawRowCheck9662 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form6 = rawRow9662 := by decide +kernel

def row9662 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9662 : row9662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9662 := by decide +kernel

theorem rowEval9662 (x : Key → ℝ) : Integer.Sparse.eval row9662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9662, Integer.Sparse.eval_collectBalanced, rawRowCheck9662]

def rawRow9663 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2590, 6), (key2769, 6), (key2877, 6)]

theorem rawRowCheck9663 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form6 = rawRow9663 := by decide +kernel

def row9663 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9663 : row9663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9663 := by decide +kernel

theorem rowEval9663 (x : Key → ℝ) : Integer.Sparse.eval row9663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9663, Integer.Sparse.eval_collectBalanced, rawRowCheck9663]

def rawRow9664 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2590, 6), (key2877, 6), (key2769, 6)]

theorem rawRowCheck9664 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form6 = rawRow9664 := by decide +kernel

def row9664 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9664 : row9664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9664 := by decide +kernel

theorem rowEval9664 (x : Key → ℝ) : Integer.Sparse.eval row9664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9664, Integer.Sparse.eval_collectBalanced, rawRowCheck9664]

def rawRow9665 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2769, 6), (key2590, 6), (key2877, 6)]

theorem rawRowCheck9665 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form6 = rawRow9665 := by decide +kernel

def row9665 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9665 : row9665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9665 := by decide +kernel

theorem rowEval9665 (x : Key → ℝ) : Integer.Sparse.eval row9665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9665, Integer.Sparse.eval_collectBalanced, rawRowCheck9665]

def rawRow9666 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2769, 6), (key2877, 6), (key2590, 6)]

theorem rawRowCheck9666 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form6 = rawRow9666 := by decide +kernel

def row9666 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9666 : row9666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9666 := by decide +kernel

theorem rowEval9666 (x : Key → ℝ) : Integer.Sparse.eval row9666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9666, Integer.Sparse.eval_collectBalanced, rawRowCheck9666]

def rawRow9667 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2877, 6), (key2590, 6), (key2769, 6)]

theorem rawRowCheck9667 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form6 = rawRow9667 := by decide +kernel

def row9667 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9667 : row9667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9667 := by decide +kernel

theorem rowEval9667 (x : Key → ℝ) : Integer.Sparse.eval row9667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9667, Integer.Sparse.eval_collectBalanced, rawRowCheck9667]

def rawRow9668 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2877, 6), (key2769, 6), (key2590, 6)]

theorem rawRowCheck9668 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form6 = rawRow9668 := by decide +kernel

def row9668 : Integer.Sparse Key := [(key2590, 6), (key2769, 6), (key2846, -24), (key2877, 12)]

theorem rowCheck9668 : row9668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9668 := by decide +kernel

theorem rowEval9668 (x : Key → ℝ) : Integer.Sparse.eval row9668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck9668, Integer.Sparse.eval_collectBalanced, rawRowCheck9668]

def rawRow9669 : Integer.Sparse Key := [(key2667, -2), (key2667, -2), (key2673, -2), (key2702, -2), (key2702, -2), (key2735, -2), (key2735, -2), (key2737, -2), (key2737, -2), (key2728, -2), (key2747, -2), (key2747, -2), (key2612, 2), (key2616, 2), (key2621, 2), (key2809, 2), (key2809, 2), (key2829, 2), (key2829, 2), (key2835, 2), (key2835, 2), (key3012, 2), (key3017, 2), (key3017, 2)]

theorem rawRowCheck9669 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form7 = rawRow9669 := by decide +kernel

def row9669 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2809, 4), (key2829, 4), (key2835, 4), (key3012, 2), (key3017, 4)]

theorem rowCheck9669 : row9669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9669 := by decide +kernel

theorem rowEval9669 (x : Key → ℝ) : Integer.Sparse.eval row9669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9669, Integer.Sparse.eval_collectBalanced, rawRowCheck9669]

def rawRow9670 : Integer.Sparse Key := [(key2667, -2), (key2673, -2), (key2667, -2), (key2735, -2), (key2737, -2), (key2702, -2), (key2737, -2), (key2702, -2), (key2735, -2), (key2747, -2), (key2728, -2), (key2747, -2), (key2612, 2), (key2618, 2), (key2616, 2), (key2829, 2), (key2835, 2), (key2809, 2), (key2835, 2), (key2809, 2), (key2829, 2), (key3017, 2), (key3012, 2), (key3017, 2)]

theorem rawRowCheck9670 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form7 = rawRow9670 := by decide +kernel

def row9670 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2809, 4), (key2829, 4), (key2835, 4), (key3012, 2), (key3017, 4)]

theorem rowCheck9670 : row9670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9670 := by decide +kernel

theorem rowEval9670 (x : Key → ℝ) : Integer.Sparse.eval row9670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9670, Integer.Sparse.eval_collectBalanced, rawRowCheck9670]

def rawRow9671 : Integer.Sparse Key := [(key2673, -2), (key2667, -2), (key2667, -2), (key2737, -2), (key2735, -2), (key2737, -2), (key2702, -2), (key2735, -2), (key2702, -2), (key2747, -2), (key2747, -2), (key2728, -2), (key2618, 2), (key2612, 2), (key2616, 2), (key2835, 2), (key2829, 2), (key2835, 2), (key2809, 2), (key2829, 2), (key2809, 2), (key3017, 2), (key3017, 2), (key3012, 2)]

theorem rawRowCheck9671 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form7 = rawRow9671 := by decide +kernel

def row9671 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2809, 4), (key2829, 4), (key2835, 4), (key3012, 2), (key3017, 4)]

theorem rowCheck9671 : row9671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9671 := by decide +kernel

theorem rowEval9671 (x : Key → ℝ) : Integer.Sparse.eval row9671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9671, Integer.Sparse.eval_collectBalanced, rawRowCheck9671]

def rawRow9672 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2667, -2), (key2667, -2), (key2735, -2), (key2735, -2), (key2747, -2), (key2747, -2), (key2673, -2), (key2737, -2), (key2737, -2), (key2805, 2), (key2805, 2), (key2831, 2), (key2612, 2), (key2616, 2), (key2829, 2), (key2829, 2), (key3017, 2), (key3017, 2), (key2621, 2), (key2835, 2), (key2835, 2)]

theorem rawRowCheck9672 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form7 = rawRow9672 := by decide +kernel

def row9672 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 4), (key2829, 4), (key2831, 2), (key2835, 4), (key3017, 4)]

theorem rowCheck9672 : row9672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9672 := by decide +kernel

theorem rowEval9672 (x : Key → ℝ) : Integer.Sparse.eval row9672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9672, Integer.Sparse.eval_collectBalanced, rawRowCheck9672]

def rawRow9673 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2735, -2), (key2747, -2), (key2667, -2), (key2747, -2), (key2667, -2), (key2735, -2), (key2737, -2), (key2673, -2), (key2737, -2), (key2805, 2), (key2831, 2), (key2805, 2), (key2948, 2), (key2960, 2), (key2612, 2), (key2960, 2), (key2616, 2), (key2829, 2), (key2835, 2), (key2621, 2), (key2835, 2)]

theorem rawRowCheck9673 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form7 = rawRow9673 := by decide +kernel

def row9673 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 4), (key2829, 2), (key2831, 2), (key2835, 4), (key2948, 2), (key2960, 4)]

theorem rowCheck9673 : row9673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9673 := by decide +kernel

theorem rowEval9673 (x : Key → ℝ) : Integer.Sparse.eval row9673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9673, Integer.Sparse.eval_collectBalanced, rawRowCheck9673]

def rawRow9674 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2747, -2), (key2735, -2), (key2747, -2), (key2667, -2), (key2735, -2), (key2667, -2), (key2737, -2), (key2737, -2), (key2673, -2), (key2831, 2), (key2805, 2), (key2805, 2), (key2960, 2), (key2948, 2), (key2960, 2), (key2612, 2), (key2829, 2), (key2616, 2), (key2835, 2), (key2835, 2), (key2621, 2)]

theorem rawRowCheck9674 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form7 = rawRow9674 := by decide +kernel

def row9674 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 4), (key2829, 2), (key2831, 2), (key2835, 4), (key2948, 2), (key2960, 4)]

theorem rowCheck9674 : row9674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9674 := by decide +kernel

theorem rowEval9674 (x : Key → ℝ) : Integer.Sparse.eval row9674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9674, Integer.Sparse.eval_collectBalanced, rawRowCheck9674]

def rawRow9675 : Integer.Sparse Key := [(key2735, -2), (key2737, -2), (key2747, -2), (key2667, -2), (key2673, -2), (key2702, -2), (key2737, -2), (key2728, -2), (key2747, -2), (key2667, -2), (key2702, -2), (key2735, -2), (key2948, 2), (key2950, 2), (key2960, 2), (key2612, 2), (key2618, 2), (key2805, 2), (key2950, 2), (key2831, 2), (key2960, 2), (key2616, 2), (key2809, 2), (key2829, 2)]

theorem rawRowCheck9675 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form7 = rawRow9675 := by decide +kernel

def row9675 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

theorem rowCheck9675 : row9675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9675 := by decide +kernel

theorem rowEval9675 (x : Key → ℝ) : Integer.Sparse.eval row9675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9675, Integer.Sparse.eval_collectBalanced, rawRowCheck9675]

def rawRow9676 : Integer.Sparse Key := [(key2737, -2), (key2735, -2), (key2747, -2), (key2673, -2), (key2667, -2), (key2737, -2), (key2702, -2), (key2747, -2), (key2728, -2), (key2667, -2), (key2735, -2), (key2702, -2), (key2950, 2), (key2948, 2), (key2960, 2), (key2618, 2), (key2612, 2), (key2950, 2), (key2805, 2), (key2960, 2), (key2831, 2), (key2616, 2), (key2829, 2), (key2809, 2)]

theorem rawRowCheck9676 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form7 = rawRow9676 := by decide +kernel

def row9676 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

theorem rowCheck9676 : row9676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9676 := by decide +kernel

theorem rowEval9676 (x : Key → ℝ) : Integer.Sparse.eval row9676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9676, Integer.Sparse.eval_collectBalanced, rawRowCheck9676]

def rawRow9677 : Integer.Sparse Key := [(key2735, -2), (key2747, -2), (key2737, -2), (key2702, -2), (key2728, -2), (key2667, -2), (key2747, -2), (key2673, -2), (key2737, -2), (key2702, -2), (key2667, -2), (key2735, -2), (key2948, 2), (key2960, 2), (key2950, 2), (key2805, 2), (key2831, 2), (key2612, 2), (key2960, 2), (key2618, 2), (key2950, 2), (key2809, 2), (key2616, 2), (key2829, 2)]

theorem rawRowCheck9677 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form7 = rawRow9677 := by decide +kernel

def row9677 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

theorem rowCheck9677 : row9677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9677 := by decide +kernel

theorem rowEval9677 (x : Key → ℝ) : Integer.Sparse.eval row9677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9677, Integer.Sparse.eval_collectBalanced, rawRowCheck9677]

def rawRow9678 : Integer.Sparse Key := [(key2747, -2), (key2735, -2), (key2737, -2), (key2728, -2), (key2702, -2), (key2747, -2), (key2667, -2), (key2737, -2), (key2673, -2), (key2702, -2), (key2735, -2), (key2667, -2), (key2960, 2), (key2948, 2), (key2950, 2), (key2831, 2), (key2805, 2), (key2960, 2), (key2612, 2), (key2950, 2), (key2618, 2), (key2809, 2), (key2829, 2), (key2616, 2)]

theorem rawRowCheck9678 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form7 = rawRow9678 := by decide +kernel

def row9678 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

theorem rowCheck9678 : row9678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9678 := by decide +kernel

theorem rowEval9678 (x : Key → ℝ) : Integer.Sparse.eval row9678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9678, Integer.Sparse.eval_collectBalanced, rawRowCheck9678]

def rawRow9679 : Integer.Sparse Key := [(key2737, -2), (key2747, -2), (key2735, -2), (key2737, -2), (key2747, -2), (key2673, -2), (key2728, -2), (key2667, -2), (key2702, -2), (key2735, -2), (key2667, -2), (key2702, -2), (key2950, 2), (key2960, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2618, 2), (key2831, 2), (key2612, 2), (key2805, 2), (key2829, 2), (key2616, 2), (key2809, 2)]

theorem rawRowCheck9679 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form7 = rawRow9679 := by decide +kernel

def row9679 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

theorem rowCheck9679 : row9679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9679 := by decide +kernel

theorem rowEval9679 (x : Key → ℝ) : Integer.Sparse.eval row9679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9679, Integer.Sparse.eval_collectBalanced, rawRowCheck9679]

def rawRow9680 : Integer.Sparse Key := [(key2747, -2), (key2737, -2), (key2735, -2), (key2747, -2), (key2737, -2), (key2728, -2), (key2673, -2), (key2702, -2), (key2667, -2), (key2735, -2), (key2702, -2), (key2667, -2), (key2960, 2), (key2950, 2), (key2948, 2), (key2960, 2), (key2950, 2), (key2831, 2), (key2618, 2), (key2805, 2), (key2612, 2), (key2829, 2), (key2809, 2), (key2616, 2)]

theorem rawRowCheck9680 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form7 = rawRow9680 := by decide +kernel

def row9680 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2667, -4), (key2673, -2), (key2702, -4), (key2728, -2), (key2735, -4), (key2737, -4), (key2747, -4), (key2805, 2), (key2809, 2), (key2829, 2), (key2831, 2), (key2948, 2), (key2950, 4), (key2960, 4)]

theorem rowCheck9680 : row9680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9680 := by decide +kernel

theorem rowEval9680 (x : Key → ℝ) : Integer.Sparse.eval row9680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9680, Integer.Sparse.eval_collectBalanced, rawRowCheck9680]

def rawRow9681 : Integer.Sparse Key := [(key2782, -2), (key2782, -2), (key2795, -2), (key2805, -2), (key2805, -2), (key2893, -2), (key2893, -2), (key2897, -2), (key2897, -2), (key2831, -2), (key2904, -2), (key2904, -2), (key2628, 2), (key2628, 2), (key2641, 2), (key2702, 2), (key2702, 2), (key2972, 2), (key2972, 2), (key2976, 2), (key2976, 2), (key2728, 2), (key2983, 2), (key2983, 2)]

theorem rawRowCheck9681 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form7 = rawRow9681 := by decide +kernel

def row9681 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9681 : row9681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9681 := by decide +kernel

theorem rowEval9681 (x : Key → ℝ) : Integer.Sparse.eval row9681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9681, Integer.Sparse.eval_collectBalanced, rawRowCheck9681]

def rawRow9682 : Integer.Sparse Key := [(key2782, -2), (key2795, -2), (key2782, -2), (key2893, -2), (key2897, -2), (key2805, -2), (key2897, -2), (key2805, -2), (key2893, -2), (key2904, -2), (key2831, -2), (key2904, -2), (key2628, 2), (key2641, 2), (key2628, 2), (key2972, 2), (key2976, 2), (key2702, 2), (key2976, 2), (key2702, 2), (key2972, 2), (key2983, 2), (key2728, 2), (key2983, 2)]

theorem rawRowCheck9682 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form7 = rawRow9682 := by decide +kernel

def row9682 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9682 : row9682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9682 := by decide +kernel

theorem rowEval9682 (x : Key → ℝ) : Integer.Sparse.eval row9682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9682, Integer.Sparse.eval_collectBalanced, rawRowCheck9682]

def rawRow9683 : Integer.Sparse Key := [(key2795, -2), (key2782, -2), (key2782, -2), (key2897, -2), (key2893, -2), (key2897, -2), (key2805, -2), (key2893, -2), (key2805, -2), (key2904, -2), (key2904, -2), (key2831, -2), (key2641, 2), (key2628, 2), (key2628, 2), (key2976, 2), (key2972, 2), (key2976, 2), (key2702, 2), (key2972, 2), (key2702, 2), (key2983, 2), (key2983, 2), (key2728, 2)]

theorem rawRowCheck9683 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form7 = rawRow9683 := by decide +kernel

def row9683 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9683 : row9683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9683 := by decide +kernel

theorem rowEval9683 (x : Key → ℝ) : Integer.Sparse.eval row9683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9683, Integer.Sparse.eval_collectBalanced, rawRowCheck9683]

def rawRow9684 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2782, -2), (key2782, -2), (key2893, -2), (key2893, -2), (key2904, -2), (key2904, -2), (key2795, -2), (key2897, -2), (key2897, -2), (key2702, 2), (key2702, 2), (key2728, 2), (key2628, 2), (key2628, 2), (key2972, 2), (key2972, 2), (key2983, 2), (key2983, 2), (key2641, 2), (key2976, 2), (key2976, 2)]

theorem rawRowCheck9684 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form7 = rawRow9684 := by decide +kernel

def row9684 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9684 : row9684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9684 := by decide +kernel

theorem rowEval9684 (x : Key → ℝ) : Integer.Sparse.eval row9684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9684, Integer.Sparse.eval_collectBalanced, rawRowCheck9684]

def rawRow9685 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2893, -2), (key2904, -2), (key2782, -2), (key2904, -2), (key2782, -2), (key2893, -2), (key2897, -2), (key2795, -2), (key2897, -2), (key2702, 2), (key2728, 2), (key2702, 2), (key2972, 2), (key2983, 2), (key2628, 2), (key2983, 2), (key2628, 2), (key2972, 2), (key2976, 2), (key2641, 2), (key2976, 2)]

theorem rawRowCheck9685 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form7 = rawRow9685 := by decide +kernel

def row9685 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9685 : row9685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9685 := by decide +kernel

theorem rowEval9685 (x : Key → ℝ) : Integer.Sparse.eval row9685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9685, Integer.Sparse.eval_collectBalanced, rawRowCheck9685]

def rawRow9686 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2904, -2), (key2893, -2), (key2904, -2), (key2782, -2), (key2893, -2), (key2782, -2), (key2897, -2), (key2897, -2), (key2795, -2), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, 2), (key2972, 2), (key2983, 2), (key2628, 2), (key2972, 2), (key2628, 2), (key2976, 2), (key2976, 2), (key2641, 2)]

theorem rawRowCheck9686 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form7 = rawRow9686 := by decide +kernel

def row9686 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9686 : row9686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9686 := by decide +kernel

theorem rowEval9686 (x : Key → ℝ) : Integer.Sparse.eval row9686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9686, Integer.Sparse.eval_collectBalanced, rawRowCheck9686]

def rawRow9687 : Integer.Sparse Key := [(key2893, -2), (key2897, -2), (key2904, -2), (key2782, -2), (key2795, -2), (key2805, -2), (key2897, -2), (key2831, -2), (key2904, -2), (key2782, -2), (key2805, -2), (key2893, -2), (key2972, 2), (key2976, 2), (key2983, 2), (key2628, 2), (key2641, 2), (key2702, 2), (key2976, 2), (key2728, 2), (key2983, 2), (key2628, 2), (key2702, 2), (key2972, 2)]

theorem rawRowCheck9687 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form7 = rawRow9687 := by decide +kernel

def row9687 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9687 : row9687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9687 := by decide +kernel

theorem rowEval9687 (x : Key → ℝ) : Integer.Sparse.eval row9687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9687, Integer.Sparse.eval_collectBalanced, rawRowCheck9687]

def rawRow9688 : Integer.Sparse Key := [(key2897, -2), (key2893, -2), (key2904, -2), (key2795, -2), (key2782, -2), (key2897, -2), (key2805, -2), (key2904, -2), (key2831, -2), (key2782, -2), (key2893, -2), (key2805, -2), (key2976, 2), (key2972, 2), (key2983, 2), (key2641, 2), (key2628, 2), (key2976, 2), (key2702, 2), (key2983, 2), (key2728, 2), (key2628, 2), (key2972, 2), (key2702, 2)]

theorem rawRowCheck9688 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form7 = rawRow9688 := by decide +kernel

def row9688 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9688 : row9688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9688 := by decide +kernel

theorem rowEval9688 (x : Key → ℝ) : Integer.Sparse.eval row9688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9688, Integer.Sparse.eval_collectBalanced, rawRowCheck9688]

def rawRow9689 : Integer.Sparse Key := [(key2893, -2), (key2904, -2), (key2897, -2), (key2805, -2), (key2831, -2), (key2782, -2), (key2904, -2), (key2795, -2), (key2897, -2), (key2805, -2), (key2782, -2), (key2893, -2), (key2972, 2), (key2983, 2), (key2976, 2), (key2702, 2), (key2728, 2), (key2628, 2), (key2983, 2), (key2641, 2), (key2976, 2), (key2702, 2), (key2628, 2), (key2972, 2)]

theorem rawRowCheck9689 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form7 = rawRow9689 := by decide +kernel

def row9689 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9689 : row9689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9689 := by decide +kernel

theorem rowEval9689 (x : Key → ℝ) : Integer.Sparse.eval row9689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9689, Integer.Sparse.eval_collectBalanced, rawRowCheck9689]

def rawRow9690 : Integer.Sparse Key := [(key2904, -2), (key2893, -2), (key2897, -2), (key2831, -2), (key2805, -2), (key2904, -2), (key2782, -2), (key2897, -2), (key2795, -2), (key2805, -2), (key2893, -2), (key2782, -2), (key2983, 2), (key2972, 2), (key2976, 2), (key2728, 2), (key2702, 2), (key2983, 2), (key2628, 2), (key2976, 2), (key2641, 2), (key2702, 2), (key2972, 2), (key2628, 2)]

theorem rawRowCheck9690 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form7 = rawRow9690 := by decide +kernel

def row9690 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9690 : row9690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9690 := by decide +kernel

theorem rowEval9690 (x : Key → ℝ) : Integer.Sparse.eval row9690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9690, Integer.Sparse.eval_collectBalanced, rawRowCheck9690]

def rawRow9691 : Integer.Sparse Key := [(key2897, -2), (key2904, -2), (key2893, -2), (key2897, -2), (key2904, -2), (key2795, -2), (key2831, -2), (key2782, -2), (key2805, -2), (key2893, -2), (key2782, -2), (key2805, -2), (key2976, 2), (key2983, 2), (key2972, 2), (key2976, 2), (key2983, 2), (key2641, 2), (key2728, 2), (key2628, 2), (key2702, 2), (key2972, 2), (key2628, 2), (key2702, 2)]

theorem rawRowCheck9691 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form7 = rawRow9691 := by decide +kernel

def row9691 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9691 : row9691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9691 := by decide +kernel

theorem rowEval9691 (x : Key → ℝ) : Integer.Sparse.eval row9691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9691, Integer.Sparse.eval_collectBalanced, rawRowCheck9691]

def rawRow9692 : Integer.Sparse Key := [(key2904, -2), (key2897, -2), (key2893, -2), (key2904, -2), (key2897, -2), (key2831, -2), (key2795, -2), (key2805, -2), (key2782, -2), (key2893, -2), (key2805, -2), (key2782, -2), (key2983, 2), (key2976, 2), (key2972, 2), (key2983, 2), (key2976, 2), (key2728, 2), (key2641, 2), (key2702, 2), (key2628, 2), (key2972, 2), (key2702, 2), (key2628, 2)]

theorem rawRowCheck9692 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form7 = rawRow9692 := by decide +kernel

def row9692 : Integer.Sparse Key := [(key2628, 4), (key2641, 2), (key2702, 4), (key2728, 2), (key2782, -4), (key2795, -2), (key2805, -4), (key2831, -2), (key2893, -4), (key2897, -4), (key2904, -4), (key2972, 4), (key2976, 4), (key2983, 4)]

theorem rowCheck9692 : row9692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9692 := by decide +kernel

theorem rowEval9692 (x : Key → ℝ) : Integer.Sparse.eval row9692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck9692, Integer.Sparse.eval_collectBalanced, rawRowCheck9692]

def rawRow9693 : Integer.Sparse Key := [(key1296, -2), (key1296, -2), (key1303, -2), (key1573, -2), (key1573, -2), (key1788, -2), (key1788, -2), (key1791, -2), (key1791, -2), (key1597, -2), (key1799, -2), (key1799, -2), (key1316, 1), (key1316, 1), (key1337, 1), (key1337, 1), (key1340, 1), (key1340, 1), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1775, 1), (key1775, 1), (key1655, 1), (key1655, 1), (key1813, 1), (key1813, 1), (key1840, 1), (key1840, 1), (key1668, 1), (key1668, 1), (key1826, 1), (key1826, 1), (key1845, 1), (key1845, 1)]

theorem rawRowCheck9693 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form8 = rawRow9693 := by decide +kernel

def row9693 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9693 : row9693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9693 := by decide +kernel

theorem rowEval9693 (x : Key → ℝ) : Integer.Sparse.eval row9693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9693, Integer.Sparse.eval_collectBalanced, rawRowCheck9693]

def rawRow9694 : Integer.Sparse Key := [(key1296, -2), (key1303, -2), (key1296, -2), (key1788, -2), (key1791, -2), (key1573, -2), (key1791, -2), (key1573, -2), (key1788, -2), (key1799, -2), (key1597, -2), (key1799, -2), (key1337, 1), (key1340, 1), (key1316, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1813, 1), (key1840, 1), (key1655, 1), (key1840, 1), (key1655, 1), (key1813, 1), (key1826, 1), (key1845, 1), (key1668, 1), (key1845, 1), (key1668, 1), (key1826, 1)]

theorem rawRowCheck9694 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form8 = rawRow9694 := by decide +kernel

def row9694 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9694 : row9694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9694 := by decide +kernel

theorem rowEval9694 (x : Key → ℝ) : Integer.Sparse.eval row9694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9694, Integer.Sparse.eval_collectBalanced, rawRowCheck9694]

def rawRow9695 : Integer.Sparse Key := [(key1303, -2), (key1296, -2), (key1296, -2), (key1791, -2), (key1788, -2), (key1791, -2), (key1573, -2), (key1788, -2), (key1573, -2), (key1799, -2), (key1799, -2), (key1597, -2), (key1340, 1), (key1337, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1316, 1), (key1775, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1546, 1), (key1840, 1), (key1813, 1), (key1840, 1), (key1655, 1), (key1813, 1), (key1655, 1), (key1845, 1), (key1826, 1), (key1845, 1), (key1668, 1), (key1826, 1), (key1668, 1)]

theorem rawRowCheck9695 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form8 = rawRow9695 := by decide +kernel

def row9695 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9695 : row9695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9695 := by decide +kernel

theorem rowEval9695 (x : Key → ℝ) : Integer.Sparse.eval row9695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9695, Integer.Sparse.eval_collectBalanced, rawRowCheck9695]

def rawRow9696 : Integer.Sparse Key := [(key1573, -2), (key1573, -2), (key1597, -2), (key1296, -2), (key1296, -2), (key1788, -2), (key1788, -2), (key1799, -2), (key1799, -2), (key1303, -2), (key1791, -2), (key1791, -2), (key1546, 1), (key1546, 1), (key1655, 1), (key1655, 1), (key1668, 1), (key1668, 1), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1826, 1), (key1826, 1), (key1337, 1), (key1337, 1), (key1772, 1), (key1772, 1), (key1845, 1), (key1845, 1), (key1340, 1), (key1340, 1), (key1775, 1), (key1775, 1), (key1840, 1), (key1840, 1)]

theorem rawRowCheck9696 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form8 = rawRow9696 := by decide +kernel

def row9696 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9696 : row9696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9696 := by decide +kernel

theorem rowEval9696 (x : Key → ℝ) : Integer.Sparse.eval row9696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9696, Integer.Sparse.eval_collectBalanced, rawRowCheck9696]

def rawRow9697 : Integer.Sparse Key := [(key1573, -2), (key1597, -2), (key1573, -2), (key1788, -2), (key1799, -2), (key1296, -2), (key1799, -2), (key1296, -2), (key1788, -2), (key1791, -2), (key1303, -2), (key1791, -2), (key1655, 1), (key1668, 1), (key1546, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1772, 1), (key1845, 1), (key1337, 1), (key1845, 1), (key1337, 1), (key1772, 1), (key1775, 1), (key1840, 1), (key1340, 1), (key1840, 1), (key1340, 1), (key1775, 1)]

theorem rawRowCheck9697 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form8 = rawRow9697 := by decide +kernel

def row9697 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9697 : row9697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9697 := by decide +kernel

theorem rowEval9697 (x : Key → ℝ) : Integer.Sparse.eval row9697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9697, Integer.Sparse.eval_collectBalanced, rawRowCheck9697]

def rawRow9698 : Integer.Sparse Key := [(key1597, -2), (key1573, -2), (key1573, -2), (key1799, -2), (key1788, -2), (key1799, -2), (key1296, -2), (key1788, -2), (key1296, -2), (key1791, -2), (key1791, -2), (key1303, -2), (key1668, 1), (key1655, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1546, 1), (key1826, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1845, 1), (key1772, 1), (key1845, 1), (key1337, 1), (key1772, 1), (key1337, 1), (key1840, 1), (key1775, 1), (key1840, 1), (key1340, 1), (key1775, 1), (key1340, 1)]

theorem rawRowCheck9698 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form8 = rawRow9698 := by decide +kernel

def row9698 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9698 : row9698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9698 := by decide +kernel

theorem rowEval9698 (x : Key → ℝ) : Integer.Sparse.eval row9698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9698, Integer.Sparse.eval_collectBalanced, rawRowCheck9698]

def rawRow9699 : Integer.Sparse Key := [(key1788, -2), (key1791, -2), (key1799, -2), (key1296, -2), (key1303, -2), (key1573, -2), (key1791, -2), (key1597, -2), (key1799, -2), (key1296, -2), (key1573, -2), (key1788, -2), (key1772, 1), (key1775, 1), (key1813, 1), (key1840, 1), (key1826, 1), (key1845, 1), (key1337, 1), (key1340, 1), (key1655, 1), (key1840, 1), (key1668, 1), (key1845, 1), (key1316, 1), (key1340, 1), (key1546, 1), (key1775, 1), (key1668, 1), (key1826, 1), (key1316, 1), (key1337, 1), (key1546, 1), (key1772, 1), (key1655, 1), (key1813, 1)]

theorem rawRowCheck9699 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form8 = rawRow9699 := by decide +kernel

def row9699 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9699 : row9699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9699 := by decide +kernel

theorem rowEval9699 (x : Key → ℝ) : Integer.Sparse.eval row9699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9699, Integer.Sparse.eval_collectBalanced, rawRowCheck9699]

def rawRow9700 : Integer.Sparse Key := [(key1791, -2), (key1788, -2), (key1799, -2), (key1303, -2), (key1296, -2), (key1791, -2), (key1573, -2), (key1799, -2), (key1597, -2), (key1296, -2), (key1788, -2), (key1573, -2), (key1775, 1), (key1772, 1), (key1840, 1), (key1813, 1), (key1845, 1), (key1826, 1), (key1340, 1), (key1337, 1), (key1840, 1), (key1655, 1), (key1845, 1), (key1668, 1), (key1340, 1), (key1316, 1), (key1775, 1), (key1546, 1), (key1826, 1), (key1668, 1), (key1337, 1), (key1316, 1), (key1772, 1), (key1546, 1), (key1813, 1), (key1655, 1)]

theorem rawRowCheck9700 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form8 = rawRow9700 := by decide +kernel

def row9700 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9700 : row9700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9700 := by decide +kernel

theorem rowEval9700 (x : Key → ℝ) : Integer.Sparse.eval row9700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9700, Integer.Sparse.eval_collectBalanced, rawRowCheck9700]

def rawRow9701 : Integer.Sparse Key := [(key1788, -2), (key1799, -2), (key1791, -2), (key1573, -2), (key1597, -2), (key1296, -2), (key1799, -2), (key1303, -2), (key1791, -2), (key1573, -2), (key1296, -2), (key1788, -2), (key1813, 1), (key1826, 1), (key1772, 1), (key1845, 1), (key1775, 1), (key1840, 1), (key1655, 1), (key1668, 1), (key1337, 1), (key1845, 1), (key1340, 1), (key1840, 1), (key1546, 1), (key1668, 1), (key1316, 1), (key1826, 1), (key1340, 1), (key1775, 1), (key1546, 1), (key1655, 1), (key1316, 1), (key1813, 1), (key1337, 1), (key1772, 1)]

theorem rawRowCheck9701 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form8 = rawRow9701 := by decide +kernel

def row9701 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9701 : row9701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9701 := by decide +kernel

theorem rowEval9701 (x : Key → ℝ) : Integer.Sparse.eval row9701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9701, Integer.Sparse.eval_collectBalanced, rawRowCheck9701]

def rawRow9702 : Integer.Sparse Key := [(key1799, -2), (key1788, -2), (key1791, -2), (key1597, -2), (key1573, -2), (key1799, -2), (key1296, -2), (key1791, -2), (key1303, -2), (key1573, -2), (key1788, -2), (key1296, -2), (key1826, 1), (key1813, 1), (key1845, 1), (key1772, 1), (key1840, 1), (key1775, 1), (key1668, 1), (key1655, 1), (key1845, 1), (key1337, 1), (key1840, 1), (key1340, 1), (key1668, 1), (key1546, 1), (key1826, 1), (key1316, 1), (key1775, 1), (key1340, 1), (key1655, 1), (key1546, 1), (key1813, 1), (key1316, 1), (key1772, 1), (key1337, 1)]

theorem rawRowCheck9702 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form8 = rawRow9702 := by decide +kernel

def row9702 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9702 : row9702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9702 := by decide +kernel

theorem rowEval9702 (x : Key → ℝ) : Integer.Sparse.eval row9702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9702, Integer.Sparse.eval_collectBalanced, rawRowCheck9702]

def rawRow9703 : Integer.Sparse Key := [(key1791, -2), (key1799, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1303, -2), (key1597, -2), (key1296, -2), (key1573, -2), (key1788, -2), (key1296, -2), (key1573, -2), (key1840, 1), (key1845, 1), (key1775, 1), (key1826, 1), (key1772, 1), (key1813, 1), (key1840, 1), (key1845, 1), (key1340, 1), (key1668, 1), (key1337, 1), (key1655, 1), (key1775, 1), (key1826, 1), (key1340, 1), (key1668, 1), (key1316, 1), (key1546, 1), (key1772, 1), (key1813, 1), (key1337, 1), (key1655, 1), (key1316, 1), (key1546, 1)]

theorem rawRowCheck9703 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form8 = rawRow9703 := by decide +kernel

def row9703 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9703 : row9703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9703 := by decide +kernel

theorem rowEval9703 (x : Key → ℝ) : Integer.Sparse.eval row9703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9703, Integer.Sparse.eval_collectBalanced, rawRowCheck9703]

def rawRow9704 : Integer.Sparse Key := [(key1799, -2), (key1791, -2), (key1788, -2), (key1799, -2), (key1791, -2), (key1597, -2), (key1303, -2), (key1573, -2), (key1296, -2), (key1788, -2), (key1573, -2), (key1296, -2), (key1845, 1), (key1840, 1), (key1826, 1), (key1775, 1), (key1813, 1), (key1772, 1), (key1845, 1), (key1840, 1), (key1668, 1), (key1340, 1), (key1655, 1), (key1337, 1), (key1826, 1), (key1775, 1), (key1668, 1), (key1340, 1), (key1546, 1), (key1316, 1), (key1813, 1), (key1772, 1), (key1655, 1), (key1337, 1), (key1546, 1), (key1316, 1)]

theorem rawRowCheck9704 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form8 = rawRow9704 := by decide +kernel

def row9704 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1772, 2), (key1775, 2), (key1788, -4), (key1791, -4), (key1799, -4), (key1813, 2), (key1826, 2), (key1840, 2), (key1845, 2)]

theorem rowCheck9704 : row9704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9704 := by decide +kernel

theorem rowEval9704 (x : Key → ℝ) : Integer.Sparse.eval row9704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9704, Integer.Sparse.eval_collectBalanced, rawRowCheck9704]

def rawRow9705 : Integer.Sparse Key := [(key1316, -2), (key1316, -2), (key1330, -2), (key1424, -2), (key1424, -2), (key1813, -2), (key1813, -2), (key1818, -2), (key1818, -2), (key1448, -2), (key1826, -2), (key1826, -2), (key1296, 1), (key1296, 1), (key1337, 1), (key1337, 1), (key1346, 1), (key1346, 1), (key1391, 1), (key1391, 1), (key1772, 1), (key1772, 1), (key1781, 1), (key1781, 1), (key1455, 1), (key1455, 1), (key1788, 1), (key1788, 1), (key1842, 1), (key1842, 1), (key1467, 1), (key1467, 1), (key1799, 1), (key1799, 1), (key1845, 1), (key1845, 1)]

theorem rawRowCheck9705 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form8 = rawRow9705 := by decide +kernel

def row9705 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9705 : row9705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9705 := by decide +kernel

theorem rowEval9705 (x : Key → ℝ) : Integer.Sparse.eval row9705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9705, Integer.Sparse.eval_collectBalanced, rawRowCheck9705]

def rawRow9706 : Integer.Sparse Key := [(key1316, -2), (key1330, -2), (key1316, -2), (key1813, -2), (key1818, -2), (key1424, -2), (key1818, -2), (key1424, -2), (key1813, -2), (key1826, -2), (key1448, -2), (key1826, -2), (key1337, 1), (key1346, 1), (key1296, 1), (key1346, 1), (key1296, 1), (key1337, 1), (key1772, 1), (key1781, 1), (key1391, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1788, 1), (key1842, 1), (key1455, 1), (key1842, 1), (key1455, 1), (key1788, 1), (key1799, 1), (key1845, 1), (key1467, 1), (key1845, 1), (key1467, 1), (key1799, 1)]

theorem rawRowCheck9706 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form8 = rawRow9706 := by decide +kernel

def row9706 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9706 : row9706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9706 := by decide +kernel

theorem rowEval9706 (x : Key → ℝ) : Integer.Sparse.eval row9706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9706, Integer.Sparse.eval_collectBalanced, rawRowCheck9706]

def rawRow9707 : Integer.Sparse Key := [(key1330, -2), (key1316, -2), (key1316, -2), (key1818, -2), (key1813, -2), (key1818, -2), (key1424, -2), (key1813, -2), (key1424, -2), (key1826, -2), (key1826, -2), (key1448, -2), (key1346, 1), (key1337, 1), (key1346, 1), (key1296, 1), (key1337, 1), (key1296, 1), (key1781, 1), (key1772, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1842, 1), (key1788, 1), (key1842, 1), (key1455, 1), (key1788, 1), (key1455, 1), (key1845, 1), (key1799, 1), (key1845, 1), (key1467, 1), (key1799, 1), (key1467, 1)]

theorem rawRowCheck9707 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form8 = rawRow9707 := by decide +kernel

def row9707 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9707 : row9707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9707 := by decide +kernel

theorem rowEval9707 (x : Key → ℝ) : Integer.Sparse.eval row9707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9707, Integer.Sparse.eval_collectBalanced, rawRowCheck9707]

def rawRow9708 : Integer.Sparse Key := [(key1424, -2), (key1424, -2), (key1448, -2), (key1316, -2), (key1316, -2), (key1813, -2), (key1813, -2), (key1826, -2), (key1826, -2), (key1330, -2), (key1818, -2), (key1818, -2), (key1391, 1), (key1391, 1), (key1455, 1), (key1455, 1), (key1467, 1), (key1467, 1), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1799, 1), (key1799, 1), (key1337, 1), (key1337, 1), (key1772, 1), (key1772, 1), (key1845, 1), (key1845, 1), (key1346, 1), (key1346, 1), (key1781, 1), (key1781, 1), (key1842, 1), (key1842, 1)]

theorem rawRowCheck9708 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form8 = rawRow9708 := by decide +kernel

def row9708 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9708 : row9708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9708 := by decide +kernel

theorem rowEval9708 (x : Key → ℝ) : Integer.Sparse.eval row9708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9708, Integer.Sparse.eval_collectBalanced, rawRowCheck9708]

def rawRow9709 : Integer.Sparse Key := [(key1424, -2), (key1448, -2), (key1424, -2), (key1813, -2), (key1826, -2), (key1316, -2), (key1826, -2), (key1316, -2), (key1813, -2), (key1818, -2), (key1330, -2), (key1818, -2), (key1455, 1), (key1467, 1), (key1391, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1772, 1), (key1845, 1), (key1337, 1), (key1845, 1), (key1337, 1), (key1772, 1), (key1781, 1), (key1842, 1), (key1346, 1), (key1842, 1), (key1346, 1), (key1781, 1)]

theorem rawRowCheck9709 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form8 = rawRow9709 := by decide +kernel

def row9709 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9709 : row9709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9709 := by decide +kernel

theorem rowEval9709 (x : Key → ℝ) : Integer.Sparse.eval row9709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9709, Integer.Sparse.eval_collectBalanced, rawRowCheck9709]

def rawRow9710 : Integer.Sparse Key := [(key1448, -2), (key1424, -2), (key1424, -2), (key1826, -2), (key1813, -2), (key1826, -2), (key1316, -2), (key1813, -2), (key1316, -2), (key1818, -2), (key1818, -2), (key1330, -2), (key1467, 1), (key1455, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1391, 1), (key1799, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1845, 1), (key1772, 1), (key1845, 1), (key1337, 1), (key1772, 1), (key1337, 1), (key1842, 1), (key1781, 1), (key1842, 1), (key1346, 1), (key1781, 1), (key1346, 1)]

theorem rawRowCheck9710 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form8 = rawRow9710 := by decide +kernel

def row9710 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9710 : row9710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9710 := by decide +kernel

theorem rowEval9710 (x : Key → ℝ) : Integer.Sparse.eval row9710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9710, Integer.Sparse.eval_collectBalanced, rawRowCheck9710]

def rawRow9711 : Integer.Sparse Key := [(key1813, -2), (key1818, -2), (key1826, -2), (key1316, -2), (key1330, -2), (key1424, -2), (key1818, -2), (key1448, -2), (key1826, -2), (key1316, -2), (key1424, -2), (key1813, -2), (key1772, 1), (key1781, 1), (key1788, 1), (key1842, 1), (key1799, 1), (key1845, 1), (key1337, 1), (key1346, 1), (key1455, 1), (key1842, 1), (key1467, 1), (key1845, 1), (key1296, 1), (key1346, 1), (key1391, 1), (key1781, 1), (key1467, 1), (key1799, 1), (key1296, 1), (key1337, 1), (key1391, 1), (key1772, 1), (key1455, 1), (key1788, 1)]

theorem rawRowCheck9711 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form8 = rawRow9711 := by decide +kernel

def row9711 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9711 : row9711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9711 := by decide +kernel

theorem rowEval9711 (x : Key → ℝ) : Integer.Sparse.eval row9711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9711, Integer.Sparse.eval_collectBalanced, rawRowCheck9711]

def rawRow9712 : Integer.Sparse Key := [(key1818, -2), (key1813, -2), (key1826, -2), (key1330, -2), (key1316, -2), (key1818, -2), (key1424, -2), (key1826, -2), (key1448, -2), (key1316, -2), (key1813, -2), (key1424, -2), (key1781, 1), (key1772, 1), (key1842, 1), (key1788, 1), (key1845, 1), (key1799, 1), (key1346, 1), (key1337, 1), (key1842, 1), (key1455, 1), (key1845, 1), (key1467, 1), (key1346, 1), (key1296, 1), (key1781, 1), (key1391, 1), (key1799, 1), (key1467, 1), (key1337, 1), (key1296, 1), (key1772, 1), (key1391, 1), (key1788, 1), (key1455, 1)]

theorem rawRowCheck9712 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form8 = rawRow9712 := by decide +kernel

def row9712 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9712 : row9712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9712 := by decide +kernel

theorem rowEval9712 (x : Key → ℝ) : Integer.Sparse.eval row9712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9712, Integer.Sparse.eval_collectBalanced, rawRowCheck9712]

def rawRow9713 : Integer.Sparse Key := [(key1813, -2), (key1826, -2), (key1818, -2), (key1424, -2), (key1448, -2), (key1316, -2), (key1826, -2), (key1330, -2), (key1818, -2), (key1424, -2), (key1316, -2), (key1813, -2), (key1788, 1), (key1799, 1), (key1772, 1), (key1845, 1), (key1781, 1), (key1842, 1), (key1455, 1), (key1467, 1), (key1337, 1), (key1845, 1), (key1346, 1), (key1842, 1), (key1391, 1), (key1467, 1), (key1296, 1), (key1799, 1), (key1346, 1), (key1781, 1), (key1391, 1), (key1455, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1772, 1)]

theorem rawRowCheck9713 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form8 = rawRow9713 := by decide +kernel

def row9713 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9713 : row9713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9713 := by decide +kernel

theorem rowEval9713 (x : Key → ℝ) : Integer.Sparse.eval row9713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9713, Integer.Sparse.eval_collectBalanced, rawRowCheck9713]

def rawRow9714 : Integer.Sparse Key := [(key1826, -2), (key1813, -2), (key1818, -2), (key1448, -2), (key1424, -2), (key1826, -2), (key1316, -2), (key1818, -2), (key1330, -2), (key1424, -2), (key1813, -2), (key1316, -2), (key1799, 1), (key1788, 1), (key1845, 1), (key1772, 1), (key1842, 1), (key1781, 1), (key1467, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1842, 1), (key1346, 1), (key1467, 1), (key1391, 1), (key1799, 1), (key1296, 1), (key1781, 1), (key1346, 1), (key1455, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1772, 1), (key1337, 1)]

theorem rawRowCheck9714 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form8 = rawRow9714 := by decide +kernel

def row9714 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9714 : row9714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9714 := by decide +kernel

theorem rowEval9714 (x : Key → ℝ) : Integer.Sparse.eval row9714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9714, Integer.Sparse.eval_collectBalanced, rawRowCheck9714]

def rawRow9715 : Integer.Sparse Key := [(key1818, -2), (key1826, -2), (key1813, -2), (key1818, -2), (key1826, -2), (key1330, -2), (key1448, -2), (key1316, -2), (key1424, -2), (key1813, -2), (key1316, -2), (key1424, -2), (key1842, 1), (key1845, 1), (key1781, 1), (key1799, 1), (key1772, 1), (key1788, 1), (key1842, 1), (key1845, 1), (key1346, 1), (key1467, 1), (key1337, 1), (key1455, 1), (key1781, 1), (key1799, 1), (key1346, 1), (key1467, 1), (key1296, 1), (key1391, 1), (key1772, 1), (key1788, 1), (key1337, 1), (key1455, 1), (key1296, 1), (key1391, 1)]

theorem rawRowCheck9715 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form8 = rawRow9715 := by decide +kernel

def row9715 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9715 : row9715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9715 := by decide +kernel

theorem rowEval9715 (x : Key → ℝ) : Integer.Sparse.eval row9715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9715, Integer.Sparse.eval_collectBalanced, rawRowCheck9715]

def rawRow9716 : Integer.Sparse Key := [(key1826, -2), (key1818, -2), (key1813, -2), (key1826, -2), (key1818, -2), (key1448, -2), (key1330, -2), (key1424, -2), (key1316, -2), (key1813, -2), (key1424, -2), (key1316, -2), (key1845, 1), (key1842, 1), (key1799, 1), (key1781, 1), (key1788, 1), (key1772, 1), (key1845, 1), (key1842, 1), (key1467, 1), (key1346, 1), (key1455, 1), (key1337, 1), (key1799, 1), (key1781, 1), (key1467, 1), (key1346, 1), (key1391, 1), (key1296, 1), (key1788, 1), (key1772, 1), (key1455, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

theorem rawRowCheck9716 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form8 = rawRow9716 := by decide +kernel

def row9716 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1772, 2), (key1781, 2), (key1788, 2), (key1799, 2), (key1813, -4), (key1818, -4), (key1826, -4), (key1842, 2), (key1845, 2)]

theorem rowCheck9716 : row9716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9716 := by decide +kernel

theorem rowEval9716 (x : Key → ℝ) : Integer.Sparse.eval row9716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck9716, Integer.Sparse.eval_collectBalanced, rawRowCheck9716]

def rawRow9717 : Integer.Sparse Key := [(key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2644, 1), (key2644, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1), (key2860, 1), (key2860, 1), (key2870, 1), (key2870, 1), (key2885, 1), (key2885, 1), (key3023, 1), (key3023, 1), (key3026, 1), (key3026, 1), (key3030, 1), (key3030, 1), (key2658, -2), (key2660, -2), (key2660, -2), (key2753, -2), (key2758, -2), (key2758, -2), (key2920, -2), (key2920, -2), (key2923, -2), (key2923, -2), (key2927, -2), (key2927, -2)]

theorem rawRowCheck9717 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form9 = rawRow9717 := by decide +kernel

def row9717 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9717 : row9717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9717 := by decide +kernel

theorem rowEval9717 (x : Key → ℝ) : Integer.Sparse.eval row9717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9717, Integer.Sparse.eval_collectBalanced, rawRowCheck9717]

def rawRow9718 : Integer.Sparse Key := [(key2640, 1), (key2644, 1), (key2632, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key2660, -2), (key2658, -2), (key2660, -2), (key2758, -2), (key2753, -2), (key2758, -2), (key2923, -2), (key2927, -2), (key2920, -2), (key2927, -2), (key2920, -2), (key2923, -2)]

theorem rawRowCheck9718 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form9 = rawRow9718 := by decide +kernel

def row9718 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9718 : row9718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9718 := by decide +kernel

theorem rowEval9718 (x : Key → ℝ) : Integer.Sparse.eval row9718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9718, Integer.Sparse.eval_collectBalanced, rawRowCheck9718]

def rawRow9719 : Integer.Sparse Key := [(key2644, 1), (key2640, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key2885, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key2860, 1), (key3030, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key3023, 1), (key2660, -2), (key2660, -2), (key2658, -2), (key2758, -2), (key2758, -2), (key2753, -2), (key2927, -2), (key2923, -2), (key2927, -2), (key2920, -2), (key2923, -2), (key2920, -2)]

theorem rawRowCheck9719 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form9 = rawRow9719 := by decide +kernel

def row9719 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9719 : row9719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9719 := by decide +kernel

theorem rowEval9719 (x : Key → ℝ) : Integer.Sparse.eval row9719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9719, Integer.Sparse.eval_collectBalanced, rawRowCheck9719]

def rawRow9720 : Integer.Sparse Key := [(key2706, 1), (key2706, 1), (key2860, 1), (key2860, 1), (key3023, 1), (key3023, 1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2644, 1), (key2644, 1), (key2732, 1), (key2732, 1), (key2885, 1), (key2885, 1), (key2753, -2), (key2920, -2), (key2920, -2), (key2658, -2), (key2923, -2), (key2923, -2), (key2660, -2), (key2660, -2), (key2758, -2), (key2758, -2), (key2927, -2), (key2927, -2)]

theorem rawRowCheck9720 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form9 = rawRow9720 := by decide +kernel

def row9720 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9720 : row9720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9720 := by decide +kernel

theorem rowEval9720 (x : Key → ℝ) : Integer.Sparse.eval row9720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9720, Integer.Sparse.eval_collectBalanced, rawRowCheck9720]

def rawRow9721 : Integer.Sparse Key := [(key2860, 1), (key3023, 1), (key2706, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2920, -2), (key2753, -2), (key2920, -2), (key2923, -2), (key2658, -2), (key2923, -2), (key2758, -2), (key2927, -2), (key2660, -2), (key2927, -2), (key2660, -2), (key2758, -2)]

theorem rawRowCheck9721 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form9 = rawRow9721 := by decide +kernel

def row9721 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9721 : row9721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9721 := by decide +kernel

theorem rowEval9721 (x : Key → ℝ) : Integer.Sparse.eval row9721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9721, Integer.Sparse.eval_collectBalanced, rawRowCheck9721]

def rawRow9722 : Integer.Sparse Key := [(key3023, 1), (key2860, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2885, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2644, 1), (key2920, -2), (key2920, -2), (key2753, -2), (key2923, -2), (key2923, -2), (key2658, -2), (key2927, -2), (key2758, -2), (key2927, -2), (key2660, -2), (key2758, -2), (key2660, -2)]

theorem rawRowCheck9722 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form9 = rawRow9722 := by decide +kernel

def row9722 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9722 : row9722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9722 := by decide +kernel

theorem rowEval9722 (x : Key → ℝ) : Integer.Sparse.eval row9722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9722, Integer.Sparse.eval_collectBalanced, rawRowCheck9722]

def rawRow9723 : Integer.Sparse Key := [(key2726, 1), (key2732, 1), (key2870, 1), (key2885, 1), (key3026, 1), (key3030, 1), (key2640, 1), (key2644, 1), (key2860, 1), (key2885, 1), (key3023, 1), (key3030, 1), (key2632, 1), (key2644, 1), (key2706, 1), (key2732, 1), (key3023, 1), (key3026, 1), (key2632, 1), (key2640, 1), (key2706, 1), (key2726, 1), (key2860, 1), (key2870, 1), (key2758, -2), (key2923, -2), (key2927, -2), (key2660, -2), (key2920, -2), (key2927, -2), (key2658, -2), (key2660, -2), (key2753, -2), (key2758, -2), (key2920, -2), (key2923, -2)]

theorem rawRowCheck9723 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form9 = rawRow9723 := by decide +kernel

def row9723 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9723 : row9723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9723 := by decide +kernel

theorem rowEval9723 (x : Key → ℝ) : Integer.Sparse.eval row9723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9723, Integer.Sparse.eval_collectBalanced, rawRowCheck9723]

def rawRow9724 : Integer.Sparse Key := [(key2732, 1), (key2726, 1), (key2885, 1), (key2870, 1), (key3030, 1), (key3026, 1), (key2644, 1), (key2640, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key3023, 1), (key2644, 1), (key2632, 1), (key2732, 1), (key2706, 1), (key3026, 1), (key3023, 1), (key2640, 1), (key2632, 1), (key2726, 1), (key2706, 1), (key2870, 1), (key2860, 1), (key2758, -2), (key2927, -2), (key2923, -2), (key2660, -2), (key2927, -2), (key2920, -2), (key2660, -2), (key2658, -2), (key2758, -2), (key2753, -2), (key2923, -2), (key2920, -2)]

theorem rawRowCheck9724 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form9 = rawRow9724 := by decide +kernel

def row9724 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9724 : row9724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9724 := by decide +kernel

theorem rowEval9724 (x : Key → ℝ) : Integer.Sparse.eval row9724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9724, Integer.Sparse.eval_collectBalanced, rawRowCheck9724]

def rawRow9725 : Integer.Sparse Key := [(key2870, 1), (key3026, 1), (key2726, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2860, 1), (key3023, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2706, 1), (key3023, 1), (key2632, 1), (key3026, 1), (key2644, 1), (key2732, 1), (key2706, 1), (key2860, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2923, -2), (key2758, -2), (key2927, -2), (key2920, -2), (key2660, -2), (key2927, -2), (key2753, -2), (key2920, -2), (key2658, -2), (key2923, -2), (key2660, -2), (key2758, -2)]

theorem rawRowCheck9725 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form9 = rawRow9725 := by decide +kernel

def row9725 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9725 : row9725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9725 := by decide +kernel

theorem rowEval9725 (x : Key → ℝ) : Integer.Sparse.eval row9725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9725, Integer.Sparse.eval_collectBalanced, rawRowCheck9725]

def rawRow9726 : Integer.Sparse Key := [(key3026, 1), (key2870, 1), (key3030, 1), (key2726, 1), (key2885, 1), (key2732, 1), (key3023, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key2885, 1), (key2644, 1), (key3023, 1), (key2706, 1), (key3026, 1), (key2632, 1), (key2732, 1), (key2644, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2726, 1), (key2640, 1), (key2923, -2), (key2927, -2), (key2758, -2), (key2920, -2), (key2927, -2), (key2660, -2), (key2920, -2), (key2753, -2), (key2923, -2), (key2658, -2), (key2758, -2), (key2660, -2)]

theorem rawRowCheck9726 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form9 = rawRow9726 := by decide +kernel

def row9726 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9726 : row9726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9726 := by decide +kernel

theorem rowEval9726 (x : Key → ℝ) : Integer.Sparse.eval row9726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9726, Integer.Sparse.eval_collectBalanced, rawRowCheck9726]

def rawRow9727 : Integer.Sparse Key := [(key2885, 1), (key3030, 1), (key2732, 1), (key3026, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2640, 1), (key2860, 1), (key2732, 1), (key3026, 1), (key2644, 1), (key3023, 1), (key2632, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2632, 1), (key2706, 1), (key2927, -2), (key2758, -2), (key2923, -2), (key2927, -2), (key2660, -2), (key2920, -2), (key2758, -2), (key2923, -2), (key2660, -2), (key2920, -2), (key2658, -2), (key2753, -2)]

theorem rawRowCheck9727 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form9 = rawRow9727 := by decide +kernel

def row9727 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9727 : row9727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9727 := by decide +kernel

theorem rowEval9727 (x : Key → ℝ) : Integer.Sparse.eval row9727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9727, Integer.Sparse.eval_collectBalanced, rawRowCheck9727]

end MUB6.Certificate.GramRows

end OAI

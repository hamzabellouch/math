import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
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

def rawRow7680 : Integer.Sparse Key := [(key1123, -6), (key1150, -6), (key1114, -6), (key1106, -6), (key1235, 2), (key1242, 2), (key1232, 2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1106, 2), (key993, 2), (key1028, 2)]

theorem rawRowCheck7680 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form2 = rawRow7680 := by decide +kernel

def row7680 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7680 : row7680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7680 := by decide +kernel

theorem rowEval7680 (x : Key → ℝ) : Integer.Sparse.eval row7680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7680, Integer.Sparse.eval_collectBalanced, rawRowCheck7680]

def rawRow7681 : Integer.Sparse Key := [(key1150, -6), (key1123, -6), (key1114, -6), (key1106, -6), (key1242, 2), (key1235, 2), (key1232, 2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1106, 2), (key1028, 2), (key993, 2)]

theorem rawRowCheck7681 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form2 = rawRow7681 := by decide +kernel

def row7681 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

theorem rowCheck7681 : row7681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7681 := by decide +kernel

theorem rowEval7681 (x : Key → ℝ) : Integer.Sparse.eval row7681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck7681, Integer.Sparse.eval_collectBalanced, rawRowCheck7681]

def rawRow7682 : Integer.Sparse Key := [(key2610, -6), (key2803, -6), (key2803, -6), (key2824, -6), (key2626, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck7682 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form3 = rawRow7682 := by decide +kernel

def row7682 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7682 : row7682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7682 := by decide +kernel

theorem rowEval7682 (x : Key → ℝ) : Integer.Sparse.eval row7682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7682, Integer.Sparse.eval_collectBalanced, rawRowCheck7682]

def rawRow7683 : Integer.Sparse Key := [(key2610, -6), (key2803, -6), (key2824, -6), (key2803, -6), (key2626, 2), (key2635, 2), (key2626, 2), (key2700, 2), (key2721, 2), (key2700, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck7683 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form3 = rawRow7683 := by decide +kernel

def row7683 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7683 : row7683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7683 := by decide +kernel

theorem rowEval7683 (x : Key → ℝ) : Integer.Sparse.eval row7683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7683, Integer.Sparse.eval_collectBalanced, rawRowCheck7683]

def rawRow7684 : Integer.Sparse Key := [(key2610, -6), (key2824, -6), (key2803, -6), (key2803, -6), (key2635, 2), (key2626, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2700, 2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck7684 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form3 = rawRow7684 := by decide +kernel

def row7684 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7684 : row7684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7684 := by decide +kernel

theorem rowEval7684 (x : Key → ℝ) : Integer.Sparse.eval row7684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7684, Integer.Sparse.eval_collectBalanced, rawRowCheck7684]

def rawRow7685 : Integer.Sparse Key := [(key2803, -6), (key2610, -6), (key2803, -6), (key2824, -6), (key2700, 2), (key2853, 2), (key2855, 2), (key2626, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck7685 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form3 = rawRow7685 := by decide +kernel

def row7685 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7685 : row7685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7685 := by decide +kernel

theorem rowEval7685 (x : Key → ℝ) : Integer.Sparse.eval row7685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7685, Integer.Sparse.eval_collectBalanced, rawRowCheck7685]

def rawRow7686 : Integer.Sparse Key := [(key2803, -6), (key2610, -6), (key2824, -6), (key2803, -6), (key2700, 2), (key2855, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2853, 2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck7686 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form3 = rawRow7686 := by decide +kernel

def row7686 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7686 : row7686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7686 := by decide +kernel

theorem rowEval7686 (x : Key → ℝ) : Integer.Sparse.eval row7686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7686, Integer.Sparse.eval_collectBalanced, rawRowCheck7686]

def rawRow7687 : Integer.Sparse Key := [(key2803, -6), (key2803, -6), (key2610, -6), (key2824, -6), (key2853, 2), (key2700, 2), (key2855, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

theorem rawRowCheck7687 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form3 = rawRow7687 := by decide +kernel

def row7687 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7687 : row7687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7687 := by decide +kernel

theorem rowEval7687 (x : Key → ℝ) : Integer.Sparse.eval row7687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7687, Integer.Sparse.eval_collectBalanced, rawRowCheck7687]

def rawRow7688 : Integer.Sparse Key := [(key2803, -6), (key2803, -6), (key2824, -6), (key2610, -6), (key2853, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

theorem rawRowCheck7688 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form3 = rawRow7688 := by decide +kernel

def row7688 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7688 : row7688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7688 := by decide +kernel

theorem rowEval7688 (x : Key → ℝ) : Integer.Sparse.eval row7688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7688, Integer.Sparse.eval_collectBalanced, rawRowCheck7688]

def rawRow7689 : Integer.Sparse Key := [(key2803, -6), (key2824, -6), (key2610, -6), (key2803, -6), (key2855, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck7689 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form3 = rawRow7689 := by decide +kernel

def row7689 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7689 : row7689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7689 := by decide +kernel

theorem rowEval7689 (x : Key → ℝ) : Integer.Sparse.eval row7689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7689, Integer.Sparse.eval_collectBalanced, rawRowCheck7689]

def rawRow7690 : Integer.Sparse Key := [(key2803, -6), (key2824, -6), (key2803, -6), (key2610, -6), (key2855, 2), (key2853, 2), (key2700, 2), (key2865, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck7690 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form3 = rawRow7690 := by decide +kernel

def row7690 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7690 : row7690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7690 := by decide +kernel

theorem rowEval7690 (x : Key → ℝ) : Integer.Sparse.eval row7690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7690, Integer.Sparse.eval_collectBalanced, rawRowCheck7690]

def rawRow7691 : Integer.Sparse Key := [(key2824, -6), (key2610, -6), (key2803, -6), (key2803, -6), (key2721, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2855, 2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck7691 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form3 = rawRow7691 := by decide +kernel

def row7691 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7691 : row7691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7691 := by decide +kernel

theorem rowEval7691 (x : Key → ℝ) : Integer.Sparse.eval row7691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7691, Integer.Sparse.eval_collectBalanced, rawRowCheck7691]

def rawRow7692 : Integer.Sparse Key := [(key2824, -6), (key2803, -6), (key2610, -6), (key2803, -6), (key2865, 2), (key2721, 2), (key2865, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck7692 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form3 = rawRow7692 := by decide +kernel

def row7692 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7692 : row7692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7692 := by decide +kernel

theorem rowEval7692 (x : Key → ℝ) : Integer.Sparse.eval row7692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7692, Integer.Sparse.eval_collectBalanced, rawRowCheck7692]

def rawRow7693 : Integer.Sparse Key := [(key2824, -6), (key2803, -6), (key2803, -6), (key2610, -6), (key2865, 2), (key2865, 2), (key2721, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck7693 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form3 = rawRow7693 := by decide +kernel

def row7693 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck7693 : row7693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7693 := by decide +kernel

theorem rowEval7693 (x : Key → ℝ) : Integer.Sparse.eval row7693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7693, Integer.Sparse.eval_collectBalanced, rawRowCheck7693]

def rawRow7694 : Integer.Sparse Key := [(key2626, -6), (key2780, -6), (key2853, -6), (key2865, -6), (key2610, 2), (key2626, 2), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck7694 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form3 = rawRow7694 := by decide +kernel

def row7694 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7694 : row7694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7694 := by decide +kernel

theorem rowEval7694 (x : Key → ℝ) : Integer.Sparse.eval row7694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7694, Integer.Sparse.eval_collectBalanced, rawRowCheck7694]

def rawRow7695 : Integer.Sparse Key := [(key2626, -6), (key2780, -6), (key2865, -6), (key2853, -6), (key2610, 2), (key2635, 2), (key2626, 2), (key2665, 2), (key2721, 2), (key2700, 2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck7695 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form3 = rawRow7695 := by decide +kernel

def row7695 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7695 : row7695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7695 := by decide +kernel

theorem rowEval7695 (x : Key → ℝ) : Integer.Sparse.eval row7695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7695, Integer.Sparse.eval_collectBalanced, rawRowCheck7695]

def rawRow7696 : Integer.Sparse Key := [(key2626, -6), (key2853, -6), (key2780, -6), (key2865, -6), (key2626, 2), (key2610, 2), (key2635, 2), (key2700, 2), (key2665, 2), (key2721, 2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

theorem rawRowCheck7696 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form3 = rawRow7696 := by decide +kernel

def row7696 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7696 : row7696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7696 := by decide +kernel

theorem rowEval7696 (x : Key → ℝ) : Integer.Sparse.eval row7696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7696, Integer.Sparse.eval_collectBalanced, rawRowCheck7696]

def rawRow7697 : Integer.Sparse Key := [(key2626, -6), (key2853, -6), (key2865, -6), (key2780, -6), (key2626, 2), (key2635, 2), (key2610, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

theorem rawRowCheck7697 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form3 = rawRow7697 := by decide +kernel

def row7697 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7697 : row7697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7697 := by decide +kernel

theorem rowEval7697 (x : Key → ℝ) : Integer.Sparse.eval row7697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7697, Integer.Sparse.eval_collectBalanced, rawRowCheck7697]

def rawRow7698 : Integer.Sparse Key := [(key2626, -6), (key2865, -6), (key2780, -6), (key2853, -6), (key2635, 2), (key2610, 2), (key2626, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck7698 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form3 = rawRow7698 := by decide +kernel

def row7698 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7698 : row7698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7698 := by decide +kernel

theorem rowEval7698 (x : Key → ℝ) : Integer.Sparse.eval row7698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7698, Integer.Sparse.eval_collectBalanced, rawRowCheck7698]

def rawRow7699 : Integer.Sparse Key := [(key2626, -6), (key2865, -6), (key2853, -6), (key2780, -6), (key2635, 2), (key2626, 2), (key2610, 2), (key2721, 2), (key2700, 2), (key2665, 2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck7699 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form3 = rawRow7699 := by decide +kernel

def row7699 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7699 : row7699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7699 := by decide +kernel

theorem rowEval7699 (x : Key → ℝ) : Integer.Sparse.eval row7699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7699, Integer.Sparse.eval_collectBalanced, rawRowCheck7699]

def rawRow7700 : Integer.Sparse Key := [(key2780, -6), (key2626, -6), (key2853, -6), (key2865, -6), (key2665, 2), (key2780, 2), (key2789, 2), (key2610, 2), (key2803, 2), (key2824, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck7700 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form3 = rawRow7700 := by decide +kernel

def row7700 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7700 : row7700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7700 := by decide +kernel

theorem rowEval7700 (x : Key → ℝ) : Integer.Sparse.eval row7700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7700, Integer.Sparse.eval_collectBalanced, rawRowCheck7700]

def rawRow7701 : Integer.Sparse Key := [(key2780, -6), (key2626, -6), (key2865, -6), (key2853, -6), (key2665, 2), (key2789, 2), (key2780, 2), (key2610, 2), (key2824, 2), (key2803, 2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck7701 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form3 = rawRow7701 := by decide +kernel

def row7701 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7701 : row7701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7701 := by decide +kernel

theorem rowEval7701 (x : Key → ℝ) : Integer.Sparse.eval row7701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7701, Integer.Sparse.eval_collectBalanced, rawRowCheck7701]

def rawRow7702 : Integer.Sparse Key := [(key2780, -6), (key2853, -6), (key2626, -6), (key2865, -6), (key2780, 2), (key2665, 2), (key2789, 2), (key2803, 2), (key2610, 2), (key2824, 2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

theorem rawRowCheck7702 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form3 = rawRow7702 := by decide +kernel

def row7702 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7702 : row7702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7702 := by decide +kernel

theorem rowEval7702 (x : Key → ℝ) : Integer.Sparse.eval row7702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7702, Integer.Sparse.eval_collectBalanced, rawRowCheck7702]

def rawRow7703 : Integer.Sparse Key := [(key2780, -6), (key2853, -6), (key2865, -6), (key2626, -6), (key2780, 2), (key2789, 2), (key2665, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

theorem rawRowCheck7703 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form3 = rawRow7703 := by decide +kernel

def row7703 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7703 : row7703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7703 := by decide +kernel

theorem rowEval7703 (x : Key → ℝ) : Integer.Sparse.eval row7703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7703, Integer.Sparse.eval_collectBalanced, rawRowCheck7703]

def rawRow7704 : Integer.Sparse Key := [(key2780, -6), (key2865, -6), (key2626, -6), (key2853, -6), (key2789, 2), (key2665, 2), (key2780, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck7704 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form3 = rawRow7704 := by decide +kernel

def row7704 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7704 : row7704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7704 := by decide +kernel

theorem rowEval7704 (x : Key → ℝ) : Integer.Sparse.eval row7704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7704, Integer.Sparse.eval_collectBalanced, rawRowCheck7704]

def rawRow7705 : Integer.Sparse Key := [(key2780, -6), (key2865, -6), (key2853, -6), (key2626, -6), (key2789, 2), (key2780, 2), (key2665, 2), (key2824, 2), (key2803, 2), (key2610, 2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck7705 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form3 = rawRow7705 := by decide +kernel

def row7705 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7705 : row7705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7705 := by decide +kernel

theorem rowEval7705 (x : Key → ℝ) : Integer.Sparse.eval row7705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7705, Integer.Sparse.eval_collectBalanced, rawRowCheck7705]

def rawRow7706 : Integer.Sparse Key := [(key2853, -6), (key2626, -6), (key2780, -6), (key2865, -6), (key2700, 2), (key2803, 2), (key2855, 2), (key2626, 2), (key2780, 2), (key2865, 2), (key2610, 2), (key2635, 2), (key2665, 2), (key2721, 2), (key2789, 2), (key2824, 2)]

theorem rawRowCheck7706 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form3 = rawRow7706 := by decide +kernel

def row7706 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7706 : row7706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7706 := by decide +kernel

theorem rowEval7706 (x : Key → ℝ) : Integer.Sparse.eval row7706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7706, Integer.Sparse.eval_collectBalanced, rawRowCheck7706]

def rawRow7707 : Integer.Sparse Key := [(key2853, -6), (key2626, -6), (key2865, -6), (key2780, -6), (key2700, 2), (key2855, 2), (key2803, 2), (key2626, 2), (key2865, 2), (key2780, 2), (key2635, 2), (key2610, 2), (key2721, 2), (key2665, 2), (key2824, 2), (key2789, 2)]

theorem rawRowCheck7707 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form3 = rawRow7707 := by decide +kernel

def row7707 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7707 : row7707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7707 := by decide +kernel

theorem rowEval7707 (x : Key → ℝ) : Integer.Sparse.eval row7707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7707, Integer.Sparse.eval_collectBalanced, rawRowCheck7707]

def rawRow7708 : Integer.Sparse Key := [(key2853, -6), (key2780, -6), (key2626, -6), (key2865, -6), (key2803, 2), (key2700, 2), (key2855, 2), (key2780, 2), (key2626, 2), (key2865, 2), (key2665, 2), (key2789, 2), (key2610, 2), (key2824, 2), (key2635, 2), (key2721, 2)]

theorem rawRowCheck7708 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form3 = rawRow7708 := by decide +kernel

def row7708 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7708 : row7708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7708 := by decide +kernel

theorem rowEval7708 (x : Key → ℝ) : Integer.Sparse.eval row7708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7708, Integer.Sparse.eval_collectBalanced, rawRowCheck7708]

def rawRow7709 : Integer.Sparse Key := [(key2853, -6), (key2780, -6), (key2865, -6), (key2626, -6), (key2803, 2), (key2855, 2), (key2700, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2789, 2), (key2665, 2), (key2824, 2), (key2610, 2), (key2721, 2), (key2635, 2)]

theorem rawRowCheck7709 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form3 = rawRow7709 := by decide +kernel

def row7709 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7709 : row7709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7709 := by decide +kernel

theorem rowEval7709 (x : Key → ℝ) : Integer.Sparse.eval row7709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7709, Integer.Sparse.eval_collectBalanced, rawRowCheck7709]

def rawRow7710 : Integer.Sparse Key := [(key2853, -6), (key2865, -6), (key2626, -6), (key2780, -6), (key2855, 2), (key2700, 2), (key2803, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2721, 2), (key2824, 2), (key2635, 2), (key2789, 2), (key2610, 2), (key2665, 2)]

theorem rawRowCheck7710 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form3 = rawRow7710 := by decide +kernel

def row7710 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7710 : row7710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7710 := by decide +kernel

theorem rowEval7710 (x : Key → ℝ) : Integer.Sparse.eval row7710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7710, Integer.Sparse.eval_collectBalanced, rawRowCheck7710]

def rawRow7711 : Integer.Sparse Key := [(key2853, -6), (key2865, -6), (key2780, -6), (key2626, -6), (key2855, 2), (key2803, 2), (key2700, 2), (key2865, 2), (key2780, 2), (key2626, 2), (key2824, 2), (key2721, 2), (key2789, 2), (key2635, 2), (key2665, 2), (key2610, 2)]

theorem rawRowCheck7711 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form3 = rawRow7711 := by decide +kernel

def row7711 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7711 : row7711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7711 := by decide +kernel

theorem rowEval7711 (x : Key → ℝ) : Integer.Sparse.eval row7711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7711, Integer.Sparse.eval_collectBalanced, rawRowCheck7711]

def rawRow7712 : Integer.Sparse Key := [(key2865, -6), (key2626, -6), (key2780, -6), (key2853, -6), (key2721, 2), (key2824, 2), (key2865, 2), (key2635, 2), (key2789, 2), (key2855, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck7712 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form3 = rawRow7712 := by decide +kernel

def row7712 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7712 : row7712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7712 := by decide +kernel

theorem rowEval7712 (x : Key → ℝ) : Integer.Sparse.eval row7712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7712, Integer.Sparse.eval_collectBalanced, rawRowCheck7712]

def rawRow7713 : Integer.Sparse Key := [(key2865, -6), (key2626, -6), (key2853, -6), (key2780, -6), (key2721, 2), (key2865, 2), (key2824, 2), (key2635, 2), (key2855, 2), (key2789, 2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck7713 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form3 = rawRow7713 := by decide +kernel

def row7713 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7713 : row7713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7713 := by decide +kernel

theorem rowEval7713 (x : Key → ℝ) : Integer.Sparse.eval row7713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7713, Integer.Sparse.eval_collectBalanced, rawRowCheck7713]

def rawRow7714 : Integer.Sparse Key := [(key2865, -6), (key2780, -6), (key2626, -6), (key2853, -6), (key2824, 2), (key2721, 2), (key2865, 2), (key2789, 2), (key2635, 2), (key2855, 2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck7714 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form3 = rawRow7714 := by decide +kernel

def row7714 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7714 : row7714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7714 := by decide +kernel

theorem rowEval7714 (x : Key → ℝ) : Integer.Sparse.eval row7714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7714, Integer.Sparse.eval_collectBalanced, rawRowCheck7714]

def rawRow7715 : Integer.Sparse Key := [(key2865, -6), (key2780, -6), (key2853, -6), (key2626, -6), (key2824, 2), (key2865, 2), (key2721, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck7715 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form3 = rawRow7715 := by decide +kernel

def row7715 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7715 : row7715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7715 := by decide +kernel

theorem rowEval7715 (x : Key → ℝ) : Integer.Sparse.eval row7715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7715, Integer.Sparse.eval_collectBalanced, rawRowCheck7715]

def rawRow7716 : Integer.Sparse Key := [(key2865, -6), (key2853, -6), (key2626, -6), (key2780, -6), (key2865, 2), (key2721, 2), (key2824, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

theorem rawRowCheck7716 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form3 = rawRow7716 := by decide +kernel

def row7716 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7716 : row7716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7716 := by decide +kernel

theorem rowEval7716 (x : Key → ℝ) : Integer.Sparse.eval row7716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck7716, Integer.Sparse.eval_collectBalanced, rawRowCheck7716]

def rawRow7717 : Integer.Sparse Key := [(key2865, -6), (key2853, -6), (key2780, -6), (key2626, -6), (key2865, 2), (key2824, 2), (key2721, 2), (key2855, 2), (key2789, 2), (key2635, 2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

theorem rawRowCheck7717 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form3 = rawRow7717 := by decide +kernel

def row7717 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

theorem rowCheck7717 : row7717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7717 := by decide +kernel

theorem rowEval7717 (x : Key → ℝ) : Integer.Sparse.eval row7717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck7717, Integer.Sparse.eval_collectBalanced, rawRowCheck7717]

def rawRow7718 : Integer.Sparse Key := [(key2398, -6), (key2404, -6), (key2404, -6), (key2435, -6), (key2583, 2), (key2589, 2), (key2589, 2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key3019, 2), (key3019, 2), (key3028, 2)]

theorem rawRowCheck7718 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form4 = rawRow7718 := by decide +kernel

def row7718 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7718 : row7718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7718 := by decide +kernel

theorem rowEval7718 (x : Key → ℝ) : Integer.Sparse.eval row7718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7718, Integer.Sparse.eval_collectBalanced, rawRowCheck7718]

def rawRow7719 : Integer.Sparse Key := [(key2404, -6), (key2398, -6), (key2404, -6), (key2435, -6), (key2589, 2), (key2583, 2), (key2589, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key3019, 2), (key3028, 2), (key3019, 2)]

theorem rawRowCheck7719 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form4 = rawRow7719 := by decide +kernel

def row7719 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7719 : row7719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7719 := by decide +kernel

theorem rowEval7719 (x : Key → ℝ) : Integer.Sparse.eval row7719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7719, Integer.Sparse.eval_collectBalanced, rawRowCheck7719]

def rawRow7720 : Integer.Sparse Key := [(key2404, -6), (key2404, -6), (key2398, -6), (key2435, -6), (key2589, 2), (key2589, 2), (key2583, 2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key3019, 2)]

theorem rawRowCheck7720 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form4 = rawRow7720 := by decide +kernel

def row7720 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7720 : row7720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7720 := by decide +kernel

theorem rowEval7720 (x : Key → ℝ) : Integer.Sparse.eval row7720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7720, Integer.Sparse.eval_collectBalanced, rawRowCheck7720]

def rawRow7721 : Integer.Sparse Key := [(key2398, -6), (key2404, -6), (key2435, -6), (key2404, -6), (key2839, 2), (key2845, 2), (key3019, 2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2589, 2), (key2845, 2), (key2876, 2)]

theorem rawRowCheck7721 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form4 = rawRow7721 := by decide +kernel

def row7721 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7721 : row7721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7721 := by decide +kernel

theorem rowEval7721 (x : Key → ℝ) : Integer.Sparse.eval row7721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7721, Integer.Sparse.eval_collectBalanced, rawRowCheck7721]

def rawRow7722 : Integer.Sparse Key := [(key2404, -6), (key2398, -6), (key2435, -6), (key2404, -6), (key2845, 2), (key2839, 2), (key3019, 2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2589, 2), (key2876, 2), (key2845, 2)]

theorem rawRowCheck7722 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form4 = rawRow7722 := by decide +kernel

def row7722 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7722 : row7722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7722 := by decide +kernel

theorem rowEval7722 (x : Key → ℝ) : Integer.Sparse.eval row7722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7722, Integer.Sparse.eval_collectBalanced, rawRowCheck7722]

def rawRow7723 : Integer.Sparse Key := [(key2398, -6), (key2435, -6), (key2404, -6), (key2404, -6), (key2839, 2), (key3019, 2), (key2845, 2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2845, 2), (key2589, 2), (key2876, 2)]

theorem rawRowCheck7723 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form4 = rawRow7723 := by decide +kernel

def row7723 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7723 : row7723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7723 := by decide +kernel

theorem rowEval7723 (x : Key → ℝ) : Integer.Sparse.eval row7723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7723, Integer.Sparse.eval_collectBalanced, rawRowCheck7723]

def rawRow7724 : Integer.Sparse Key := [(key2435, -6), (key2398, -6), (key2404, -6), (key2404, -6), (key3019, 2), (key2839, 2), (key2845, 2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2845, 2), (key2876, 2), (key2589, 2)]

theorem rawRowCheck7724 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form4 = rawRow7724 := by decide +kernel

def row7724 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7724 : row7724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7724 := by decide +kernel

theorem rowEval7724 (x : Key → ℝ) : Integer.Sparse.eval row7724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7724, Integer.Sparse.eval_collectBalanced, rawRowCheck7724]

def rawRow7725 : Integer.Sparse Key := [(key2404, -6), (key2435, -6), (key2398, -6), (key2404, -6), (key2845, 2), (key3019, 2), (key2839, 2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2876, 2), (key2589, 2), (key2845, 2)]

theorem rawRowCheck7725 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form4 = rawRow7725 := by decide +kernel

def row7725 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7725 : row7725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7725 := by decide +kernel

theorem rowEval7725 (x : Key → ℝ) : Integer.Sparse.eval row7725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7725, Integer.Sparse.eval_collectBalanced, rawRowCheck7725]

def rawRow7726 : Integer.Sparse Key := [(key2435, -6), (key2404, -6), (key2398, -6), (key2404, -6), (key3019, 2), (key2845, 2), (key2839, 2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2876, 2), (key2845, 2), (key2589, 2)]

theorem rawRowCheck7726 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form4 = rawRow7726 := by decide +kernel

def row7726 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7726 : row7726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7726 := by decide +kernel

theorem rowEval7726 (x : Key → ℝ) : Integer.Sparse.eval row7726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7726, Integer.Sparse.eval_collectBalanced, rawRowCheck7726]

def rawRow7727 : Integer.Sparse Key := [(key2404, -6), (key2404, -6), (key2435, -6), (key2398, -6), (key2876, 2), (key2876, 2), (key3028, 2), (key2589, 2), (key2589, 2), (key2845, 2), (key2845, 2), (key3019, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2839, 2)]

theorem rawRowCheck7727 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form4 = rawRow7727 := by decide +kernel

def row7727 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7727 : row7727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7727 := by decide +kernel

theorem rowEval7727 (x : Key → ℝ) : Integer.Sparse.eval row7727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7727, Integer.Sparse.eval_collectBalanced, rawRowCheck7727]

def rawRow7728 : Integer.Sparse Key := [(key2404, -6), (key2435, -6), (key2404, -6), (key2398, -6), (key2876, 2), (key3028, 2), (key2876, 2), (key2845, 2), (key3019, 2), (key2589, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2839, 2), (key2583, 2), (key2839, 2)]

theorem rawRowCheck7728 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form4 = rawRow7728 := by decide +kernel

def row7728 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7728 : row7728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7728 := by decide +kernel

theorem rowEval7728 (x : Key → ℝ) : Integer.Sparse.eval row7728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7728, Integer.Sparse.eval_collectBalanced, rawRowCheck7728]

def rawRow7729 : Integer.Sparse Key := [(key2435, -6), (key2404, -6), (key2404, -6), (key2398, -6), (key3028, 2), (key2876, 2), (key2876, 2), (key3019, 2), (key2845, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2589, 2), (key2839, 2), (key2839, 2), (key2583, 2)]

theorem rawRowCheck7729 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form4 = rawRow7729 := by decide +kernel

def row7729 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

theorem rowCheck7729 : row7729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7729 := by decide +kernel

theorem rowEval7729 (x : Key → ℝ) : Integer.Sparse.eval row7729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7729, Integer.Sparse.eval_collectBalanced, rawRowCheck7729]

def rawRow7730 : Integer.Sparse Key := [(key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2370, 2), (key2376, 2), (key2388, 2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

theorem rawRowCheck7730 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form4 = rawRow7730 := by decide +kernel

def row7730 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7730 : row7730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7730 := by decide +kernel

theorem rowEval7730 (x : Key → ℝ) : Integer.Sparse.eval row7730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7730, Integer.Sparse.eval_collectBalanced, rawRowCheck7730]

def rawRow7731 : Integer.Sparse Key := [(key2470, -6), (key2464, -6), (key2478, -6), (key2501, -6), (key2376, 2), (key2370, 2), (key2388, 2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key3005, 2), (key3028, 2), (key3019, 2)]

theorem rawRowCheck7731 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form4 = rawRow7731 := by decide +kernel

def row7731 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7731 : row7731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7731 := by decide +kernel

theorem rowEval7731 (x : Key → ℝ) : Integer.Sparse.eval row7731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7731, Integer.Sparse.eval_collectBalanced, rawRowCheck7731]

def rawRow7732 : Integer.Sparse Key := [(key2464, -6), (key2478, -6), (key2470, -6), (key2501, -6), (key2370, 2), (key2388, 2), (key2376, 2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key3019, 2), (key3005, 2), (key3028, 2)]

theorem rawRowCheck7732 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form4 = rawRow7732 := by decide +kernel

def row7732 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7732 : row7732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7732 := by decide +kernel

theorem rowEval7732 (x : Key → ℝ) : Integer.Sparse.eval row7732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7732, Integer.Sparse.eval_collectBalanced, rawRowCheck7732]

def rawRow7733 : Integer.Sparse Key := [(key2478, -6), (key2464, -6), (key2470, -6), (key2501, -6), (key2388, 2), (key2370, 2), (key2376, 2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key3019, 2), (key3028, 2), (key3005, 2)]

theorem rawRowCheck7733 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form4 = rawRow7733 := by decide +kernel

def row7733 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7733 : row7733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7733 := by decide +kernel

theorem rowEval7733 (x : Key → ℝ) : Integer.Sparse.eval row7733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7733, Integer.Sparse.eval_collectBalanced, rawRowCheck7733]

def rawRow7734 : Integer.Sparse Key := [(key2470, -6), (key2478, -6), (key2464, -6), (key2501, -6), (key2376, 2), (key2388, 2), (key2370, 2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key3028, 2), (key3005, 2), (key3019, 2)]

theorem rawRowCheck7734 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form4 = rawRow7734 := by decide +kernel

def row7734 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7734 : row7734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7734 := by decide +kernel

theorem rowEval7734 (x : Key → ℝ) : Integer.Sparse.eval row7734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7734, Integer.Sparse.eval_collectBalanced, rawRowCheck7734]

def rawRow7735 : Integer.Sparse Key := [(key2478, -6), (key2470, -6), (key2464, -6), (key2501, -6), (key2388, 2), (key2376, 2), (key2370, 2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key3028, 2), (key3019, 2), (key3005, 2)]

theorem rawRowCheck7735 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form4 = rawRow7735 := by decide +kernel

def row7735 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7735 : row7735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7735 := by decide +kernel

theorem rowEval7735 (x : Key → ℝ) : Integer.Sparse.eval row7735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7735, Integer.Sparse.eval_collectBalanced, rawRowCheck7735]

def rawRow7736 : Integer.Sparse Key := [(key2464, -6), (key2470, -6), (key2501, -6), (key2478, -6), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2604, 2), (key2916, 2), (key2925, 2)]

theorem rawRowCheck7736 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form4 = rawRow7736 := by decide +kernel

def row7736 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7736 : row7736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7736 := by decide +kernel

theorem rowEval7736 (x : Key → ℝ) : Integer.Sparse.eval row7736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7736, Integer.Sparse.eval_collectBalanced, rawRowCheck7736]

def rawRow7737 : Integer.Sparse Key := [(key2470, -6), (key2464, -6), (key2501, -6), (key2478, -6), (key2404, 2), (key2398, 2), (key2435, 2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2604, 2), (key2925, 2), (key2916, 2)]

theorem rawRowCheck7737 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form4 = rawRow7737 := by decide +kernel

def row7737 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7737 : row7737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7737 := by decide +kernel

theorem rowEval7737 (x : Key → ℝ) : Integer.Sparse.eval row7737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7737, Integer.Sparse.eval_collectBalanced, rawRowCheck7737]

def rawRow7738 : Integer.Sparse Key := [(key2464, -6), (key2501, -6), (key2470, -6), (key2478, -6), (key2398, 2), (key2435, 2), (key2404, 2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2916, 2), (key2604, 2), (key2925, 2)]

theorem rawRowCheck7738 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form4 = rawRow7738 := by decide +kernel

def row7738 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7738 : row7738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7738 := by decide +kernel

theorem rowEval7738 (x : Key → ℝ) : Integer.Sparse.eval row7738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7738, Integer.Sparse.eval_collectBalanced, rawRowCheck7738]

def rawRow7739 : Integer.Sparse Key := [(key2501, -6), (key2464, -6), (key2470, -6), (key2478, -6), (key2435, 2), (key2398, 2), (key2404, 2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2916, 2), (key2925, 2), (key2604, 2)]

theorem rawRowCheck7739 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form4 = rawRow7739 := by decide +kernel

def row7739 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7739 : row7739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7739 := by decide +kernel

theorem rowEval7739 (x : Key → ℝ) : Integer.Sparse.eval row7739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7739, Integer.Sparse.eval_collectBalanced, rawRowCheck7739]

def rawRow7740 : Integer.Sparse Key := [(key2470, -6), (key2501, -6), (key2464, -6), (key2478, -6), (key2404, 2), (key2435, 2), (key2398, 2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2925, 2), (key2604, 2), (key2916, 2)]

theorem rawRowCheck7740 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form4 = rawRow7740 := by decide +kernel

def row7740 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7740 : row7740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7740 := by decide +kernel

theorem rowEval7740 (x : Key → ℝ) : Integer.Sparse.eval row7740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7740, Integer.Sparse.eval_collectBalanced, rawRowCheck7740]

def rawRow7741 : Integer.Sparse Key := [(key2501, -6), (key2470, -6), (key2464, -6), (key2478, -6), (key2435, 2), (key2404, 2), (key2398, 2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2925, 2), (key2916, 2), (key2604, 2)]

theorem rawRowCheck7741 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form4 = rawRow7741 := by decide +kernel

def row7741 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

theorem rowCheck7741 : row7741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7741 := by decide +kernel

theorem rowEval7741 (x : Key → ℝ) : Integer.Sparse.eval row7741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7741, Integer.Sparse.eval_collectBalanced, rawRowCheck7741]

def rawRow7742 : Integer.Sparse Key := [(key2464, -6), (key2478, -6), (key2501, -6), (key2470, -6), (key2464, 2), (key2478, 2), (key2501, 2), (key2370, 2), (key2388, 2), (key2762, 2), (key2925, 2), (key3005, 2), (key3028, 2), (key2589, 2), (key2768, 2), (key2876, 2)]

theorem rawRowCheck7742 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form4 = rawRow7742 := by decide +kernel

def row7742 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2589, 2), (key2762, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3005, 2), (key3028, 2)]

theorem rowCheck7742 : row7742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7742 := by decide +kernel

theorem rowEval7742 (x : Key → ℝ) : Integer.Sparse.eval row7742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7742, Integer.Sparse.eval_collectBalanced, rawRowCheck7742]

def rawRow7743 : Integer.Sparse Key := [(key2478, -6), (key2464, -6), (key2501, -6), (key2470, -6), (key2478, 2), (key2464, 2), (key2501, 2), (key2388, 2), (key2370, 2), (key2925, 2), (key2762, 2), (key3028, 2), (key3005, 2), (key2589, 2), (key2876, 2), (key2768, 2)]

theorem rawRowCheck7743 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form4 = rawRow7743 := by decide +kernel

def row7743 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2589, 2), (key2762, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3005, 2), (key3028, 2)]

theorem rowCheck7743 : row7743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7743 := by decide +kernel

theorem rowEval7743 (x : Key → ℝ) : Integer.Sparse.eval row7743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7743, Integer.Sparse.eval_collectBalanced, rawRowCheck7743]

def rawRow7744 : Integer.Sparse Key := [(key2464, -6), (key2501, -6), (key2478, -6), (key2470, -6), (key2464, 2), (key2501, 2), (key2478, 2), (key2398, 2), (key2435, 2), (key2583, 2), (key3028, 2), (key2604, 2), (key2925, 2), (key2768, 2), (key2589, 2), (key2876, 2)]

theorem rawRowCheck7744 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form4 = rawRow7744 := by decide +kernel

def row7744 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, 2), (key2604, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3028, 2)]

theorem rowCheck7744 : row7744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7744 := by decide +kernel

theorem rowEval7744 (x : Key → ℝ) : Integer.Sparse.eval row7744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7744, Integer.Sparse.eval_collectBalanced, rawRowCheck7744]

def rawRow7745 : Integer.Sparse Key := [(key2501, -6), (key2464, -6), (key2478, -6), (key2470, -6), (key2501, 2), (key2464, 2), (key2478, 2), (key2435, 2), (key2398, 2), (key3028, 2), (key2583, 2), (key2925, 2), (key2604, 2), (key2768, 2), (key2876, 2), (key2589, 2)]

theorem rawRowCheck7745 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form4 = rawRow7745 := by decide +kernel

def row7745 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, 2), (key2604, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3028, 2)]

theorem rowCheck7745 : row7745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7745 := by decide +kernel

theorem rowEval7745 (x : Key → ℝ) : Integer.Sparse.eval row7745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7745, Integer.Sparse.eval_collectBalanced, rawRowCheck7745]

def rawRow7746 : Integer.Sparse Key := [(key2478, -6), (key2501, -6), (key2464, -6), (key2470, -6), (key2478, 2), (key2501, 2), (key2464, 2), (key2570, 2), (key2575, 2), (key2388, 2), (key2435, 2), (key2370, 2), (key2762, 2), (key2876, 2), (key2589, 2), (key2768, 2)]

theorem rawRowCheck7746 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form4 = rawRow7746 := by decide +kernel

def row7746 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, 2), (key2768, 2), (key2876, 2)]

theorem rowCheck7746 : row7746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7746 := by decide +kernel

theorem rowEval7746 (x : Key → ℝ) : Integer.Sparse.eval row7746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7746, Integer.Sparse.eval_collectBalanced, rawRowCheck7746]

def rawRow7747 : Integer.Sparse Key := [(key2501, -6), (key2478, -6), (key2464, -6), (key2470, -6), (key2501, 2), (key2478, 2), (key2464, 2), (key2575, 2), (key2570, 2), (key2435, 2), (key2388, 2), (key2398, 2), (key2583, 2), (key2876, 2), (key2768, 2), (key2589, 2)]

theorem rawRowCheck7747 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form4 = rawRow7747 := by decide +kernel

def row7747 : Integer.Sparse Key := [(key2388, 2), (key2398, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2583, 2), (key2589, 2), (key2768, 2), (key2876, 2)]

theorem rowCheck7747 : row7747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7747 := by decide +kernel

theorem rowEval7747 (x : Key → ℝ) : Integer.Sparse.eval row7747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7747, Integer.Sparse.eval_collectBalanced, rawRowCheck7747]

def rawRow7748 : Integer.Sparse Key := [(key2470, -6), (key2478, -6), (key2501, -6), (key2464, -6), (key2568, 2), (key2570, 2), (key2575, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2370, 2), (key2762, 2), (key2839, 2)]

theorem rawRowCheck7748 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form4 = rawRow7748 := by decide +kernel

def row7748 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2762, 2), (key2839, 2)]

theorem rowCheck7748 : row7748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7748 := by decide +kernel

theorem rowEval7748 (x : Key → ℝ) : Integer.Sparse.eval row7748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7748, Integer.Sparse.eval_collectBalanced, rawRowCheck7748]

def rawRow7749 : Integer.Sparse Key := [(key2478, -6), (key2470, -6), (key2501, -6), (key2464, -6), (key2570, 2), (key2568, 2), (key2575, 2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2370, 2), (key2839, 2), (key2762, 2)]

theorem rawRowCheck7749 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form4 = rawRow7749 := by decide +kernel

def row7749 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2762, 2), (key2839, 2)]

theorem rowCheck7749 : row7749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7749 := by decide +kernel

theorem rowEval7749 (x : Key → ℝ) : Integer.Sparse.eval row7749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7749, Integer.Sparse.eval_collectBalanced, rawRowCheck7749]

def rawRow7750 : Integer.Sparse Key := [(key2470, -6), (key2501, -6), (key2478, -6), (key2464, -6), (key2568, 2), (key2575, 2), (key2570, 2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2398, 2), (key2583, 2), (key2839, 2)]

theorem rawRowCheck7750 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form4 = rawRow7750 := by decide +kernel

def row7750 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, 2), (key2839, 2)]

theorem rowCheck7750 : row7750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7750 := by decide +kernel

theorem rowEval7750 (x : Key → ℝ) : Integer.Sparse.eval row7750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck7750, Integer.Sparse.eval_collectBalanced, rawRowCheck7750]

def rawRow7751 : Integer.Sparse Key := [(key2501, -6), (key2470, -6), (key2478, -6), (key2464, -6), (key2575, 2), (key2568, 2), (key2570, 2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2398, 2), (key2839, 2), (key2583, 2)]

theorem rawRowCheck7751 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form4 = rawRow7751 := by decide +kernel

def row7751 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, 2), (key2839, 2)]

theorem rowCheck7751 : row7751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7751 := by decide +kernel

theorem rowEval7751 (x : Key → ℝ) : Integer.Sparse.eval row7751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7751, Integer.Sparse.eval_collectBalanced, rawRowCheck7751]

def rawRow7752 : Integer.Sparse Key := [(key2478, -6), (key2501, -6), (key2470, -6), (key2464, -6), (key2570, 2), (key2575, 2), (key2568, 2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2464, 2), (key2370, 2), (key2762, 2)]

theorem rawRowCheck7752 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form4 = rawRow7752 := by decide +kernel

def row7752 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2762, 2)]

theorem rowCheck7752 : row7752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7752 := by decide +kernel

theorem rowEval7752 (x : Key → ℝ) : Integer.Sparse.eval row7752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck7752, Integer.Sparse.eval_collectBalanced, rawRowCheck7752]

def rawRow7753 : Integer.Sparse Key := [(key2501, -6), (key2478, -6), (key2470, -6), (key2464, -6), (key2575, 2), (key2570, 2), (key2568, 2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2464, 2), (key2398, 2), (key2583, 2)]

theorem rawRowCheck7753 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form4 = rawRow7753 := by decide +kernel

def row7753 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, 2), (key2404, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, 2)]

theorem rowCheck7753 : row7753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7753 := by decide +kernel

theorem rowEval7753 (x : Key → ℝ) : Integer.Sparse.eval row7753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck7753, Integer.Sparse.eval_collectBalanced, rawRowCheck7753]

def rawRow7754 : Integer.Sparse Key := [(key2608, -2), (key2614, -2), (key2614, -2), (key2801, -2), (key2807, -2), (key2801, -2), (key2827, -2), (key2807, -2), (key2827, -2), (key3011, -2), (key3011, -2), (key3016, -2), (key2624, 1), (key2630, 1), (key2624, 1), (key2638, 1), (key2630, 1), (key2638, 1), (key2698, 1), (key2704, 1), (key2698, 1), (key2724, 1), (key2704, 1), (key2724, 1), (key2851, 1), (key2858, 1), (key2851, 1), (key2868, 1), (key2858, 1), (key2868, 1), (key3021, 1), (key3022, 1), (key3021, 1), (key3025, 1), (key3022, 1), (key3025, 1)]

theorem rawRowCheck7754 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form5 = rawRow7754 := by decide +kernel

def row7754 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7754 : row7754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7754 := by decide +kernel

theorem rowEval7754 (x : Key → ℝ) : Integer.Sparse.eval row7754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7754, Integer.Sparse.eval_collectBalanced, rawRowCheck7754]

def rawRow7755 : Integer.Sparse Key := [(key2614, -2), (key2608, -2), (key2614, -2), (key2807, -2), (key2801, -2), (key2827, -2), (key2801, -2), (key2827, -2), (key2807, -2), (key3011, -2), (key3016, -2), (key3011, -2), (key2630, 1), (key2624, 1), (key2638, 1), (key2624, 1), (key2638, 1), (key2630, 1), (key2704, 1), (key2698, 1), (key2724, 1), (key2698, 1), (key2724, 1), (key2704, 1), (key2858, 1), (key2851, 1), (key2868, 1), (key2851, 1), (key2868, 1), (key2858, 1), (key3022, 1), (key3021, 1), (key3025, 1), (key3021, 1), (key3025, 1), (key3022, 1)]

theorem rawRowCheck7755 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form5 = rawRow7755 := by decide +kernel

def row7755 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7755 : row7755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7755 := by decide +kernel

theorem rowEval7755 (x : Key → ℝ) : Integer.Sparse.eval row7755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7755, Integer.Sparse.eval_collectBalanced, rawRowCheck7755]

def rawRow7756 : Integer.Sparse Key := [(key2614, -2), (key2614, -2), (key2608, -2), (key2827, -2), (key2827, -2), (key2807, -2), (key2807, -2), (key2801, -2), (key2801, -2), (key3016, -2), (key3011, -2), (key3011, -2), (key2638, 1), (key2638, 1), (key2630, 1), (key2630, 1), (key2624, 1), (key2624, 1), (key2724, 1), (key2724, 1), (key2704, 1), (key2704, 1), (key2698, 1), (key2698, 1), (key2868, 1), (key2868, 1), (key2858, 1), (key2858, 1), (key2851, 1), (key2851, 1), (key3025, 1), (key3025, 1), (key3022, 1), (key3022, 1), (key3021, 1), (key3021, 1)]

theorem rawRowCheck7756 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form5 = rawRow7756 := by decide +kernel

def row7756 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7756 : row7756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7756 := by decide +kernel

theorem rowEval7756 (x : Key → ℝ) : Integer.Sparse.eval row7756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7756, Integer.Sparse.eval_collectBalanced, rawRowCheck7756]

def rawRow7757 : Integer.Sparse Key := [(key2801, -2), (key2807, -2), (key2827, -2), (key2608, -2), (key2614, -2), (key2801, -2), (key2827, -2), (key3011, -2), (key3016, -2), (key2614, -2), (key2807, -2), (key2827, -2), (key2698, 1), (key2704, 1), (key2851, 1), (key2858, 1), (key3021, 1), (key3022, 1), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key2724, 1), (key3022, 1), (key3025, 1), (key2630, 1), (key2638, 1), (key2704, 1), (key2724, 1), (key2858, 1), (key2868, 1)]

theorem rawRowCheck7757 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form5 = rawRow7757 := by decide +kernel

def row7757 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7757 : row7757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7757 := by decide +kernel

theorem rowEval7757 (x : Key → ℝ) : Integer.Sparse.eval row7757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7757, Integer.Sparse.eval_collectBalanced, rawRowCheck7757]

def rawRow7758 : Integer.Sparse Key := [(key2807, -2), (key2801, -2), (key2827, -2), (key2614, -2), (key2608, -2), (key2827, -2), (key2801, -2), (key3016, -2), (key3011, -2), (key2614, -2), (key2827, -2), (key2807, -2), (key2704, 1), (key2698, 1), (key2858, 1), (key2851, 1), (key3022, 1), (key3021, 1), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1), (key2638, 1), (key2624, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key3022, 1), (key2638, 1), (key2630, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2858, 1)]

theorem rawRowCheck7758 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form5 = rawRow7758 := by decide +kernel

def row7758 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7758 : row7758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7758 := by decide +kernel

theorem rowEval7758 (x : Key → ℝ) : Integer.Sparse.eval row7758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7758, Integer.Sparse.eval_collectBalanced, rawRowCheck7758]

def rawRow7759 : Integer.Sparse Key := [(key2801, -2), (key2827, -2), (key2807, -2), (key2801, -2), (key2827, -2), (key2608, -2), (key3016, -2), (key2614, -2), (key2827, -2), (key2807, -2), (key2614, -2), (key2827, -2), (key2851, 1), (key3021, 1), (key2698, 1), (key3022, 1), (key2704, 1), (key2858, 1), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2698, 1), (key3022, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2704, 1), (key2858, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2724, 1)]

theorem rawRowCheck7759 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form5 = rawRow7759 := by decide +kernel

def row7759 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -8), (key2851, 2), (key2858, 2), (key2868, 2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7759 : row7759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7759 := by decide +kernel

theorem rowEval7759 (x : Key → ℝ) : Integer.Sparse.eval row7759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7759, Integer.Sparse.eval_collectBalanced, rawRowCheck7759]

def rawRow7760 : Integer.Sparse Key := [(key2827, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2801, -2), (key3016, -2), (key2608, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2827, -2), (key2614, -2), (key3021, 1), (key2851, 1), (key3022, 1), (key2698, 1), (key2858, 1), (key2704, 1), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key2724, 1), (key2638, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2724, 1), (key2638, 1)]

theorem rawRowCheck7760 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form5 = rawRow7760 := by decide +kernel

def row7760 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -8), (key2851, 2), (key2858, 2), (key2868, 2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7760 : row7760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7760 := by decide +kernel

theorem rowEval7760 (x : Key → ℝ) : Integer.Sparse.eval row7760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7760, Integer.Sparse.eval_collectBalanced, rawRowCheck7760]

def rawRow7761 : Integer.Sparse Key := [(key2807, -2), (key2827, -2), (key2801, -2), (key3011, -2), (key3016, -2), (key2614, -2), (key2827, -2), (key2608, -2), (key2801, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2858, 1), (key3022, 1), (key2704, 1), (key3021, 1), (key2698, 1), (key2851, 1), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1), (key2724, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2624, 1), (key2698, 1), (key2724, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2630, 1), (key2704, 1)]

theorem rawRowCheck7761 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form5 = rawRow7761 := by decide +kernel

def row7761 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7761 : row7761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7761 := by decide +kernel

theorem rowEval7761 (x : Key → ℝ) : Integer.Sparse.eval row7761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7761, Integer.Sparse.eval_collectBalanced, rawRowCheck7761]

def rawRow7762 : Integer.Sparse Key := [(key2827, -2), (key2807, -2), (key2801, -2), (key3016, -2), (key3011, -2), (key2827, -2), (key2614, -2), (key2801, -2), (key2608, -2), (key2827, -2), (key2807, -2), (key2614, -2), (key3022, 1), (key2858, 1), (key3021, 1), (key2704, 1), (key2851, 1), (key2698, 1), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key3025, 1), (key2724, 1), (key3022, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key2868, 1), (key2724, 1), (key2858, 1), (key2638, 1), (key2704, 1), (key2630, 1)]

theorem rawRowCheck7762 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form5 = rawRow7762 := by decide +kernel

def row7762 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7762 : row7762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7762 := by decide +kernel

theorem rowEval7762 (x : Key → ℝ) : Integer.Sparse.eval row7762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7762, Integer.Sparse.eval_collectBalanced, rawRowCheck7762]

def rawRow7763 : Integer.Sparse Key := [(key3011, -2), (key3011, -2), (key3016, -2), (key2614, -2), (key2614, -2), (key2807, -2), (key2807, -2), (key2827, -2), (key2827, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2724, 1), (key2724, 1), (key2868, 1), (key2868, 1), (key3025, 1), (key3025, 1), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1), (key2630, 1), (key2630, 1), (key2704, 1), (key2704, 1), (key3021, 1), (key3021, 1), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

theorem rawRowCheck7763 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form5 = rawRow7763 := by decide +kernel

def row7763 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7763 : row7763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7763 := by decide +kernel

theorem rowEval7763 (x : Key → ℝ) : Integer.Sparse.eval row7763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7763, Integer.Sparse.eval_collectBalanced, rawRowCheck7763]

def rawRow7764 : Integer.Sparse Key := [(key3011, -2), (key3016, -2), (key3011, -2), (key2807, -2), (key2827, -2), (key2614, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2868, 1), (key3025, 1), (key2724, 1), (key3025, 1), (key2724, 1), (key2868, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2704, 1), (key3021, 1), (key2630, 1), (key3021, 1), (key2630, 1), (key2704, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

theorem rawRowCheck7764 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form5 = rawRow7764 := by decide +kernel

def row7764 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7764 : row7764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7764 := by decide +kernel

theorem rowEval7764 (x : Key → ℝ) : Integer.Sparse.eval row7764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7764, Integer.Sparse.eval_collectBalanced, rawRowCheck7764]

def rawRow7765 : Integer.Sparse Key := [(key3016, -2), (key3011, -2), (key3011, -2), (key2827, -2), (key2807, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2614, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key3025, 1), (key2868, 1), (key3025, 1), (key2724, 1), (key2868, 1), (key2724, 1), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key3021, 1), (key2704, 1), (key3021, 1), (key2630, 1), (key2704, 1), (key2630, 1), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

theorem rawRowCheck7765 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form5 = rawRow7765 := by decide +kernel

def row7765 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

theorem rowCheck7765 : row7765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7765 := by decide +kernel

theorem rowEval7765 (x : Key → ℝ) : Integer.Sparse.eval row7765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7765, Integer.Sparse.eval_collectBalanced, rawRowCheck7765]

def rawRow7766 : Integer.Sparse Key := [(key2624, -2), (key2630, -2), (key2638, -2), (key2698, -2), (key2704, -2), (key2851, -2), (key3021, -2), (key2858, -2), (key3022, -2), (key2724, -2), (key2868, -2), (key3025, -2), (key2608, 1), (key2614, 1), (key2624, 1), (key2638, 1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

theorem rawRowCheck7766 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form5 = rawRow7766 := by decide +kernel

def row7766 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7766 : row7766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7766 := by decide +kernel

theorem rowEval7766 (x : Key → ℝ) : Integer.Sparse.eval row7766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7766, Integer.Sparse.eval_collectBalanced, rawRowCheck7766]

def rawRow7767 : Integer.Sparse Key := [(key2630, -2), (key2624, -2), (key2638, -2), (key2704, -2), (key2698, -2), (key3021, -2), (key2851, -2), (key3022, -2), (key2858, -2), (key2724, -2), (key3025, -2), (key2868, -2), (key2614, 1), (key2608, 1), (key2638, 1), (key2624, 1), (key2659, 1), (key2657, 1), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2792, 1), (key2778, 1), (key2827, 1), (key2801, 1), (key2922, 1), (key2919, 1), (key3009, 1), (key3007, 1), (key3016, 1), (key3011, 1), (key3025, 1), (key3022, 1)]

theorem rawRowCheck7767 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form5 = rawRow7767 := by decide +kernel

def row7767 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7767 : row7767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7767 := by decide +kernel

theorem rowEval7767 (x : Key → ℝ) : Integer.Sparse.eval row7767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7767, Integer.Sparse.eval_collectBalanced, rawRowCheck7767]

def rawRow7768 : Integer.Sparse Key := [(key2624, -2), (key2638, -2), (key2630, -2), (key2851, -2), (key2858, -2), (key2698, -2), (key3022, -2), (key2704, -2), (key3021, -2), (key2868, -2), (key2724, -2), (key3025, -2), (key2624, 1), (key2638, 1), (key2608, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2801, 1), (key2919, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key3011, 1), (key3022, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3016, 1)]

theorem rawRowCheck7768 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form5 = rawRow7768 := by decide +kernel

def row7768 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7768 : row7768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7768 := by decide +kernel

theorem rowEval7768 (x : Key → ℝ) : Integer.Sparse.eval row7768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7768, Integer.Sparse.eval_collectBalanced, rawRowCheck7768]

def rawRow7769 : Integer.Sparse Key := [(key2638, -2), (key2624, -2), (key2630, -2), (key2858, -2), (key2851, -2), (key3022, -2), (key2698, -2), (key3021, -2), (key2704, -2), (key2868, -2), (key3025, -2), (key2724, -2), (key2638, 1), (key2624, 1), (key2659, 1), (key2608, 1), (key2638, 1), (key2614, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2827, 1), (key2792, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3016, 1), (key3009, 1)]

theorem rawRowCheck7769 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form5 = rawRow7769 := by decide +kernel

def row7769 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7769 : row7769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7769 := by decide +kernel

theorem rowEval7769 (x : Key → ℝ) : Integer.Sparse.eval row7769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7769, Integer.Sparse.eval_collectBalanced, rawRowCheck7769]

def rawRow7770 : Integer.Sparse Key := [(key2630, -2), (key2638, -2), (key2624, -2), (key3021, -2), (key3022, -2), (key2704, -2), (key2858, -2), (key2698, -2), (key2851, -2), (key3025, -2), (key2724, -2), (key2868, -2), (key2657, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2608, 1), (key2624, 1), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2827, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2778, 1), (key2801, 1), (key3016, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key3007, 1), (key3011, 1)]

theorem rawRowCheck7770 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form5 = rawRow7770 := by decide +kernel

def row7770 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7770 : row7770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7770 := by decide +kernel

theorem rowEval7770 (x : Key → ℝ) : Integer.Sparse.eval row7770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7770, Integer.Sparse.eval_collectBalanced, rawRowCheck7770]

def rawRow7771 : Integer.Sparse Key := [(key2638, -2), (key2630, -2), (key2624, -2), (key3022, -2), (key3021, -2), (key2858, -2), (key2704, -2), (key2851, -2), (key2698, -2), (key3025, -2), (key2868, -2), (key2724, -2), (key2659, 1), (key2657, 1), (key2638, 1), (key2614, 1), (key2624, 1), (key2608, 1), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2922, 1), (key2827, 1), (key2919, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key3025, 1), (key3016, 1), (key3022, 1), (key3009, 1), (key3011, 1), (key3007, 1)]

theorem rawRowCheck7771 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form5 = rawRow7771 := by decide +kernel

def row7771 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7771 : row7771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7771 := by decide +kernel

theorem rowEval7771 (x : Key → ℝ) : Integer.Sparse.eval row7771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7771, Integer.Sparse.eval_collectBalanced, rawRowCheck7771]

def rawRow7772 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2624, -2), (key2630, -2), (key2851, -2), (key3021, -2), (key2868, -2), (key3025, -2), (key2638, -2), (key2858, -2), (key3022, -2), (key2663, 1), (key2669, 1), (key2698, 1), (key2752, 1), (key2724, 1), (key2757, 1), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key2724, 1), (key3022, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2752, 1), (key2757, 1), (key2919, 1), (key2922, 1)]

theorem rawRowCheck7772 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form5 = rawRow7772 := by decide +kernel

def row7772 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7772 : row7772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7772 := by decide +kernel

theorem rowEval7772 (x : Key → ℝ) : Integer.Sparse.eval row7772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7772, Integer.Sparse.eval_collectBalanced, rawRowCheck7772]

def rawRow7773 : Integer.Sparse Key := [(key2704, -2), (key2698, -2), (key2724, -2), (key2630, -2), (key2624, -2), (key3021, -2), (key2851, -2), (key3025, -2), (key2868, -2), (key2638, -2), (key3022, -2), (key2858, -2), (key2669, 1), (key2663, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2724, 1), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2638, 1), (key2624, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key3022, 1), (key2659, 1), (key2657, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2919, 1)]

theorem rawRowCheck7773 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form5 = rawRow7773 := by decide +kernel

def row7773 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7773 : row7773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7773 := by decide +kernel

theorem rowEval7773 (x : Key → ℝ) : Integer.Sparse.eval row7773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7773, Integer.Sparse.eval_collectBalanced, rawRowCheck7773]

def rawRow7774 : Integer.Sparse Key := [(key2698, -2), (key2724, -2), (key2704, -2), (key2851, -2), (key2868, -2), (key2624, -2), (key3025, -2), (key2630, -2), (key3021, -2), (key2858, -2), (key2638, -2), (key3022, -2), (key2698, 1), (key2724, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2698, 1), (key3022, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2752, 1), (key2919, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2757, 1)]

theorem rawRowCheck7774 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form5 = rawRow7774 := by decide +kernel

def row7774 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7774 : row7774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7774 := by decide +kernel

theorem rowEval7774 (x : Key → ℝ) : Integer.Sparse.eval row7774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7774, Integer.Sparse.eval_collectBalanced, rawRowCheck7774]

def rawRow7775 : Integer.Sparse Key := [(key2724, -2), (key2698, -2), (key2704, -2), (key2868, -2), (key2851, -2), (key3025, -2), (key2624, -2), (key3021, -2), (key2630, -2), (key2858, -2), (key3022, -2), (key2638, -2), (key2724, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2752, 1), (key2669, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key2724, 1), (key2638, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2757, 1), (key2659, 1)]

theorem rawRowCheck7775 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form5 = rawRow7775 := by decide +kernel

def row7775 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7775 : row7775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7775 := by decide +kernel

theorem rowEval7775 (x : Key → ℝ) : Integer.Sparse.eval row7775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7775, Integer.Sparse.eval_collectBalanced, rawRowCheck7775]

def rawRow7776 : Integer.Sparse Key := [(key2704, -2), (key2724, -2), (key2698, -2), (key3021, -2), (key3025, -2), (key2630, -2), (key2868, -2), (key2624, -2), (key2851, -2), (key3022, -2), (key2638, -2), (key2858, -2), (key2752, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2724, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2624, 1), (key2698, 1), (key2757, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2657, 1), (key2752, 1)]

theorem rawRowCheck7776 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form5 = rawRow7776 := by decide +kernel

def row7776 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7776 : row7776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7776 := by decide +kernel

theorem rowEval7776 (x : Key → ℝ) : Integer.Sparse.eval row7776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7776, Integer.Sparse.eval_collectBalanced, rawRowCheck7776]

def rawRow7777 : Integer.Sparse Key := [(key2724, -2), (key2704, -2), (key2698, -2), (key3025, -2), (key3021, -2), (key2868, -2), (key2630, -2), (key2851, -2), (key2624, -2), (key3022, -2), (key2858, -2), (key2638, -2), (key2757, 1), (key2752, 1), (key2724, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key3025, 1), (key2724, 1), (key3022, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key2922, 1), (key2757, 1), (key2919, 1), (key2659, 1), (key2752, 1), (key2657, 1)]

theorem rawRowCheck7777 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form5 = rawRow7777 := by decide +kernel

def row7777 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7777 : row7777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7777 := by decide +kernel

theorem rowEval7777 (x : Key → ℝ) : Integer.Sparse.eval row7777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7777, Integer.Sparse.eval_collectBalanced, rawRowCheck7777]

def rawRow7778 : Integer.Sparse Key := [(key2851, -2), (key2858, -2), (key2868, -2), (key2624, -2), (key2638, -2), (key2698, -2), (key3022, -2), (key2724, -2), (key3025, -2), (key2630, -2), (key2704, -2), (key3021, -2), (key2778, 1), (key2792, 1), (key2801, 1), (key2919, 1), (key2827, 1), (key2922, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key3022, 1), (key2724, 1), (key3025, 1), (key2608, 1), (key2659, 1), (key2663, 1), (key2757, 1), (key3009, 1), (key3016, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2724, 1), (key2792, 1), (key2827, 1)]

theorem rawRowCheck7778 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form5 = rawRow7778 := by decide +kernel

def row7778 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7778 : row7778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7778 := by decide +kernel

theorem rowEval7778 (x : Key → ℝ) : Integer.Sparse.eval row7778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7778, Integer.Sparse.eval_collectBalanced, rawRowCheck7778]

def rawRow7779 : Integer.Sparse Key := [(key2858, -2), (key2851, -2), (key2868, -2), (key2638, -2), (key2624, -2), (key3022, -2), (key2698, -2), (key3025, -2), (key2724, -2), (key2630, -2), (key3021, -2), (key2704, -2), (key2792, 1), (key2778, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2827, 1), (key2638, 1), (key2624, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2724, 1), (key2659, 1), (key2608, 1), (key2757, 1), (key2663, 1), (key3016, 1), (key3009, 1), (key2638, 1), (key2614, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2792, 1)]

theorem rawRowCheck7779 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form5 = rawRow7779 := by decide +kernel

def row7779 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7779 : row7779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7779 := by decide +kernel

theorem rowEval7779 (x : Key → ℝ) : Integer.Sparse.eval row7779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7779, Integer.Sparse.eval_collectBalanced, rawRowCheck7779]

def rawRow7780 : Integer.Sparse Key := [(key2851, -2), (key2868, -2), (key2858, -2), (key2698, -2), (key2724, -2), (key2624, -2), (key3025, -2), (key2638, -2), (key3022, -2), (key2704, -2), (key2630, -2), (key3021, -2), (key2801, 1), (key2827, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2698, 1), (key2724, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2663, 1), (key2757, 1), (key2608, 1), (key3016, 1), (key2659, 1), (key2757, 1), (key2669, 1), (key2792, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2724, 1)]

theorem rawRowCheck7780 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form5 = rawRow7780 := by decide +kernel

def row7780 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 2), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7780 : row7780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7780 := by decide +kernel

theorem rowEval7780 (x : Key → ℝ) : Integer.Sparse.eval row7780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7780, Integer.Sparse.eval_collectBalanced, rawRowCheck7780]

def rawRow7781 : Integer.Sparse Key := [(key2868, -2), (key2851, -2), (key2858, -2), (key2724, -2), (key2698, -2), (key3025, -2), (key2624, -2), (key3022, -2), (key2638, -2), (key2704, -2), (key3021, -2), (key2630, -2), (key2827, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2919, 1), (key2792, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key3022, 1), (key2638, 1), (key2757, 1), (key2663, 1), (key3016, 1), (key2608, 1), (key2757, 1), (key2659, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2724, 1), (key2638, 1)]

theorem rawRowCheck7781 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form5 = rawRow7781 := by decide +kernel

def row7781 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 2), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7781 : row7781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7781 := by decide +kernel

theorem rowEval7781 (x : Key → ℝ) : Integer.Sparse.eval row7781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7781, Integer.Sparse.eval_collectBalanced, rawRowCheck7781]

def rawRow7782 : Integer.Sparse Key := [(key2858, -2), (key2868, -2), (key2851, -2), (key3022, -2), (key3025, -2), (key2638, -2), (key2724, -2), (key2624, -2), (key2698, -2), (key3021, -2), (key2630, -2), (key2704, -2), (key2919, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key2778, 1), (key2801, 1), (key3022, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2624, 1), (key2698, 1), (key3009, 1), (key3016, 1), (key2659, 1), (key2757, 1), (key2608, 1), (key2663, 1), (key2724, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2614, 1), (key2669, 1)]

theorem rawRowCheck7782 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form5 = rawRow7782 := by decide +kernel

def row7782 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7782 : row7782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7782 := by decide +kernel

theorem rowEval7782 (x : Key → ℝ) : Integer.Sparse.eval row7782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7782, Integer.Sparse.eval_collectBalanced, rawRowCheck7782]

def rawRow7783 : Integer.Sparse Key := [(key2868, -2), (key2858, -2), (key2851, -2), (key3025, -2), (key3022, -2), (key2724, -2), (key2638, -2), (key2698, -2), (key2624, -2), (key3021, -2), (key2704, -2), (key2630, -2), (key2922, 1), (key2919, 1), (key2827, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key3025, 1), (key3022, 1), (key2724, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key3016, 1), (key3009, 1), (key2757, 1), (key2659, 1), (key2663, 1), (key2608, 1), (key2827, 1), (key2724, 1), (key2792, 1), (key2638, 1), (key2669, 1), (key2614, 1)]

theorem rawRowCheck7783 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form5 = rawRow7783 := by decide +kernel

def row7783 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7783 : row7783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7783 := by decide +kernel

theorem rowEval7783 (x : Key → ℝ) : Integer.Sparse.eval row7783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7783, Integer.Sparse.eval_collectBalanced, rawRowCheck7783]

def rawRow7784 : Integer.Sparse Key := [(key3021, -2), (key3022, -2), (key3025, -2), (key2630, -2), (key2638, -2), (key2704, -2), (key2858, -2), (key2724, -2), (key2868, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key3007, 1), (key3009, 1), (key3011, 1), (key3022, 1), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

theorem rawRowCheck7784 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form5 = rawRow7784 := by decide +kernel

def row7784 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7784 : row7784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7784 := by decide +kernel

theorem rowEval7784 (x : Key → ℝ) : Integer.Sparse.eval row7784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7784, Integer.Sparse.eval_collectBalanced, rawRowCheck7784]

def rawRow7785 : Integer.Sparse Key := [(key3022, -2), (key3021, -2), (key3025, -2), (key2638, -2), (key2630, -2), (key2858, -2), (key2704, -2), (key2868, -2), (key2724, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key3009, 1), (key3007, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

theorem rawRowCheck7785 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form5 = rawRow7785 := by decide +kernel

def row7785 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7785 : row7785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7785 := by decide +kernel

theorem rowEval7785 (x : Key → ℝ) : Integer.Sparse.eval row7785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7785, Integer.Sparse.eval_collectBalanced, rawRowCheck7785]

def rawRow7786 : Integer.Sparse Key := [(key3021, -2), (key3025, -2), (key3022, -2), (key2704, -2), (key2724, -2), (key2630, -2), (key2868, -2), (key2638, -2), (key2858, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key3011, 1), (key3016, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

theorem rawRowCheck7786 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form5 = rawRow7786 := by decide +kernel

def row7786 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7786 : row7786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7786 := by decide +kernel

theorem rowEval7786 (x : Key → ℝ) : Integer.Sparse.eval row7786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7786, Integer.Sparse.eval_collectBalanced, rawRowCheck7786]

def rawRow7787 : Integer.Sparse Key := [(key3025, -2), (key3021, -2), (key3022, -2), (key2724, -2), (key2704, -2), (key2868, -2), (key2630, -2), (key2858, -2), (key2638, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key3016, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

theorem rawRowCheck7787 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form5 = rawRow7787 := by decide +kernel

def row7787 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7787 : row7787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7787 := by decide +kernel

theorem rowEval7787 (x : Key → ℝ) : Integer.Sparse.eval row7787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7787, Integer.Sparse.eval_collectBalanced, rawRowCheck7787]

def rawRow7788 : Integer.Sparse Key := [(key3022, -2), (key3025, -2), (key3021, -2), (key2858, -2), (key2868, -2), (key2638, -2), (key2724, -2), (key2630, -2), (key2704, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key3022, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key3007, 1), (key3011, 1), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

theorem rawRowCheck7788 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form5 = rawRow7788 := by decide +kernel

def row7788 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7788 : row7788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7788 := by decide +kernel

theorem rowEval7788 (x : Key → ℝ) : Integer.Sparse.eval row7788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7788, Integer.Sparse.eval_collectBalanced, rawRowCheck7788]

def rawRow7789 : Integer.Sparse Key := [(key3025, -2), (key3022, -2), (key3021, -2), (key2868, -2), (key2858, -2), (key2724, -2), (key2638, -2), (key2704, -2), (key2630, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key3025, 1), (key3022, 1), (key3016, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

theorem rawRowCheck7789 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form5 = rawRow7789 := by decide +kernel

def row7789 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

theorem rowCheck7789 : row7789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7789 := by decide +kernel

theorem rowEval7789 (x : Key → ℝ) : Integer.Sparse.eval row7789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7789, Integer.Sparse.eval_collectBalanced, rawRowCheck7789]

def rawRow7790 : Integer.Sparse Key := [(key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2)]

theorem rawRowCheck7790 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7790 := by decide +kernel

def row7790 : Integer.Sparse Key := [(key2455, 24), (key2516, -24)]

theorem rowCheck7790 : row7790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7790 := by decide +kernel

theorem rowEval7790 (x : Key → ℝ) : Integer.Sparse.eval row7790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7790, Integer.Sparse.eval_collectBalanced, rawRowCheck7790]

def rawRow7791 : Integer.Sparse Key := [(key2360, 2), (key2360, 2), (key2360, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2360, -2), (key2360, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2516, -2), (key2516, -2)]

theorem rawRowCheck7791 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0 = rawRow7791 := by decide +kernel

def row7791 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

theorem rowCheck7791 : row7791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7791 := by decide +kernel

theorem rowEval7791 (x : Key → ℝ) : Integer.Sparse.eval row7791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7791, Integer.Sparse.eval_collectBalanced, rawRowCheck7791]

def rawRow7792 : Integer.Sparse Key := [(key2455, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2360, 2), (key2455, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2455, -2), (key2455, -2), (key2516, -2), (key2360, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2516, -2), (key2360, -2), (key2455, -2), (key2455, -2)]

theorem rawRowCheck7792 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0 = rawRow7792 := by decide +kernel

def row7792 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

theorem rowCheck7792 : row7792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7792 := by decide +kernel

theorem rowEval7792 (x : Key → ℝ) : Integer.Sparse.eval row7792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7792, Integer.Sparse.eval_collectBalanced, rawRowCheck7792]

def rawRow7793 : Integer.Sparse Key := [(key2516, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2455, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2360, 2), (key2455, 2), (key2455, -2), (key2516, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2360, -2), (key2516, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2360, -2), (key2455, -2)]

theorem rawRowCheck7793 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0 = rawRow7793 := by decide +kernel

def row7793 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

theorem rowCheck7793 : row7793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7793 := by decide +kernel

theorem rowEval7793 (x : Key → ℝ) : Integer.Sparse.eval row7793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7793, Integer.Sparse.eval_collectBalanced, rawRowCheck7793]

def rawRow7794 : Integer.Sparse Key := [(key2516, 2), (key2516, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2455, 2), (key2516, 2), (key2360, 2), (key2455, 2), (key2360, 2), (key2516, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2455, -2), (key2516, -2), (key2360, -2), (key2455, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2360, -2)]

theorem rawRowCheck7794 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0 = rawRow7794 := by decide +kernel

def row7794 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

theorem rowCheck7794 : row7794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7794 := by decide +kernel

theorem rowEval7794 (x : Key → ℝ) : Integer.Sparse.eval row7794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form0) x := by
  rw [rowCheck7794, Integer.Sparse.eval_collectBalanced, rawRowCheck7794]

def rawRow7795 : Integer.Sparse Key := [(key968, -24), (key1082, 6), (key1082, 6), (key1082, 6), (key1082, 6)]

theorem rawRowCheck7795 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7795 := by decide +kernel

def row7795 : Integer.Sparse Key := [(key968, -24), (key1082, 24)]

theorem rowCheck7795 : row7795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7795 := by decide +kernel

theorem rowEval7795 (x : Key → ℝ) : Integer.Sparse.eval row7795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7795, Integer.Sparse.eval_collectBalanced, rawRowCheck7795]

def rawRow7796 : Integer.Sparse Key := [(key1082, -24), (key968, 6), (key1082, 6), (key1082, 6), (key1082, 6)]

theorem rawRowCheck7796 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1 = rawRow7796 := by decide +kernel

def row7796 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

theorem rowCheck7796 : row7796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7796 := by decide +kernel

theorem rowEval7796 (x : Key → ℝ) : Integer.Sparse.eval row7796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7796, Integer.Sparse.eval_collectBalanced, rawRowCheck7796]

def rawRow7797 : Integer.Sparse Key := [(key1082, -24), (key1082, 6), (key968, 6), (key1082, 6), (key1082, 6)]

theorem rawRowCheck7797 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1 = rawRow7797 := by decide +kernel

def row7797 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

theorem rowCheck7797 : row7797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7797 := by decide +kernel

theorem rowEval7797 (x : Key → ℝ) : Integer.Sparse.eval row7797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7797, Integer.Sparse.eval_collectBalanced, rawRowCheck7797]

def rawRow7798 : Integer.Sparse Key := [(key1082, -24), (key1082, 6), (key1082, 6), (key968, 6), (key1082, 6)]

theorem rawRowCheck7798 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1 = rawRow7798 := by decide +kernel

def row7798 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

theorem rowCheck7798 : row7798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7798 := by decide +kernel

theorem rowEval7798 (x : Key → ℝ) : Integer.Sparse.eval row7798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7798, Integer.Sparse.eval_collectBalanced, rawRowCheck7798]

def rawRow7799 : Integer.Sparse Key := [(key1082, -24), (key1082, 6), (key1082, 6), (key1082, 6), (key968, 6)]

theorem rawRowCheck7799 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1 = rawRow7799 := by decide +kernel

def row7799 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

theorem rowCheck7799 : row7799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7799 := by decide +kernel

theorem rowEval7799 (x : Key → ℝ) : Integer.Sparse.eval row7799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form1) x := by
  rw [rowCheck7799, Integer.Sparse.eval_collectBalanced, rawRowCheck7799]

def rawRow7800 : Integer.Sparse Key := [(key973, -6), (key973, -6), (key973, -6), (key973, -6), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2)]

theorem rawRowCheck7800 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7800 := by decide +kernel

def row7800 : Integer.Sparse Key := [(key973, -24), (key1087, 24)]

theorem rowCheck7800 : row7800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7800 := by decide +kernel

theorem rowEval7800 (x : Key → ℝ) : Integer.Sparse.eval row7800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7800, Integer.Sparse.eval_collectBalanced, rawRowCheck7800]

def rawRow7801 : Integer.Sparse Key := [(key1087, -6), (key1087, -6), (key1087, -6), (key1160, -6), (key973, 2), (key973, 2), (key973, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key1160, 2), (key1160, 2)]

theorem rawRowCheck7801 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form2 = rawRow7801 := by decide +kernel

def row7801 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

theorem rowCheck7801 : row7801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7801 := by decide +kernel

theorem rowEval7801 (x : Key → ℝ) : Integer.Sparse.eval row7801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7801, Integer.Sparse.eval_collectBalanced, rawRowCheck7801]

def rawRow7802 : Integer.Sparse Key := [(key1087, -6), (key1087, -6), (key1160, -6), (key1087, -6), (key1087, 2), (key1087, 2), (key1160, 2), (key973, 2), (key973, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key1160, 2), (key973, 2), (key1087, 2), (key1087, 2)]

theorem rawRowCheck7802 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form2 = rawRow7802 := by decide +kernel

def row7802 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

theorem rowCheck7802 : row7802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7802 := by decide +kernel

theorem rowEval7802 (x : Key → ℝ) : Integer.Sparse.eval row7802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7802, Integer.Sparse.eval_collectBalanced, rawRowCheck7802]

def rawRow7803 : Integer.Sparse Key := [(key1087, -6), (key1160, -6), (key1087, -6), (key1087, -6), (key1087, 2), (key1160, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key973, 2), (key1160, 2), (key973, 2), (key1087, 2), (key1087, 2), (key973, 2), (key1087, 2)]

theorem rawRowCheck7803 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form2 = rawRow7803 := by decide +kernel

def row7803 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

theorem rowCheck7803 : row7803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7803 := by decide +kernel

theorem rowEval7803 (x : Key → ℝ) : Integer.Sparse.eval row7803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck7803, Integer.Sparse.eval_collectBalanced, rawRowCheck7803]

def rawRow7804 : Integer.Sparse Key := [(key1160, -6), (key1087, -6), (key1087, -6), (key1087, -6), (key1160, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key1087, 2), (key1160, 2), (key973, 2), (key1087, 2), (key973, 2), (key1087, 2), (key1087, 2), (key973, 2)]

theorem rawRowCheck7804 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form2 = rawRow7804 := by decide +kernel

def row7804 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

theorem rowCheck7804 : row7804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7804 := by decide +kernel

theorem rowEval7804 (x : Key → ℝ) : Integer.Sparse.eval row7804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block3.form2) x := by
  rw [rowCheck7804, Integer.Sparse.eval_collectBalanced, rawRowCheck7804]

def rawRow7805 : Integer.Sparse Key := [(key2396, -6), (key2396, -6), (key2396, -6), (key2396, -6), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2)]

theorem rawRowCheck7805 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7805 := by decide +kernel

def row7805 : Integer.Sparse Key := [(key2396, -24), (key2462, 24)]

theorem rowCheck7805 : row7805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7805 := by decide +kernel

theorem rowEval7805 (x : Key → ℝ) : Integer.Sparse.eval row7805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7805, Integer.Sparse.eval_collectBalanced, rawRowCheck7805]

def rawRow7806 : Integer.Sparse Key := [(key2581, -6), (key2837, -6), (key2837, -6), (key2837, -6), (key2368, 2), (key2368, 2), (key2368, 2), (key2396, 2), (key2396, 2), (key2396, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2)]

theorem rawRowCheck7806 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form3 = rawRow7806 := by decide +kernel

def row7806 : Integer.Sparse Key := [(key2368, 6), (key2396, 6), (key2462, 12), (key2581, -6), (key2837, -18)]

theorem rowCheck7806 : row7806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7806 := by decide +kernel

theorem rowEval7806 (x : Key → ℝ) : Integer.Sparse.eval row7806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7806, Integer.Sparse.eval_collectBalanced, rawRowCheck7806]

def rawRow7807 : Integer.Sparse Key := [(key2837, -6), (key2581, -6), (key2837, -6), (key2837, -6), (key2760, 2), (key2837, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2837, 2), (key2368, 2), (key2368, 2), (key2396, 2), (key2396, 2), (key2462, 2), (key2462, 2)]

theorem rawRowCheck7807 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form3 = rawRow7807 := by decide +kernel

def row7807 : Integer.Sparse Key := [(key2368, 4), (key2396, 4), (key2462, 4), (key2581, -4), (key2760, 2), (key2837, -10)]

theorem rowCheck7807 : row7807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7807 := by decide +kernel

theorem rowEval7807 (x : Key → ℝ) : Integer.Sparse.eval row7807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck7807, Integer.Sparse.eval_collectBalanced, rawRowCheck7807]

end MUB6.Certificate.GramRows

end OAI

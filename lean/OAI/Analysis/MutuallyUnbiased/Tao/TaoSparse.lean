import Mathlib.Algebra.BigOperators.Ring.List
import OAI.Analysis.MutuallyUnbiased.Tao.TaoArithmetic
import OAI.Analysis.MutuallyUnbiased.Moments.DifferentMatrices

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

def encode (a : Charge) : List ℤ := List.ofFn a

def decode (l : List ℤ) : Charge := fun i => l[i.val]?.getD 0

@[simp] theorem decode_encode (a : Charge) : decode (encode a) = a := by
  funext i
  fin_cases i <;> simp [decode, encode]

abbrev Sparse := Certificate.Integer.Sparse (List ℤ)

def momentValues (f : Charge → ℂ) (key : List ℤ) : ℝ :=
  if key.headD 0 = 0 then (f (decode key.tail)).re
  else (omega * f (decode key.tail)).re

def monomial (a : Charge) (z : Coeff) : Sparse :=
  [(0 :: encode a, z.1), (1 :: encode a, z.2)]

theorem eval_monomial (f : Charge → ℂ) (a : Charge) (z : Coeff) :
    Certificate.Integer.Sparse.eval (monomial a z) (momentValues f) =
      (value z * f a).re := by
  simp [Certificate.Integer.Sparse.eval, monomial, momentValues, value,
    add_mul, Complex.add_re, Complex.mul_re]
  ring

def offDiagonalPairs : List (Coord × Coord) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),
   (1,0),(1,2),(1,3),(1,4),(1,5),
   (2,0),(2,1),(2,3),(2,4),(2,5),
   (3,0),(3,1),(3,2),(3,4),(3,5),
   (4,0),(4,1),(4,2),(4,3),(4,5),
   (5,0),(5,1),(5,2),(5,3),(5,4)]

theorem offDiagonalPairs_sum (f : Coord → Coord → ℂ) :
    (offDiagonalPairs.map (fun p => f p.1 p.2)).sum = offDiagSum f := by
  simp [offDiagonalPairs, offDiagSum, Finset.sum_erase_eq_sub, Fin.sum_univ_succ]
  ring

def row (a c : Charge) (w : Coeff) : Sparse :=
  offDiagonalPairs.flatMap (fun p => monomial (a + difference p.1 p.2)
    (mul w (conjugate (counts (c + difference p.1 p.2)))))

theorem eval_flatMap {ι : Type*} (l : List ι) (r : ι → Sparse) (x : List ℤ → ℝ) :
    Certificate.Integer.Sparse.eval (l.flatMap r) x =
      (l.map (fun i => Certificate.Integer.Sparse.eval (r i) x)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [List.flatMap_cons, ih]

theorem re_list_sum (l : List ℂ) : l.sum.re = (l.map Complex.re).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Complex.add_re, ih]

theorem eval_row (f : Charge → ℂ) (a c : Charge) (w : Coeff) :
    Certificate.Integer.Sparse.eval (row a c w) (momentValues f) =
      6 * (value w * offDiagSum
        (fun i j => f (a + difference i j) * conj (g tao (c + difference i j)))).re := by
  rw [row, eval_flatMap]
  simp_rw [eval_monomial, value_mul, value_conjugate, counts_interpretation,
    map_mul, map_ofNat]
  have hs : (offDiagonalPairs.map (fun p =>
      ((value w * (6 * conj (g tao (c + difference p.1 p.2)))) *
        f (a + difference p.1 p.2)).re)).sum =
      (6 * value w * (offDiagonalPairs.map (fun p =>
        f (a + difference p.1 p.2) * conj (g tao (c + difference p.1 p.2)))).sum).re := by
    rw [← List.sum_map_mul_left, re_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    ring
  rw [hs, offDiagonalPairs_sum (fun i j =>
    f (a + difference i j) * conj (g tao (c + difference i j)))]
  simp only [mul_assoc, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]

theorem eval_row_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        conj (g tao (c + difference i j))) = 0)
    (a c : Charge) (ha : Balanced a) (hc : Balanced c) (w : Coeff) :
    Certificate.Integer.Sparse.eval (row a c w) (momentValues f) = 0 := by
  rw [eval_row, hcross a c ha hc]
  simp

def normalize : Sparse → Sparse
  | [] => []
  | p :: ps => if p.2 = 0 then normalize ps
      else Certificate.Integer.Sparse.merge [p] (normalize ps)

theorem eval_normalize (r : Sparse) (x : List ℤ → ℝ) :
    Certificate.Integer.Sparse.eval (normalize r) x =
      Certificate.Integer.Sparse.eval r x := by
  induction r with
  | nil => rfl
  | cons p ps ih =>
    simp only [normalize]
    split_ifs with h
    · simp [ih, h]
    · simp [ih]

end MUB6.TaoArithmetic

end

end OAI

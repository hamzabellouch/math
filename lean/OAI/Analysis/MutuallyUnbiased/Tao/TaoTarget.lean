import Mathlib.Data.List.Basic
import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

def OrderTwoValues (f : Charge → ℂ) : Prop :=
  ∀ a, Balanced a → order a = 2 → f a = -(g tao a) / 5

theorem eval_known_monomial (f : Charge → ℂ) (hf : OrderTwoValues f)
    (a : Charge) (z : Coeff) (n : ℤ)
    (ha : Balanced a) (ho : order a = 2) (hn : mul z (counts a) = (n, 0)) :
    Certificate.Integer.Sparse.eval (monomial a z) (momentValues f) = -(n : ℝ) / 30 := by
  rw [eval_monomial]
  have h := congrArg value hn
  rw [value_mul, counts_interpretation] at h
  have hvn : value (n, 0) = (n : ℂ) := by simp [value]
  rw [hvn] at h
  have he : value z * f a = -(n : ℂ) / 30 := by
    rw [hf a ha ho]
    linear_combination -h / 30
  rw [he]
  simp

def knownTerms (ps : List (Charge × Coeff)) : Sparse :=
  ps.flatMap (fun p => monomial p.1 p.2)

theorem eval_knownTerms (f : Charge → ℂ) (hf : OrderTwoValues f)
    (ps : List (Charge × Coeff)) (n : ℤ)
    (hp : ps.Forall (fun p => Balanced p.1 ∧ order p.1 = 2 ∧
      mul p.2 (counts p.1) = (n, 0))) :
    Certificate.Integer.Sparse.eval (knownTerms ps) (momentValues f) =
      -(n : ℝ) / 30 * ps.length := by
  induction ps with
  | nil => simp [knownTerms]
  | cons p ps ih =>
    rw [List.forall_cons] at hp
    obtain ⟨⟨ha, ho, hn⟩, ht⟩ := hp
    rw [knownTerms, List.flatMap_cons, Certificate.Integer.Sparse.eval_append,
      eval_known_monomial f hf p.1 p.2 n ha ho hn]
    rw [show ps.flatMap (fun p => monomial p.1 p.2) = knownTerms ps from rfl, ih ht]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

def cubeTerms : Sparse :=
  offDiagonalPairs.flatMap (fun p => monomial ((3 : ℤ) • difference p.1 p.2) (36, 0))

theorem eval_cubeTerms (f : Charge → ℂ) :
    Certificate.Integer.Sparse.eval cubeTerms (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) := by
  rw [cubeTerms, eval_flatMap]
  simp_rw [eval_monomial]
  simp only [value, Int.cast_zero, zero_mul, add_zero, Int.cast_ofNat]
  have hs := congrArg Complex.re
    (offDiagonalPairs_sum (fun i j => (36 : ℂ) * f ((3 : ℤ) • difference i j)))
  simp only [re_list_sum, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, offDiagSum, Complex.re_sum, List.map_map, Function.comp_def] at hs
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  rw [hs]
  simp only [offDiagSum, Finset.mul_sum]

end MUB6.TaoArithmetic

end

end OAI

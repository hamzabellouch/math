import OAI.NumberTheory.TwoPoint.Bounds.FourFormLocal
import Mathlib.Analysis.PSeries

namespace OAI

/-! Local-density products for the rough sieve. The only prime information
needed is a lower bound for the ordinary reciprocal sum. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma reciprocal_square_sum_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 1 := by
  have hsub : P ⊆ Ioo 1 (P.sup id + 1) := by
    intro p hp
    exact mem_Ioo.mpr ⟨by have := hP p hp; omega,
      Nat.lt_succ_of_le (le_sup (f := id) hp)⟩
  calc
    _ ≤ ∑ p ∈ Ioo 1 (P.sup id + 1), ((p : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 := by
      have hh := sum_Ioo_inv_sq_le (α := ℝ) 1 (P.sup id + 1)
      norm_num at hh
      exact hh

lemma one_sub_product_le_exp {ι : Type*} [Fintype ι] (ν : ι → ℝ)
    (hν : ∀ i, ν i ≤ 1) :
    (∏ i, (1 - ν i)) ≤ Real.exp (-(∑ i, ν i)) := by
  calc
    _ ≤ ∏ i, Real.exp (-ν i) := by
      apply prod_le_prod₀
      · intro i _
        exact sub_nonneg.mpr (hν i)
      · intro i _
        have hh := Real.add_one_le_exp (-ν i)
        linarith
    _ = Real.exp (∑ i, -ν i) := (Real.exp_sum univ _).symm
    _ = _ := by rw [sum_neg_distrib]

/-- Four-form local avoidance loses precisely four reciprocal prime sums,
up to an absolute constant from the convergent square sum. -/
theorem fourForm_product_bound (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (hP : ∀ p ∈ P, 2 ≤ p) :
    (∏ p : P, (1 - fourFormBadDensity (p : ℕ))) ≤
      Real.exp 6 * Real.exp (-4 * ∑ p ∈ P, 1 / (p : ℝ)) := by
  have hν (p : P) : fourFormBadDensity (p : ℕ) ≤ 1 :=
    (uniformResidueCubeLaw (p : ℕ)).probability_le_one fourFormBad
  have hlower : 4 * (∑ p ∈ P, 1 / (p : ℝ)) - 6 ≤
      ∑ p : P, fourFormBadDensity (p : ℕ) := by
    have hs := sum_le_sum (fun (p : P) (_ : p ∈ (univ : Finset P)) =>
      (fourFormBadDensity_bounds (p : ℕ)).1)
    have he₁ : (∑ p : P, 4 / (p : ℝ)) = 4 * ∑ p ∈ P, 1 / (p : ℝ) := by
      rw [← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
        (fun p => 4 / (p : ℝ))]
      simp only [div_eq_mul_inv, one_mul, ← mul_sum]
    have he₂ : (∑ p : P, 6 / (p : ℝ) ^ 2) = 6 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
      rw [← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
        (fun p => 6 / (p : ℝ) ^ 2)]
      simp only [div_eq_mul_inv, one_mul, ← mul_sum]
    rw [sum_sub_distrib, he₁, he₂] at hs
    have hsq := reciprocal_square_sum_le_one P hP
    linarith
  calc
    _ ≤ Real.exp (-(∑ p : P, fourFormBadDensity (p : ℕ))) :=
      one_sub_product_le_exp _ hν
    _ ≤ Real.exp (6 - 4 * ∑ p ∈ P, 1 / (p : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; congr 2; ring

theorem oneForm_product_bound (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ Real.exp (-(∑ p ∈ P, 1 / (p : ℝ))) := by
  have hp (p : P) : 1 / (p : ℝ) ≤ 1 := by
    have hpr : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hP p p.property
    exact (div_le_one (by linarith : (0 : ℝ) < (p : ℕ))).mpr (by linarith)
  have hh := one_sub_product_le_exp (fun p : P => 1 / (p : ℝ)) hp
  rw [← prod_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => 1 - 1 / (p : ℝ)),
    ← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => 1 / (p : ℝ))] at hh
  exact hh

/-- The lower half of the classical reciprocal-prime estimate gives the
one-form power saving, with its constant displayed. -/
theorem oneForm_product_scale (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (L C : ℝ) (hL : 0 < L)
    (hprime : (99 / 100 : ℝ) * Real.log L - C ≤ ∑ p ∈ P, 1 / (p : ℝ)) :
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ Real.exp C * L ^ (-99 / 100 : ℝ) := by
  apply (oneForm_product_bound P hP).trans
  calc
    _ ≤ Real.exp (C - (99 / 100 : ℝ) * Real.log L) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.rpow_def_of_pos hL, ← Real.exp_add]; congr 1; ring

/-- The same classical lower bound gives the full fourth-moment exponent. -/
theorem fourForm_product_scale (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (hP : ∀ p ∈ P, 2 ≤ p) (L C : ℝ) (hL : 0 < L)
    (hprime : (99 / 100 : ℝ) * Real.log L - C ≤ ∑ p ∈ P, 1 / (p : ℝ)) :
    (∏ p : P, (1 - fourFormBadDensity (p : ℕ))) ≤
      Real.exp (4 * C + 6) * L ^ (-99 / 25 : ℝ) := by
  apply (fourForm_product_bound P hP).trans
  calc
    _ ≤ Real.exp 6 * Real.exp (4 * C - (99 / 25 : ℝ) * Real.log L) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
    _ = _ := by
      rw [Real.rpow_def_of_pos hL, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end TwoPointCorrelations

end OAI

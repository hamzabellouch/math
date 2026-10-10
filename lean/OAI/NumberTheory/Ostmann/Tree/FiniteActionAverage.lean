import Mathlib.GroupTheory.GroupAction.Basic
import OAI.NumberTheory.Ostmann.Preliminaries.TestFunctions

namespace OAI

/-!
# Averaging over the finite cycle action

These are the finite-sum projection identities used in the tree cycle
reduction. The action will be reciprocal multiplication on cycle leaves.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private def actionPermutation {G Ω : Type*} [Group G] [MulAction G Ω] (g : G) : Ω ≃ Ω where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := inv_smul_smul g x
  right_inv x := smul_inv_smul g x

noncomputable def finiteActionAverage {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω]
    (f : Ω → ℂ) (x : Ω) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (g • x)

theorem finiteActionAverage_invariant {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω]
    (f : Ω → ℂ) (g : G) (x : Ω) :
    finiteActionAverage (G := G) f (g • x) = finiteActionAverage (G := G) f x := by
  unfold finiteActionAverage
  simp only [← mul_smul]
  congr 1
  exact (Equiv.mulRight g).bijective.sum_comp (fun h : G => f (h • x))

theorem finiteActionAverage_of_invariant {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω]
    (f : Ω → ℂ) (hf : ∀ (g : G) x, f (g • x) = f x) (x : Ω) :
    finiteActionAverage (G := G) f x = f x := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteActionAverage, hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem finiteActionAverage_idempotent {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω]
    (f : Ω → ℂ) (x : Ω) :
    finiteActionAverage (G := G) (finiteActionAverage (G := G) f) x = finiteActionAverage (G := G) f x :=
  finiteActionAverage_of_invariant (G := G) _ (finiteActionAverage_invariant (G := G) f) x

/-- Averaging does not change correlation against an action-invariant test. -/
theorem finiteActionAverage_correlation {G Ω : Type*} [Group G] [Fintype G]
    [Fintype Ω] [MulAction G Ω] (f h : Ω → ℂ)
    (hh : ∀ (g : G) x, h (g • x) = h x) :
    (∑ x : Ω, finiteActionAverage (G := G) f x * conj (h x)) =
      ∑ x : Ω, f x * conj (h x) := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs (g : G) : (∑ x : Ω, f (g • x) * conj (h x)) =
      ∑ x : Ω, f x * conj (h x) := by
    calc
      _ = ∑ x : Ω, f (g • x) * conj (h (g • x)) := by simp only [hh]
      _ = _ := (actionPermutation g).bijective.sum_comp (fun x => f x * conj (h x))
  simp only [finiteActionAverage, Finset.sum_mul, mul_assoc]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Jensen's inequality for the finite average, written as a counting sum. -/
theorem finiteActionAverage_norm_sq_le {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω]
    (f : Ω → ℂ) (x : Ω) :
    ‖finiteActionAverage (G := G) f x‖ ^ 2 ≤
      (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f (g • x)‖ ^ 2 := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcs := complex_weighted_sum_sq (Finset.univ : Finset G)
    (fun _ => 1) (fun g => f (g • x))
  simp only [Complex.ofReal_one, one_mul, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  unfold finiteActionAverage
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  calc
    _ ≤ ((Fintype.card G : ℝ)⁻¹) ^ 2 *
        ((Fintype.card G : ℝ) * ∑ g : G, ‖f (g • x)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by field_simp

/-- The cycle average is an `L²` contraction. -/
theorem finiteActionAverage_energy_le {G Ω : Type*} [Group G] [Fintype G]
    [Fintype Ω] [MulAction G Ω] (f : Ω → ℂ) :
    (∑ x : Ω, ‖finiteActionAverage (G := G) f x‖ ^ 2) ≤ ∑ x : Ω, ‖f x‖ ^ 2 := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs (g : G) : (∑ x : Ω, ‖f (g • x)‖ ^ 2) = ∑ x : Ω, ‖f x‖ ^ 2 :=
    (actionPermutation g).bijective.sum_comp (fun x => ‖f x‖ ^ 2)
  calc
    _ ≤ ∑ x : Ω, (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f (g • x)‖ ^ 2 :=
      Finset.sum_le_sum fun x _ => finiteActionAverage_norm_sq_le (G := G) f x
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

end Ostmann

end OAI

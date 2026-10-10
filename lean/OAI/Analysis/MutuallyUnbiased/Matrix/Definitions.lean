import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Analysis.MutuallyUnbiased.Model

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def Balanced (a : Charge) : Prop := ∑ i, a i = 0

def order (a : Charge) : ℕ := ∑ i, (a i).toNat

@[simp] theorem character_zero (x : Coord → ℂ) : character x 0 = 1 := by
  simp [character]

@[simp] theorem g_zero (H : CMatrix) : g H 0 = 1 := by
  norm_num [g]

theorem alpha_balanced : Balanced alpha := by
  norm_num [Balanced, alpha, Fin.sum_univ_succ]

theorem alpha_order : order alpha = 3 := by
  decide +kernel

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem unit_norm {z : ℂ} (hz : Complex.normSq z = 1) : ‖z‖ = 1 := by
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

theorem character_norm (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : ‖character x a‖ = 1 := by
  simp [character, unit_norm (hx _)]

theorem g_norm_le_one {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    ‖g H a‖ ≤ 1 := by
  have hb : ‖∑ k, character (fun i => H i k) a‖ ≤ (6 : ℝ) := by
    calc
      _ ≤ ∑ k, ‖character (fun i => H i k) a‖ := norm_sum_le _ _
      _ = 6 := by simp [character_norm _ (fun i => hH.1 i _) a]
  have hi : ‖(6 : ℂ)⁻¹‖ = (6 : ℝ)⁻¹ := by
    have h := map_inv₀ Complex.isAbsoluteValueNorm.abvHom (6 : ℂ)
    change ‖(6 : ℂ)⁻¹‖ = ‖(6 : ℂ)‖⁻¹ at h
    simpa only [Complex.norm_ofNat] using h
  simpa [g, Complex.norm_mul, hi] using
    mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 6⁻¹)

theorem equivalent_refl (H : CMatrix) : Equivalent H H := by
  refine ⟨Equiv.refl _, Equiv.refl _, fun _ => 1, fun _ => 1, ?_, ?_, ?_⟩ <;> simp

end MUB6

end

end OAI

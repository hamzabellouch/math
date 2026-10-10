import Mathlib.Analysis.InnerProductSpace.PiL2
import OAI.NumberTheory.Ostmann.Characters.SparseKernelEnergy
import OAI.NumberTheory.Ostmann.Supply.CenteredSupportProjection

namespace OAI

/-! # Counting L2 norms for the finite local kernel blocks -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators ComplexConjugate

noncomputable def residueVectorNorm {p : ℕ} [NeZero p] (f : ZMod p → ℂ) : ℝ :=
  ‖(toLp 2 f : EuclideanSpace ℂ (ZMod p))‖

theorem residueVectorNorm_nonneg {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    0 ≤ residueVectorNorm f := norm_nonneg _

theorem residueVectorNorm_sq {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    residueVectorNorm f ^ 2 = ∑ x, ‖f x‖ ^ 2 := EuclideanSpace.norm_sq_eq _

theorem residueVectorNorm_add_le {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) :
    residueVectorNorm (fun x => f x + g x) ≤ residueVectorNorm f + residueVectorNorm g := by
  change ‖(toLp 2 f : EuclideanSpace ℂ (ZMod p)) + toLp 2 g‖ ≤ _
  exact norm_add_le _ _

theorem residueVectorNorm_smul {p : ℕ} [NeZero p] (a : ℂ) (f : ZMod p → ℂ) :
    residueVectorNorm (fun x => a * f x) = ‖a‖ * residueVectorNorm f := by
  change ‖a • (toLp 2 f : EuclideanSpace ℂ (ZMod p))‖ = _
  exact norm_smul _ _

theorem residueVectorNorm_le_iff {p : ℕ} [NeZero p] (f : ZMod p → ℂ)
    (B : ℝ) (hB : 0 ≤ B) :
    residueVectorNorm f ≤ B ↔ (∑ x, ‖f x‖ ^ 2) ≤ B ^ 2 := by
  rw [← residueVectorNorm_sq]
  exact (sq_le_sq₀ (residueVectorNorm_nonneg f) hB).symm

theorem residueVectorNorm_inner_le {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) :
    ‖∑ x, conj (f x) * g x‖ ≤ residueVectorNorm f * residueVectorNorm g := by
  calc
    _ ≤ ∑ x, ‖conj (f x) * g x‖ := norm_sum_le _ _
    _ = ∑ x, ‖f x‖ * ‖g x‖ := by simp only [norm_mul, Complex.norm_conj]
    _ ≤ _ := by
      simpa only [residueVectorNorm, EuclideanSpace.norm_eq] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun x => ‖f x‖) (fun x => ‖g x‖)

theorem residueVectorNorm_raw_le {p : ℕ} [NeZero p]
    (k f : ZMod p → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hk : ∀ a, ‖(p : ℂ) * additiveFourier k a‖ ≤ B) :
    residueVectorNorm (rawAdditiveKernelAction k f) ≤ B * residueVectorNorm f := by
  apply (residueVectorNorm_le_iff _ _ (mul_nonneg hB (residueVectorNorm_nonneg _))).mpr
  rw [mul_pow, residueVectorNorm_sq]
  exact rawAdditiveKernelAction_energy_le k f B hk

theorem residueVectorNorm_centered_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (f : ZMod p → ℂ) :
    residueVectorNorm (centeredSupportProjection S f) ≤ residueVectorNorm f := by
  apply (residueVectorNorm_le_iff _ _ (residueVectorNorm_nonneg _)).mpr
  rw [residueVectorNorm_sq]
  exact centeredSupportProjection_energy_le S f

end Ostmann

end OAI

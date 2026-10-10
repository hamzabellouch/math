import OAI.NumberTheory.CubicMoment.Estimates.RoughDivisorBounds
import OAI.NumberTheory.CubicMoment.Estimates.QuantitativeNoncube

namespace OAI

/-! The energy of the actual stopped inner coefficient follows from
rough distinguished divisors and the lattice count, without any
mean-square hypothesis on the collected coefficient. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_stopped_beta_energy (R D S : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (w : ℝ) (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    (selected : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ)
    {M Z : ℝ} (hM : 0 ≤ M) (hZ : 0 ≤ Z)
    (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (k : ℕ) (hsize : Z < w^k)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ Z) :
    (∑ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖^2) ≤
      18*Z*((2^k:ℕ)*M)^2 := by
  have hc := primary_support_card_le S hZ (fun b hb => ⟨(hS b hb).1,(hS b hb).2.2⟩)
  calc
    _ ≤ ∑ _b ∈ S, ((2^k:ℕ)*M)^2 := by
      apply Finset.sum_le_sum
      intro b hb
      apply pow_le_pow_left₀ (_root_.norm_nonneg _)
      exact stoppedBeta_rough_bound R D hR hψ w hw hrough selected v hM hv
        (hS b hb).1 (hS b hb).2.1 ((hS b hb).2.2.trans_lt hsize)
    _ = (S.card:ℝ)*((2^k:ℕ)*M)^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)

end CubicFirstMoment

end

end OAI

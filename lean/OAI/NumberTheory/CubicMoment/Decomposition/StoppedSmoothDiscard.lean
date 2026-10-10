import OAI.NumberTheory.CubicMoment.Estimates.SmoothRankinSaving
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedUniform

namespace OAI

/-! Smooth-number removal for the literal stopped coefficient family.
The uniform coefficient bound is already proved from its distinguished
rough-prime construction. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_smooth_discard (hpnt : PrimaryPrimePNT)
    {ξ C κ A : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hC : 0 < C) (hκ : 0 < κ)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∀ᶠ X : ℝ in atTop, ∀ (B : ℝ)
      (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
      (R D U : Finset Eisenstein) (selected : Eisenstein → Eisenstein → Prop),
      X^κ ≤ B → B ≤ C*X →
      (∀ i, ∀ p ∈ S i, primaryPrime p) →
      (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) → (∀ r ∈ R, primary r) →
      (∀ b ∈ U, primary b ∧ Squarefree b) → (∀ b ∈ U, norm b ≤ B) →
      (∀ b ∈ U, ∀ p ∈ primaryPrimeFactors b,
        norm p ≤ Real.exp (Real.sqrt (Real.log X))) →
      (∑ b ∈ U, ‖stoppedBeta R D
        (distinguishedTupleCoefficient S W ψ (X^ξ) (X^(2/5:ℝ)))
        ψ (X^ξ) selected b‖) ≤ B*(Real.log X)^(-A) := by
  obtain ⟨K,hK,hcoef⟩ := stoppedBeta_distinguished_uniform (ι := ι) hξ hξz hC
    hψ hψone hψzero
  have hlogK : ∀ᶠ X : ℝ in atTop, K ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop K)
  filter_upwards [hcoef,smooth_squarefree_discard (D := A+1) hpnt hκ,
    hlogK,eventually_gt_atTop (1:ℝ)] with X hcoef hcount hlogK hX
  intro B S W R D U selected hXB hBX hS hW hR hU hsize hsmooth
  have hB : 0 < B := (Real.rpow_pos_of_pos (zero_lt_one.trans hX) κ).trans_le hXB
  have hlog : 0 < Real.log X := Real.log_pos hX
  calc
    _ ≤ ∑ _b ∈ U, K := by
      apply Finset.sum_le_sum
      intro b hb
      exact hcoef S W R D selected hS hW hR b (hU b hb).1 (hU b hb).2
        ((hsize b hb).trans hBX)
    _ = K*(U.card:ℝ) := by simp [mul_comm]
    _ ≤ K*(B*(Real.log X)^(-(A+1))) :=
      mul_le_mul_of_nonneg_left (hcount B U hXB hU hsize hsmooth) hK.le
    _ ≤ (Real.log X)*(B*(Real.log X)^(-(A+1))) :=
      mul_le_mul_of_nonneg_right hlogK (by positivity)
    _ = B*(Real.log X)^(-A) := by
      have hp : Real.log X*(Real.log X)^(-(A+1)) = (Real.log X)^(-A) := by
        calc
          _ = (Real.log X)^1*(Real.log X)^(-(A+1)) := by rw [Real.rpow_one]
          _ = (Real.log X)^(1+(-(A+1))) := (Real.rpow_add hlog _ _).symm
          _ = _ := by congr 1; ring
      rw [mul_left_comm,hp]

end CubicFirstMoment

end

end OAI

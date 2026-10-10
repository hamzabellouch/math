import OAI.Analysis.LipschitzHilbert.Phase.PhaseMotion
import OAI.Analysis.LipschitzHilbert.Phase.DominantNormalization

namespace OAI

/-!
# Removing a distinguished diagonal carrier

The path-child carrier is a coordinatewise unitary. Removing it leaves the
path vector fixed and subtracts its frequency from every off-path component.
This is the exact transition to the small-drop model in §9.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

/-- Frequencies after the distinguished child's diagonal carrier is removed. -/
def diagonalRemainderFrequency (frequency : ι → κ → ℝ) (i₀ : ι)
    (i : RemainderIndex i₀) (j : κ) : ℝ := frequency i j - frequency i₀ j

omit [Fintype κ] in
theorem diagonal_carrier_identity (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (i₀ : ι) (t : ℝ) :
    diagonalFourierSum frequency a t = diagonalModulation (frequency i₀)
      (a i₀ + diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
        (fun i : RemainderIndex i₀ => a i) t) t := by
  classical
  apply PiLp.ext
  intro j
  change finiteFourierSum (fun i => frequency i j) (fun i => a i j) t =
    (a i₀ j + finiteFourierSum (fun i : RemainderIndex i₀ => frequency i j - frequency i₀ j)
      (fun i : RemainderIndex i₀ => a i j) t) * character (frequency i₀ j) t
  rw [finiteFourierSum, Fintype.sum_eq_add_sum_subtype_ne _ i₀,
    add_mul, finiteFourierSum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, character_mul]
  congr 2
  ring

theorem diagonal_carrier_norm (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (i₀ : ι) (t : ℝ) :
    ‖diagonalFourierSum frequency a t‖ =
      ‖a i₀ + diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
        (fun i : RemainderIndex i₀ => a i) t‖ := by
  rw [diagonal_carrier_identity frequency a i₀ t, norm_diagonalModulation]

theorem diagonal_carrier_energyRatio (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (i₀ : ι) (p denominator t : ℝ) :
    energyRatio p denominator (diagonalFourierSum frequency a t) =
      energyRatio p denominator
        (a i₀ + diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
          (fun i : RemainderIndex i₀ => a i) t) := by
  unfold energyRatio
  rw [diagonal_carrier_norm]

omit [Fintype ι] [Fintype κ] in
theorem diagonalRemainderFrequency_separated (frequency : ι → κ → ℝ)
    {gap : ℝ} (hsep : ∀ j, Separated (fun i => frequency i j) gap) (i₀ : ι) :
    ∀ j, Separated (fun i => diagonalRemainderFrequency frequency i₀ i j) gap := by
  intro j
  exact remainderFrequency_separated (hsep j) i₀

omit [Fintype ι] [Fintype κ] in
theorem diagonalRemainderFrequency_bound (frequency : ι → κ → ℝ)
    {L : ℝ} (hfrequency : ∀ i j, |frequency i j| ≤ L) (i₀ : ι) :
    ∀ i j, |diagonalRemainderFrequency frequency i₀ i j| ≤ 2 * L := by
  intro i j
  have h := norm_sub_le (frequency i j) (frequency i₀ j)
  simp only [Real.norm_eq_abs] at h
  exact h.trans (by linarith [hfrequency i j, hfrequency i₀ j])

theorem off_path_coefficient_sum (a : ι → EuclideanSpace ℂ κ) (i₀ : ι) :
    (∑ i : RemainderIndex i₀, ‖a i‖) = (∑ i, ‖a i‖) - ‖a i₀‖ := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  ring

/-- A bounded off-path coefficient mass gives the relative prediction deficit
for the original phase sum, after its carrier is removed exactly. -/
theorem diagonal_prediction_deficit (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (i₀ : ι) {p denominator B : ℝ}
    (hp : 1 ≤ p) (hd : 0 < denominator) (hB : 0 ≤ B)
    (hmass : (∑ i : RemainderIndex i₀, ‖a i‖) ≤ B)
    (hexceeds : ∃ t, 1 < energyRatio p denominator (diagonalFourierSum frequency a t)) (t : ℝ) :
    max (1 - energyRatio p denominator (diagonalFourierSum frequency a t)) 0 ≤ 2 * p * B := by
  simp_rw [diagonal_carrier_energyRatio frequency a i₀] at hexceeds ⊢
  apply fixed_path_prediction_deficit hp hd hB (a i₀)
    (fun t => diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
      (fun i : RemainderIndex i₀ => a i) t)
    (fun t => (diagonalFourierSum_bound _ _ t).trans hmass) hexceeds

end LipschitzHilbert

end

end OAI

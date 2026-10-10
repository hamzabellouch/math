import OAI.Combinatorics.Progressions.Estimates.AllocatedCorrelatedModeratePlateau
import OAI.Combinatorics.Progressions.Sampling.ForecastModerateWeightedSite

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)
variable (a : (∀ b, IntegerScalarCubeBox Empty (c b).length) → ℂ) (offset : B → ℤ)

theorem correlatedModerateFourierCoefficient_shift
    (rows : Finset (Finset I)) (shift : rows → ℤ) (k : rows → Fin M) :
    correlatedModerateFourierCoefficient c s a offset M rows shift k =
      correlatedModerateFourierCoefficient c s a offset M rows 0 k *
        rectangularGridCharacter M k shift := by
  have he (x : ∀ b, IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) :
      weightedModerateIntegerJetSum c s rows offset shift x =
        weightedModerateIntegerJetSum c s rows offset 0 x + shift := by
    simp [weightedModerateIntegerJetSum, add_comm]
  unfold correlatedModerateFourierCoefficient
  simp_rw [he, rectangularGridCharacter_add, ← mul_assoc]
  unfold FiniteProbabilityWeights.complexMean
  simp only [mul_assoc, Finset.sum_mul]

theorem correlatedModerateFourierCoefficient_norm_le
    (ha : ∀ z, ‖a z‖ ≤ 1) (rows : Finset (Finset I))
    (shift : rows → ℤ) (k : rows → Fin M) :
    ‖correlatedModerateFourierCoefficient c s a offset M rows shift k‖ ≤ 1 :=
  forecastWeightedGridCoefficient_norm_le (weightedModerateIntegerProductSource c s)
    (weightedModerateIntegerJetSum c s rows offset shift)
    (fun x => a (fun b => (x b).1)) (fun _ => ha _) M k

theorem correlatedModerateFourierCoefficient_retained_mass
    (ha : ∀ z, ‖a z‖ ≤ 1) (rows : Finset (Finset I))
    (shift : rows → ℤ) (F : Finset (rows → Fin M)) :
    (∑ k : F, ‖correlatedModerateFourierCoefficient c s a offset M rows shift k.val‖) ≤
      F.card :=
  forecastWeightedGridCoefficient_retained_mass (weightedModerateIntegerProductSource c s)
    (weightedModerateIntegerJetSum c s rows offset shift)
    (fun x => a (fun b => (x b).1)) (fun _ => ha _) M F

theorem correlatedModeratePlateauApproximation_eq_weightedFourierSum
    (H : ℝ) (rows : Finset (Finset I)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) :
    correlatedModeratePlateauApproximation c s a offset K H rows shift z F =
      forecastModerateWeightedFourierSum (K := K) rows F H
        (fun k => correlatedModerateFourierCoefficient c s a offset M rows 0 k.val) shift z := by
  unfold correlatedModeratePlateauApproximation correlatedModerateGridApproximation
    forecastModerateWeightedFourierSum
  simp only [correlatedModerateFourierCoefficient_shift c s a offset rows shift,
    mul_assoc]
  congr 2
  exact (Finset.sum_coe_sort F (fun k =>
    correlatedModerateFourierCoefficient c s a offset M rows 0 k *
      (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)))).symm

theorem correlatedModeratePlateauApproximation_family {Cell : Type*}
    (aCell : Cell → (∀ b, IntegerScalarCubeBox Empty (c b).length) → ℂ)
    (ha : ∀ cell z, ‖aCell cell z‖ ≤ 1)
    (H : ℝ) (rows : Finset (Finset I)) (shift : rows → ℤ)
    (F : Finset (rows → Fin M)) :
    let β := fun cell (k : F) =>
      correlatedModerateFourierCoefficient c s (aCell cell) offset M rows 0 k.val
    (∀ cell, (∑ k, ‖β cell k‖) ≤ (F.card : ℝ)) ∧
      ∀ cell z, correlatedModeratePlateauApproximation c s (aCell cell) offset K H
        rows shift z F = forecastModerateWeightedFourierSum (K := K) rows F H (β cell) shift z := by
  dsimp only
  exact ⟨fun cell => correlatedModerateFourierCoefficient_retained_mass c s (aCell cell)
      offset (ha cell) rows 0 F,
    fun cell z => correlatedModeratePlateauApproximation_eq_weightedFourierSum c s
      (aCell cell) offset H rows shift z F⟩

end Erdos3

end

end OAI

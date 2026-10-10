import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPackedMoment
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityWeightedFourth
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityWeightedMollifier

namespace OAI

/-! # The actual moments at characterwise separated zero ordinates -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem density_packed_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, Integrable (fun v => densityCubicWeight (v - t i) *
        ‖(c i).L (densityVerticalPoint (1 / 2) v)‖ ^ 4)) ∧
      (∑ i ∈ S, ∫ v, densityCubicWeight (v - t i) *
        ‖(c i).L (densityVerticalPoint (1 / 2) v)‖ ^ 4) ≤
          C * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := density_weighted_fourth_moment
  refine ⟨densityKernelPackingConstant * C, mul_pos densityKernelPackingConstant_pos hC, ?_⟩
  intro Q hQ T hT ι S c t hc ht hs
  have hF : ∀ χ ∈ S.image c, χ.modulus ≤ Q := by
    intro χ hχ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hχ
    exact hc i hi
  obtain ⟨hi, hm⟩ := hb Q hQ T hT (S.image c) hF
  obtain ⟨hpi, hpm⟩ := density_packed_moment S c t T (by linarith) ht hs
    (fun χ v => ‖χ.L (densityVerticalPoint (1 / 2) v)‖ ^ 4)
    (fun χ => by simpa using density_L_fourth_family_continuous {χ})
    (fun _ _ => by positivity) hi
  refine ⟨hpi, hpm.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hm densityKernelPackingConstant_pos.le
  convert h using 1; ring

 theorem density_packed_mollifier_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, Integrable (fun v => densityCubicWeight (v - t i) *
        ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖ ^ 2)) ∧
      (∑ i ∈ S, ∫ v, densityCubicWeight (v - t i) *
        ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖ ^ 2) ≤
          C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X) := by
  obtain ⟨C, hC, hb⟩ := density_weighted_mollifier_mean
  refine ⟨densityKernelPackingConstant * C, mul_pos densityKernelPackingConstant_pos hC, ?_⟩
  intro X Q hX hQ T hT ι S c t hc ht hs
  have hF : ∀ χ ∈ S.image c, χ.modulus ≤ Q := by
    intro χ hχ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hχ
    exact hc i hi
  obtain ⟨hi, hm⟩ := hb X Q hX hQ T hT (S.image c) hF
  obtain ⟨hpi, hpm⟩ := density_packed_moment S c t T (by linarith) ht hs
    (fun χ v => ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) v)‖ ^ 2)
    (fun χ => by simpa using density_mollifier_family_continuous {χ} X)
    (fun _ _ => by positivity) hi
  refine ⟨hpi, hpm.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hm densityKernelPackingConstant_pos.le
  convert h using 1; ring

end Ostmann

end OAI

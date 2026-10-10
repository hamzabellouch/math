import OAI.MeasureTheory.Falconer.Fourier.InverseJetSupport
import OAI.MeasureTheory.Falconer.Estimates.RotatedInverse

namespace OAI

/-! # Isometry transport keeps the original individual mask jets -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace MaskJetIndex
variable {d : ℕ}

noncomputable def mapIsometry (j : MaskJetIndex d) (T : Space d ≃ₗᵢ[ℝ] Space d) : MaskJetIndex d where
  order := j.order
  vectors := fun i => T (j.vectors i)
  norm_vectors := fun i => by rw [T.norm_map]; exact j.norm_vectors i

theorem value_comp_isometry (j : MaskJetIndex d) (T : Space d ≃ₗᵢ[ℝ] Space d)
    {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B) (z : Space d) :
    j.value (B ∘ T) z = (j.mapIsometry T).value B (T z) := by
  unfold value
  change (iteratedFDeriv ℝ j.order
    (B ∘ (T.toContinuousLinearEquiv.toContinuousLinearMap : Space d → Space d)) z) j.vectors = _
  rw [T.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hB z (by simp)]
  rfl

theorem normalizedValue_comp_isometry (j : MaskJetIndex d) (T : Space d ≃ₗᵢ[ℝ] Space d)
    (r : ℝ) {B : Space d → ℝ} (hB : ContDiff ℝ ∞ B) (z : Space d) :
    j.normalizedValue r (B ∘ T) z = (j.mapIsometry T).normalizedValue r B (T z) := by
  unfold normalizedValue
  change ((r^j.order*(iteratedFDeriv ℝ j.order
    (B ∘ (T.toContinuousLinearEquiv.toContinuousLinearMap : Space d → Space d)) z) j.vectors:ℝ):ℂ) = _
  rw [T.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hB z (by simp)]
  rfl

end MaskJetIndex

namespace MaskJetExpansion
variable {ι : Type} {X : Type*} [Fintype ι] [DecidableEq ι]

theorem rotatedInverseAmplitude_product_radius_jets (m j : ℕ)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3))
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℝ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let S := (product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j
    rotatedInverseAmplitude m T (fun z => ∏ i, (B i x z:ℂ)) j e =
      ∑ a : S.index, (S.term a).radiusCoefficient r (T e) *
        ∏ i, (((S.term a).jet i).mapIsometry T.symm).normalizedValue (r i) (B i x) e := by
  intro S
  have hh := localInverseAmplitude_product_radius_jets_global m j r hr
    (fun i x => B i x ∘ T.symm) (fun i x => (hB i x).comp T.symm.contDiff) x (sphereMap T e)
  change localInverseAmplitude m (fun z => ∏ i, (B i x (T.symm z):ℂ)) j (T e) = _ at hh
  change localInverseAmplitude m (fun z => ∏ i, (B i x (T.symm z):ℂ)) j (T e) = _
  rw [hh]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [MaskJetIndex.normalizedValue_comp_isometry _ _ _ (hB i x)]
  simp only [sphereMap,T.symm_apply_apply]
  rfl

end MaskJetExpansion
end Falconer

end OAI

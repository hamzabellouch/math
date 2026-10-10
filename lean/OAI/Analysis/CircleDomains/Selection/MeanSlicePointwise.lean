import OAI.Analysis.CircleDomains.Sobolev.PlanarSliceIntegrals
import OAI.Analysis.CircleDomains.Sobolev.CompactIntegralComparison

namespace OAI

/-! Compact transverse tests turn the integrated coarea estimate into
an almost-everywhere bound on each physical horizontal slice. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
 theorem meanSliceCount_restrict (π : ℂ → X) (K : Set C(PathTime, X))
    (η : Measure K) (I J B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ y, ∫⁻ γ : K, pathImageCount
      (π '' (planarSliceBox I (J ∩ B) ∩ Complex.im ⁻¹' {y})) γ.val ∂η) =
      ∫⁻ y in B, ∫⁻ γ : K, pathImageCount
        (π '' (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ.val ∂η := by
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ B
  · simp only [indicator_of_mem hy]
    apply lintegral_congr
    intro γ
    rw [pathImageCount_planarSliceBox_restrict, indicator_of_mem hy]
  · simp only [indicator_of_notMem hy]
    have he : (fun γ : K => pathImageCount
        (π '' (planarSliceBox I (J ∩ B) ∩ Complex.im ⁻¹' {y})) γ.val) = 0 := by
      funext γ
      rw [pathImageCount_planarSliceBox_restrict, indicator_of_notMem hy]
      rfl
    rw [he]
    change (∫⁻ _ : K, (0 : ℝ≥0∞) ∂η) = 0
    exact lintegral_zero

 theorem ae_meanSliceCount_le
    (π : ℂ → X) (hπ : Continuous π) (K : Set C(PathTime, X))
    (hK : ∀ γ ∈ K, Injective γ) (η : Measure K) [SFinite η]
    {I J : Set ℝ} (hI : IsCompact I) (hJ : IsCompact J)
    (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ)
    (hfin : (∫⁻ z in planarSliceBox I J, ρ z) < ∞)
    (hcoarea : ∀ B : Set ℝ, IsCompact B → B ⊆ J →
      (∫⁻ y, ∫⁻ γ : K, pathImageCount
        (π '' (planarSliceBox I B ∩ Complex.im ⁻¹' {y})) γ.val ∂η) ≤
          ∫⁻ z in planarSliceBox I B, ρ z) :
    ∀ᵐ y ∂volume, (∫⁻ γ : K, pathImageCount
      (π '' (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ.val ∂η) ≤
        ∫⁻ x in I, ρ ⟨x, y⟩ := by
  have hN := (measurable_compactPhysicalFiberCount π hπ (isCompact_planarSliceBox hI hJ)
    Complex.im Complex.continuous_im K hK).comp measurable_swap
  apply ae_le_of_compact_setLIntegral_le hN.lintegral_prod_right'
    ((hcoarea J hJ Subset.rfl).trans_lt hfin)
  intro B hB
  change (∫⁻ y in B, ∫⁻ γ : K, pathImageCount
    (π '' (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ.val ∂η) ≤ _
  rw [← meanSliceCount_restrict π K η I J B hB.measurableSet]
  apply (hcoarea (J ∩ B) (hJ.inter hB) inter_subset_left).trans
  rw [lintegral_planarSliceBox hI.measurableSet (hJ.inter hB).measurableSet ρ hρ]
  exact lintegral_mono_set inter_subset_right

end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Selection.MeanGeometricIndex

namespace OAI

/-! The expected distinct intersection count controls increments of the
actual averaged index. Infinite counts are allowed. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

 theorem meanGeometricIndex_difference_le_intersections (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K)
    (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hinj : Injective (diskRayProjection ∘ δ)) :
    ENNReal.ofReal |meanGeometricIndex hsch K hKS η ⟨δ 1, hδ 1⟩ -
      meanGeometricIndex hsch K hKS η ⟨δ 0, hδ 0⟩| ≤
      ∫⁻ γ : K, pathImageCount (diskRayProjection '' range δ) γ.val ∂(η : Measure K) := by
  have h0 := integrable_geometricRayIndex hsch hsep K hK hKS η ⟨δ 0, hδ 0⟩
  have h1 := integrable_geometricRayIndex hsch hsep K hK hKS η ⟨δ 1, hδ 1⟩
  unfold meanGeometricIndex
  rw [← integral_sub h1 h0]
  calc
    _ ≤ ∫⁻ γ : K, ‖(geometricRayIndex hsch γ.val (hKS γ.property) (δ 1) : ℝ) -
        (geometricRayIndex hsch γ.val (hKS γ.property) (δ 0) : ℝ)‖ₑ ∂(η : Measure K) := by
      simpa only [Real.enorm_eq_ofReal_abs] using enorm_integral_le_lintegral_enorm
        (μ := (η : Measure K)) (fun γ : K =>
          (geometricRayIndex hsch γ.val (hKS γ.property) (δ 1) : ℝ) -
            (geometricRayIndex hsch γ.val (hKS γ.property) (δ 0) : ℝ))
    _ ≤ _ := lintegral_mono (fun γ => by
      simpa only [Real.enorm_eq_ofReal_abs] using
        geometric_index_difference_le_intersections hsch hsep γ.val (hKS γ.property) δ hδ hinj)

end CircleDomainRigidity

end

end OAI

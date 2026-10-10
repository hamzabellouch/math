import OAI.Geometry.RCD.Coordinates.RegularDirichletCore
import OAI.Geometry.RCD.Sobolev.WeakLaplacianProduct

namespace OAI

/-! # Products remain in the dense regular compact test core -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem product_mem_compactLaplacianCore [IsFiniteMeasureOnCompacts μ]
    {Ω : Set X} {f g : SobolevSpace μ hQ}
    (hf : f ∈ compactLaplacianCore μ hQ Ω) (hg : g ∈ compactLaplacianCore μ hQ Ω)
    (A B : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ A)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ B) :
    SobolevSpace.product μ hQ f g A B ∈ compactLaplacianCore μ hQ Ω := by
  obtain ⟨v,L,hv,hvc,hvs,hfr⟩ := hf.1
  obtain ⟨w,M,hw,hwc,hws,hgr⟩ := hg.1
  obtain ⟨E,hE⟩ := hvc.exists_bound_of_continuous hv.continuous
  have hE' (x : X) : |v x| ≤ (max E 0).toNNReal := by
    rw [Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hE x).trans (le_max_left _ _)
  obtain ⟨D,hD⟩ := lipschitz_mul_constant_outside_compact hv hw 0 (by simpa using hvc) hE'
  constructor
  · refine ⟨fun x => v x*w x,D,hD,hvc.mul_right,tsupport_mul_subset_left.trans hvs,?_⟩
    filter_upwards [SobolevSpace.product_coe μ hQ f g A B hA hB,hfr,hgr] with x hx hf hg
    exact hx.trans (congrArg₂ (fun a b : ℝ => a*b) hf hg)
  · obtain ⟨df,hdf⟩ := hf.2
    obtain ⟨dg,hdg⟩ := hg.2
    have hL : ∀ᵐ x ∂μ, localGamma μ hQ g g x ≤ (M:ℝ)^2 := by
      filter_upwards [localGamma_self μ hQ g,SobolevSpace.minimalSlope_le_lipschitz μ hQ g hw hgr,
        (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ g)] with x he hM h0
      rw [he]
      exact pow_le_pow_left₀ h0 hM 2
    obtain ⟨q,hq,-⟩ := hdf.product μ hQ f g df dg hdg A B M hA hB hL
    exact ⟨q,hq⟩

end RegularPointCoordinates

end

end OAI

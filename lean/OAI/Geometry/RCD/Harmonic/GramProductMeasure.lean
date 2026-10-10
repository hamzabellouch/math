import OAI.Geometry.RCD.Metric.LocalMeasureProduct
import OAI.Geometry.RCD.Sobolev.MeasureLaplacianAlgebra
import OAI.Geometry.RCD.Sobolev.FiniteEnergyRepresentatives

namespace OAI

/-! # The full measure equation for a product Gram entry -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The Gram entry of a product is represented by genuine Sobolev
products. Its local Laplacian keeps both weighted full measures and the
ordinary cross terms. -/
theorem gram_product_measure {Ω : Set X}
    (f g h Fg Fh : SobolevSpace μ hQ)
    (G H : X →ᵇ ℝ)
    (hG : SobolevSpace.toLp μ hQ g =ᵐ[μ] G)
    (hH : SobolevSpace.toLp μ hQ h =ᵐ[μ] H)
    (dg dh : Lp ℝ 2 μ) (hdg : IsWeakLaplacian μ hQ g dg)
    (hdh : IsWeakLaplacian μ hQ h dh)
    (νg νh : SignedMeasure X)
    (hνg : IsMeasureLaplacianOn μ hQ Ω Fg νg)
    (hνh : IsMeasureLaplacianOn μ hQ Ω Fh νh)
    (hFg : SobolevSpace.toLp μ hQ Fg =ᵐ[μ.restrict Ω] localGamma μ hQ f g)
    (hFh : SobolevSpace.toLp μ hQ Fh =ᵐ[μ.restrict Ω] localGamma μ hQ f h)
    (A B : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ Fg x|≤A)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ Fh x|≤B) :
    let P := SobolevSpace.product μ hQ Fh g B ‖G‖₊+
      SobolevSpace.product μ hQ Fg h A ‖H‖₊
    SobolevSpace.toLp μ hQ P =ᵐ[μ.restrict Ω]
      localGamma μ hQ f (SobolevSpace.product μ hQ g h ‖G‖₊ ‖H‖₊) ∧
    IsMeasureLaplacianOn μ hQ Ω P
      (cutoffMeasureSource μ hQ Fh g dg νh G+cutoffMeasureSource μ hQ Fg h dh νg H) := by
  have hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤(‖G‖₊:ℝ) := by
    filter_upwards [hG] with x hx
    simpa only [hx,Real.norm_eq_abs,coe_nnnorm] using G.norm_coe_le_norm x
  have hh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ h x|≤(‖H‖₊:ℝ) := by
    filter_upwards [hH] with x hx
    simpa only [hx,Real.norm_eq_abs,coe_nnnorm] using H.norm_coe_le_norm x
  constructor
  · change (SobolevSpace.toLpCLM μ hQ (_+_)) =ᵐ[μ.restrict Ω] _
    rw [map_add]
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add
      (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ Fh g B ‖G‖₊))
      (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ Fg h A ‖H‖₊))),
      ae_restrict_of_ae (SobolevSpace.product_coe μ hQ Fh g B ‖G‖₊ hB hg),
      ae_restrict_of_ae (SobolevSpace.product_coe μ hQ Fg h A ‖H‖₊ hA hh),
      ae_restrict_of_ae (localGamma_product_right μ hQ f g h ‖G‖₊ ‖H‖₊ hg hh),
      hFg,hFh] with x hadd hprod₁ hprod₂ hΓ hfg hfh
    change ((SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ Fh g B ‖G‖₊)+
      SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ Fg h A ‖H‖₊)) : Lp ℝ 2 μ) x = _
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hprod₁,hprod₂,hΓ,hfg,hfh]
    ring
  · exact (hνh.mul μ hQ G g hG dg hdg B hB).add μ hQ (hνg.mul μ hQ H h hH dh hdh A hA)

end RegularPointCoordinates

end

end OAI

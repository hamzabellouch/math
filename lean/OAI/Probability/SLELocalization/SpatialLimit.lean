import Mathlib
import OAI.Probability.SLELocalization.SlabMoments

namespace OAI


/-! Conformal localization and Spatial Limit estimates. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.SpatialLimit

lemma canonical_fiber_limit {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {ν : Measure Z} [SFinite P] [SFinite ν]
    (X : ℕ → Ω × Z → ℝ) (hX : ∀ n, AEMeasurable (X n) (P.prod ν))
    (Y : Ω × Z → ℝ)
    (hlim : ∀ᵐ z ∂ν, ∀ᵐ ω ∂P, Tendsto (fun n => X n (ω,z)) atTop (𝓝 (Y (ω,z)))) :
    ∃ G : Ω × Z → ℝ, Measurable G ∧
      (∀ᵐ q ∂P.prod ν, Tendsto (fun n => X n q) atTop (𝓝 (G q))) ∧
      (∀ᵐ z ∂ν, ∀ᵐ ω ∂P, Y (ω,z) = G (ω,z)) := by
  let F : ℕ → Ω × Z → ℝ := fun n => (hX n).mk (X n)
  have hF (n : ℕ) : Measurable (F n) := (hX n).measurable_mk
  let G : Ω × Z → ℝ := fun q => limUnder atTop (fun n => F n q)
  have hG : Measurable G := (StronglyMeasurable.limUnder (fun n => (hF n).stronglyMeasurable)).measurable
  have he : ∀ᵐ q ∂P.prod ν, ∀ n, X n q = F n q :=
    ae_all_iff.2 (fun n => (hX n).ae_eq_mk)
  have hes := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae he)
  have hGe : ∀ᵐ z ∂ν, ∀ᵐ ω ∂P, Y (ω,z) = G (ω,z) := by
    filter_upwards [hlim,hes] with z hz hez
    filter_upwards [hz,hez] with ω hω heω
    change ∀ n, X n (ω,z) = F n (ω,z) at heω
    have hf : Tendsto (fun n => F n (ω,z)) atTop (𝓝 (Y (ω,z))) := by
      simpa only [heω] using hω
    exact hf.limUnder_eq.symm
  refine ⟨G,hG,?_,hGe⟩
  apply ae_prod_tendsto_of_fibers hX hG.aemeasurable
  filter_upwards [hlim,hGe] with z hz hgz
  filter_upwards [hz,hgz] with ω hω heω
  rwa [← heω]

end SLEExactGauge.SpatialLimit

end

end OAI

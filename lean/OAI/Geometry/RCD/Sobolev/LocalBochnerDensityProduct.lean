import OAI.Geometry.RCD.Metric.SignedRadonLocal
import OAI.Geometry.RCD.Sobolev.BochnerMeasureProductLocal

namespace OAI

/-! # The pointwise density consequence of the full Bochner product identity -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [SigmaFinite μ]

/-- Taking the density of the full local identity retains its exact
Hessian term. Singular mass remains present in the original identity. -/
theorem signed_rnDeriv_local_product (Sg Sh Sz : SignedMeasure X)
    (G H : X →ᵇ ℝ) {h : X → ℝ} (hh : Integrable h μ)
    {S : Set X} (hS : MeasurableSet S)
    (he : Sz.restrict S=(signedSourceWeight Sh G+signedSourceWeight Sg H+
      (2 : ℝ) • μ.withDensityᵥ h).restrict S) :
    Sz.rnDeriv μ =ᵐ[μ.restrict S] fun x =>
      G x*Sh.rnDeriv μ x+H x*Sg.rnDeriv μ x+2*h x := by
  let A := signedSourceWeight Sh G
  let B := signedSourceWeight Sg H
  let D : SignedMeasure X := μ.withDensityᵥ h
  have hloc := signed_rnDeriv_eq_on_of_restrict_eq μ hS he
  have hAB := SignedMeasure.rnDeriv_add A B μ
  have hsum := SignedMeasure.rnDeriv_add (A+B) ((2 : ℝ) • D) μ
  have htwo := SignedMeasure.rnDeriv_smul D μ 2
  filter_upwards [hloc,ae_restrict_of_ae hAB,ae_restrict_of_ae hsum,ae_restrict_of_ae htwo,
    ae_restrict_of_ae (signed_rnDeriv_sourceWeight μ Sh G),
    ae_restrict_of_ae (signed_rnDeriv_sourceWeight μ Sg H),
    ae_restrict_of_ae (signed_rnDeriv_density μ hh)] with x hl hab hs ht ha hb hd
  change Sz.rnDeriv μ x=SignedMeasure.rnDeriv (A+B+(2 : ℝ) • D) μ x at hl
  rw [hl,hs]
  simp only [Pi.add_apply]
  rw [hab,ht]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [ha,hb,hd]

end RegularPointCoordinates

end

end OAI

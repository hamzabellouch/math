import OAI.Probability.InvariantIsing.Pressure.RandomOrbitLaw

namespace OAI

/-! Integration against the joint conditional orbit law does not require a
(global) integrability hypothesis for the random pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace InvariantIsing

lemma ConditionalFieldOrbitLaw.lintegral {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P] {d : Ω → FieldSpectralData N} {Y : Ω → ℝ}
    {H : Measure (Orthogonal N)} [IsProbabilityMeasure H]
    (h : ConditionalFieldOrbitLaw P d Y H) (hN : 0 < N)
    (hd : Measurable d) (hY : Measurable Y)
    (φ : FieldSpectralData N × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ ω, φ (d ω,Y ω) ∂P)=
      ∫⁻ ω, ∫⁻ U, φ (d ω,dataPhysicalPressure (d ω) U) ∂H ∂P := by
  have hm : Measurable (fun z : FieldSpectralData N × Orthogonal N =>
      (z.1,dataPhysicalPressure z.1 z.2)) := measurable_fst.prodMk (measurable_dataPhysicalPressure hN)
  have hF : Measurable (fun z : FieldSpectralData N × Orthogonal N =>
      φ (z.1,dataPhysicalPressure z.1 z.2)) := hφ.comp hm
  rw [← lintegral_map hφ (hd.prodMk hY),h,lintegral_map hφ hm,
    lintegral_prod _ hF.aemeasurable]
  exact lintegral_map hF.lintegral_prod_right' hd

end InvariantIsing

end

end OAI

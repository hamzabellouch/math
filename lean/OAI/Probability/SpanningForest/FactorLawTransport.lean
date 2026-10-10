import OAI.Probability.SpanningForest.FactorAssembly
import OAI.Probability.SpanningForest.FUSFLawUnique

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336.FactorAssembly

theorem measurable_rule_section {Phi : FactorRule} (hPhi : RuleBorel Phi)
    (G : GraphCode) : Measurable (Phi G) := by
  apply measurable_pi_iff.mpr
  intro e
  exact hPhi.comp (measurable_const.prodMk
    (measurable_id.prodMk measurable_const))

theorem measurable_rule_output {Ω : Type*} [MeasurableSpace Ω]
    {Phi : FactorRule} (hPhi : RuleBorel Phi) (G : GraphCode)
    (U : ℕ → Ω → ℝ) (hU : ∀ v, Measurable (U v)) :
    Measurable (fun ω e => Phi G (fun v => U v ω) e) := by
  apply measurable_pi_iff.mpr
  intro e
  exact hPhi.comp (measurable_const.prodMk
    ((Measurable.of_eval hU).prodMk measurable_const))

theorem hasFUSFLaw_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {G : GraphCode} {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → EdgeConfiguration} {Y : Ω' → EdgeConfiguration}
    (hX : Measurable X) (hY : HasFUSFLaw G Q Y)
    (hLaw : P.map X = Q.map Y) : HasFUSFLaw G P X := by
  refine ⟨fun e => (measurable_pi_apply e).comp hX, ?_⟩
  intro H hH A B
  have hc : P (X ⁻¹' configurationCylinder A B) =
      Q (Y ⁻¹' configurationCylinder A B) := by
    rw [← Measure.map_apply hX (measurableSet_configurationCylinder A B),
      ← Measure.map_apply (Measurable.of_eval hY.1)
        (measurableSet_configurationCylinder A B), hLaw]
  change Filter.Tendsto (fun n => ustCylinder (H n) A B) Filter.atTop
    (nhds (P (X ⁻¹' configurationCylinder A B)))
  rw [hc]
  exact hY.2 H hH A B

theorem assembled_hasFUSFLaw_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {b : GraphDrift} {w : GraphNoise} (hb : DriftBorel b) (hw : NoiseBorel w)
    (G : GraphCode) (P : Measure Ω) (U : ℕ → Ω → ℝ)
    (hU : ∀ v, Measurable (U v)) {Q : Measure Ω'} {Y : Ω' → EdgeConfiguration}
    (hY : HasFUSFLaw G Q Y)
    (hLaw : P.map (fun ω e => rule b w G (fun v => U v ω) e) = Q.map Y) :
    HasFUSFLaw G P (fun ω e => rule b w G (fun v => U v ω) e) :=
  hasFUSFLaw_of_map_eq (measurable_rule_output (rule_borel hb hw) G U hU) hY hLaw

end Problem336.FactorAssembly

end

end OAI

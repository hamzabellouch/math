import OAI.Probability.StrongRayleigh.BrownianBridgeSignal

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139

theorem brownianBridgeFamily_indep_signal_observedEndpoints
    {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω] {P : Measure Ω}
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s)) {X : Ω → I → ℝ} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (p : I × Set.Iic t) =>
      B p.1 p.2 ω - ((p.2 : ℝ≥0) : ℝ) / (t : ℝ) * B p.1 t ω)
      (fun ω => (X ω, fun i => (t : ℝ) * X ω i + B i t ω)) P := by
  simpa only [Function.comp_def, id_eq] using
    (brownianBridgeFamily_indep_signal_endpoints hB hIndep mB mX hX t ht).comp
      measurable_id
      (show Measurable (fun v : (I → ℝ) × (I → ℝ) =>
        (v.1, fun i => (t : ℝ) * v.1 i + v.2 i)) by fun_prop)

theorem brownianBridgeFamily_indep_observedEndpoints_of_signalMap
    {Ω : Type u_3} {I : Type u_4} {α : Type u_5} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s)) {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (signal : α → I → ℝ) (mSignal : Measurable signal)
    (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (p : I × Set.Iic t) =>
      B p.1 p.2 ω - ((p.2 : ℝ≥0) : ℝ) / (t : ℝ) * B p.1 t ω)
      (fun ω => (X ω, fun i => (t : ℝ) * signal (X ω) i + B i t ω)) P := by
  simpa only [Function.comp_def, id_eq] using
    (brownianBridgeFamily_indep_signal_endpoints hB hIndep mB mX hX t ht).comp
      measurable_id
      (show Measurable (fun v : α × (I → ℝ) =>
        (v.1, fun i => (t : ℝ) * signal v.1 i + v.2 i)) by fun_prop)

end Problem336AdditiveD139

end

end OAI

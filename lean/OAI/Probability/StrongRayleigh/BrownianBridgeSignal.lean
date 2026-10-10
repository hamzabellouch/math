import OAI.Probability.StrongRayleigh.BrownianBridge

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139

theorem indepFun_pair_reassociate
    {Ω : Type u_1} {α : Type u_2} {β : Type u_3} {γ : Type u_4} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (mX : Measurable X) (mY : Measurable Y) (mZ : Measurable Z)
    (hXZ : IndepFun X Z P) (hY : IndepFun Y (fun ω => (X ω, Z ω)) P) :
    IndepFun X (fun ω => (Y ω, Z ω)) P := by
  have hYZ : IndepFun Y Z P := by
    simpa only [Function.comp_def, id_eq] using hY.comp measurable_id measurable_snd
  apply (indepFun_iff_map_prod_eq_prod_map_map mX.aemeasurable
    (mY.prodMk mZ).aemeasurable).2
  rw [hYZ.map_prod_eq_prod_map_map mY.aemeasurable mZ.aemeasurable]
  apply Measure.ext_prod₃
  intro s u v hs hu hv
  rw [Measure.map_apply (mX.prodMk (mY.prodMk mZ)) (hs.prod (hu.prod hv)),
    Measure.prod_prod, Measure.prod_prod,
    Measure.map_apply mX hs, Measure.map_apply mY hu, Measure.map_apply mZ hv]
  have hY' := (indepFun_iff_measure_inter_preimage_eq_mul.1 hY)
    u (s ×ˢ v) hu (hs.prod hv)
  have hXZ' := (indepFun_iff_measure_inter_preimage_eq_mul.1 hXZ) s v hs hv
  have hset : (fun ω => (X ω, Y ω, Z ω)) ⁻¹' (s ×ˢ u ×ˢ v) =
      Y ⁻¹' u ∩ (fun ω => (X ω, Z ω)) ⁻¹' (s ×ˢ v) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
    tauto
  rw [hset, hY']
  change P (Y ⁻¹' u) * P (X ⁻¹' s ∩ Z ⁻¹' v) = _
  rw [hXZ']
  ring

theorem brownianBridgeFamily_indep_signal_endpoints
    {Ω : Type u_5} {I : Type u_6} {α : Type u_7} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hIndep : iIndepFun (fun i ω s => B i s ω) P)
    (mB : ∀ i s, Measurable (B i s)) {X : Ω → α} (mX : Measurable X)
    (hX : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (p : I × Set.Iic t) =>
      B p.1 p.2 ω - ((p.2 : ℝ≥0) : ℝ) / (t : ℝ) * B p.1 t ω)
      (fun ω => (X ω, fun i => B i t ω)) P := by
  have := hIndep.isProbabilityMeasure
  apply indepFun_pair_reassociate (by fun_prop) mX (by fun_prop)
    (show IndepFun (fun ω (p : I × Set.Iic t) =>
        B p.1 p.2 ω - ((p.2 : ℝ≥0) : ℝ) / (t : ℝ) * B p.1 t ω)
        (fun ω i => B i t ω) P from
      by simpa only [BrownianBridge.bridge] using
        BrownianBridge.family_bridge_indep_endpoints B hB hIndep (pos_of_ne_zero ht))
  simpa only [Function.comp_def, id_eq] using hX.comp measurable_id
    (show Measurable (fun b : I × ℝ≥0 → ℝ =>
      ((fun p : I × Set.Iic t => b (p.1, p.2) -
        ((p.2 : ℝ≥0) : ℝ) / (t : ℝ) * b (p.1, t)), fun i => b (i, t))) by
      fun_prop)

end Problem336AdditiveD139

end

end OAI

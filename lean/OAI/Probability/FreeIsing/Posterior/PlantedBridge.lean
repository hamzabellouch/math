import OAI.Probability.FreeIsing.Brownian.Bridge

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma indepFun_prod_left_of_indepFun
    {S Omega E F : Type*} [MeasurableSpace S] [MeasurableSpace Omega]
    [MeasurableSpace E] [MeasurableSpace F]
    (nu : Measure S) (mu : Measure Omega)
    [IsProbabilityMeasure nu] [IsProbabilityMeasure mu]
    {f : Omega → E} {g : Omega → F} (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g mu) :
    IndepFun (fun q : S × Omega => (q.1, f q.2)) (fun q => g q.2) (nu.prod mu) := by
  have hfirst : (nu.prod mu).map (fun q : S × Omega => (q.1, f q.2)) =
      nu.prod (mu.map f) := by
    calc
      _ = (nu.prod mu).map (Prod.map id f) := by
        congr 1
      _ = _ := by
        simpa only [Measure.map_id] using (Measure.map_prod_map nu mu measurable_id hf).symm
  have hsecond : (nu.prod mu).map (fun q : S × Omega => g q.2) = mu.map g := by
    rw [← Function.comp_def, ← Measure.map_map hg measurable_snd]
    simp
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2
  rw [hfirst, hsecond]
  calc
    _ = ((nu.prod mu).map (Prod.map id (fun w => (f w, g w)))).map
        (MeasurableEquiv.prodAssoc.symm : S × (E × F) ≃ᵐ (S × E) × F) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (nu.prod (mu.map (fun w => (f w, g w)))).map
        (MeasurableEquiv.prodAssoc.symm : S × (E × F) ≃ᵐ (S × E) × F) := by
      rw [← Measure.map_prod_map nu mu measurable_id (hf.prodMk hg), Measure.map_id]
    _ = _ := by
      rw [hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable]
      exact (measurePreserving_prodAssoc nu (mu.map f) (mu.map g)).symm.map_eq

lemma planted_bridge_indep_signal_terminal
    {S Omega : Type*} [MeasurableSpace S] [MeasurableSpace Omega]
    (nu : Measure S) (mu : Measure Omega) [IsProbabilityMeasure nu]
    {B : ℝ≥0 → Omega → ℝ} (hB : IsPreBrownianReal B mu)
    (hmB : ∀ t, Measurable (B t)) {sigma : S → ℝ} (hsigma : Measurable sigma)
    {T : ℝ≥0} (hT : T ≠ 0) :
    IndepFun (fun q : S × Omega => (sigma q.1, (T : ℝ) * sigma q.1 + B T q.2))
      (fun q (s : Set.Iic T) => brownianBridge B T s q.2) (nu.prod mu) := by
  have : IsProbabilityMeasure mu := hB.isGaussianProcess.isProbabilityMeasure
  have hmbridge : Measurable (fun w (s : Set.Iic T) => brownianBridge B T s w) := by
    apply Measurable.of_eval
    intro s
    exact (hmB s).sub ((hmB T).const_mul _)
  have hi := indepFun_prod_left_of_indepFun nu mu (hmB T) hmbridge
    (preBrownian_bridge_indep_terminal hB hT).symm
  have hm : Measurable (fun q : S × ℝ => (sigma q.1, (T : ℝ) * sigma q.1 + q.2)) := by
    fun_prop
  simpa only [Function.comp_def, id_eq] using hi.comp hm measurable_id

end Problem367

end

end OAI

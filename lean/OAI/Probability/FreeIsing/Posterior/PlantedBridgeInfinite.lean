import OAI.Probability.FreeIsing.Posterior.PlantedBridgeVector

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma indepFun_comp_measurePreserving
    {Omega Omega' E F : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [MeasurableSpace E] [MeasurableSpace F]
    {mu : Measure Omega} {nu : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {r : Omega → Omega'} (hr : MeasurePreserving r mu nu)
    {f : Omega' → E} {g : Omega' → F}
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g nu) :
    IndepFun (f ∘ r) (g ∘ r) mu := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hf.comp hr.measurable).aemeasurable (hg.comp hr.measurable).aemeasurable).2
  have h := hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  rw [← hr.map_eq] at h
  simpa only [Measure.map_map (hf.prodMk hg) hr.measurable,
    Measure.map_map hf hr.measurable, Measure.map_map hg hr.measurable,
    Function.comp_def] using h

lemma indepFun_infinitePi_of_coordinate_indepFun
    {ι Omega E F : Type*} [MeasurableSpace Omega]
    [MeasurableSpace E] [MeasurableSpace F]
    (mu : ι → Measure Omega) [∀ i, IsProbabilityMeasure (mu i)]
    {f : ι → Omega → E} {g : ι → Omega → F}
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfg : ∀ i, IndepFun (f i) (g i) (mu i)) :
    IndepFun (fun w : ι → Omega => fun i => f i (w i))
      (fun w => fun i => g i (w i)) (Measure.infinitePi mu) := by
  classical
  apply IndepFun.process_indepFun_process
    (fun i => (hf i).comp (measurable_pi_apply i))
    (fun i => (hg i).comp (measurable_pi_apply i))
  intro I J
  let K := I ∪ J
  have hi := indepFun_pi_of_coordinate_indepFun (fun i : K => mu i)
    (fun i => hf i) (fun i => hg i) (fun i => hfg i)
  have hr : MeasurePreserving (K.restrict : (ι → Omega) → K → Omega)
      (Measure.infinitePi mu) (Measure.pi fun i : K => mu i) :=
    ⟨by fun_prop, Measure.infinitePi_map_restrict mu⟩
  have hp := indepFun_comp_measurePreserving hr
    (Measurable.of_eval (fun index : K => (hf index).comp (measurable_pi_apply index)))
    (Measurable.of_eval (fun index : K => (hg index).comp (measurable_pi_apply index))) hi
  let eI : I → K := fun i => ⟨i, Finset.mem_union_left J i.property⟩
  let eJ : J → K := fun j => ⟨j, Finset.mem_union_right I j.property⟩
  have h := hp.comp
    (by fun_prop : Measurable (fun x : K → E => fun i : I => x (eI i)))
    (by fun_prop : Measurable (fun x : K → F => fun j : J => x (eJ j)))
  simpa only [Function.comp_def, Finset.restrict, eI, eJ] using h

lemma planted_infinite_bridges_indep_signal_terminal
    {ι S Omega : Type*} [MeasurableSpace S] [MeasurableSpace Omega]
    (nu : Measure S) (mu : ι → Measure Omega) [IsProbabilityMeasure nu]
    {B : ι → ℝ≥0 → Omega → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (mu i))
    (hmB : ∀ i t, Measurable (B i t))
    {sigma : S → ι → ℝ} (hsigma : Measurable sigma)
    {T : ℝ≥0} (hT : T ≠ 0) :
    IndepFun
      (fun q : S × (ι → Omega) =>
        (q.1, fun i => (T : ℝ) * sigma q.1 i + B i T (q.2 i)))
      (fun q i (s : Set.Iic T) => brownianBridge (B i) T s (q.2 i))
      (nu.prod (Measure.infinitePi mu)) := by
  have (index : ι) : IsProbabilityMeasure (mu index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  have hmbridge (i : ι) :
      Measurable (fun w (s : Set.Iic T) => brownianBridge (B i) T s w) := by
    apply Measurable.of_eval
    intro s
    exact (hmB i s).sub ((hmB i T).const_mul _)
  have hi := indepFun_infinitePi_of_coordinate_indepFun mu (fun i => hmB i T) hmbridge
    (fun i => (preBrownian_bridge_indep_terminal (hB i) hT).symm)
  have hp := indepFun_prod_left_of_indepFun nu (Measure.infinitePi mu)
    (by fun_prop : Measurable (fun w : ι → Omega => fun i => B i T (w i)))
    (Measurable.of_eval (fun index => (hmbridge index).comp (measurable_pi_apply index))) hi
  have hm : Measurable (fun q : S × (ι → ℝ) =>
      (q.1, fun i => (T : ℝ) * sigma q.1 i + q.2 i)) := by fun_prop
  simpa only [Function.comp_def, id_eq] using hp.comp hm measurable_id

end Problem367

end

end OAI

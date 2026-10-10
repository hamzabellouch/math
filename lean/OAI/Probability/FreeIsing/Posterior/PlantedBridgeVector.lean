import OAI.Probability.FreeIsing.Posterior.PlantedBridge

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma indepFun_pi_of_coordinate_indepFun
    {ι Omega E F : Type*} [Fintype ι] [MeasurableSpace Omega]
    [MeasurableSpace E] [MeasurableSpace F]
    (mu : ι → Measure Omega) [∀ i, IsProbabilityMeasure (mu i)]
    {f : ι → Omega → E} {g : ι → Omega → F}
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfg : ∀ i, IndepFun (f i) (g i) (mu i)) :
    IndepFun (fun w : ι → Omega => fun i => f i (w i))
      (fun w => fun i => g i (w i)) (Measure.pi mu) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (Measurable.of_eval (fun index => (hf index).comp (measurable_pi_apply index))).aemeasurable
    (Measurable.of_eval (fun index => (hg index).comp (measurable_pi_apply index))).aemeasurable).2
  simp only [Function.comp_def]
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable),
    Measure.pi_map_pi (fun i => (hg i).aemeasurable)]
  calc
    _ = ((Measure.pi mu).map (fun w i => (f i (w i), g i (w i)))).map
        (MeasurableEquiv.arrowProdEquivProdArrow E F ι) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (Measure.pi (fun i => (mu i).map (fun w => (f i w, g i w)))).map
        (MeasurableEquiv.arrowProdEquivProdArrow E F ι) := by
      rw [Measure.pi_map_pi (fun i => ((hf i).prodMk (hg i)).aemeasurable)]
    _ = (Measure.pi (fun i => ((mu i).map (f i)).prod ((mu i).map (g i)))).map
        (MeasurableEquiv.arrowProdEquivProdArrow E F ι) := by
      congr 2
      funext i
      exact (hfg i).map_prod_eq_prod_map_map (hf i).aemeasurable (hg i).aemeasurable
    _ = _ := (measurePreserving_arrowProdEquivProdArrow E F ι
      (fun i => (mu i).map (f i)) (fun i => (mu i).map (g i))).map_eq

lemma planted_bridges_indep_signal_terminal
    {ι S Omega : Type*} [Fintype ι] [MeasurableSpace S] [MeasurableSpace Omega]
    (nu : Measure S) (mu : ι → Measure Omega) [IsProbabilityMeasure nu]
    {B : ι → ℝ≥0 → Omega → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (mu i))
    (hmB : ∀ i t, Measurable (B i t))
    {sigma : S → ι → ℝ} (hsigma : Measurable sigma)
    {T : ℝ≥0} (hT : T ≠ 0) :
    IndepFun
      (fun q : S × (ι → Omega) =>
        (q.1, fun i => (T : ℝ) * sigma q.1 i + B i T (q.2 i)))
      (fun q i (s : Set.Iic T) => brownianBridge (B i) T s (q.2 i))
      (nu.prod (Measure.pi mu)) := by
  have (index : ι) : IsProbabilityMeasure (mu index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  have hmbridge (i : ι) :
      Measurable (fun w (s : Set.Iic T) => brownianBridge (B i) T s w) := by
    apply Measurable.of_eval
    intro s
    exact (hmB i s).sub ((hmB i T).const_mul _)
  have hi := indepFun_pi_of_coordinate_indepFun mu (fun i => hmB i T) hmbridge
    (fun i => (preBrownian_bridge_indep_terminal (hB i) hT).symm)
  have hp := indepFun_prod_left_of_indepFun nu (Measure.pi mu)
    (by fun_prop : Measurable (fun w : ι → Omega => fun i => B i T (w i)))
    (Measurable.of_eval (fun index => (hmbridge index).comp (measurable_pi_apply index))) hi
  have hm : Measurable (fun q : S × (ι → ℝ) =>
      (q.1, fun i => (T : ℝ) * sigma q.1 i + q.2 i)) := by fun_prop
  simpa only [Function.comp_def, id_eq] using hp.comp hm measurable_id

lemma comap_vector_past_eq_endpoint_bridges
    {ι Omega : Type*} (B : ι → ℝ≥0 → Omega → ℝ) (T : ℝ≥0) :
    MeasurableSpace.comap (fun w i (s : Set.Iic T) => B i s w) inferInstance =
      MeasurableSpace.comap
        (fun w => (fun i => B i T w,
          fun i (s : Set.Iic T) => brownianBridge (B i) T s w)) inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace Omega := MeasurableSpace.comap
      (fun w => (fun i => B i T w,
        fun i (s : Set.Iic T) => brownianBridge (B i) T s w)) inferInstance
    apply Measurable.comap_le
    have hm : Measurable
        (fun w => (fun i => B i T w,
          fun i (s : Set.Iic T) => brownianBridge (B i) T s w)) := comap_measurable _
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    have hb := (measurable_pi_apply s).comp
      ((measurable_pi_apply i).comp (measurable_snd.comp hm))
    have ht := (measurable_pi_apply i).comp (measurable_fst.comp hm)
    convert hb.add (ht.const_mul ((s : ℝ≥0) / (T : ℝ))) using 1
    funext w
    simp [brownianBridge]
  · let : MeasurableSpace Omega :=
      MeasurableSpace.comap (fun w i (s : Set.Iic T) => B i s w) inferInstance
    apply Measurable.comap_le
    have hm : Measurable (fun w i (s : Set.Iic T) => B i s w) := comap_measurable _
    have ht (i : ι) : Measurable (B i T) :=
      (measurable_pi_apply (⟨T, by simp⟩ : Set.Iic T)).comp
        ((measurable_pi_apply i).comp hm)
    apply (Measurable.of_eval ht).prodMk
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    exact ((measurable_pi_apply s).comp ((measurable_pi_apply i).comp hm)).sub
      ((ht i).const_mul _)

lemma comap_planted_vector_past_eq_terminal_bridges
    {ι S Omega : Type*} (B : ι → ℝ≥0 → Omega → ℝ)
    (sigma : S → ι → ℝ) {T : ℝ≥0} (hT : T ≠ 0) :
    MeasurableSpace.comap
      (fun q : S × (ι → Omega) => fun i (s : Set.Iic T) =>
        (s : ℝ≥0) * sigma q.1 i + B i s (q.2 i)) inferInstance =
    MeasurableSpace.comap
      (fun q : S × (ι → Omega) =>
        (fun i => (T : ℝ) * sigma q.1 i + B i T (q.2 i),
          fun i (s : Set.Iic T) => brownianBridge (B i) T s (q.2 i))) inferInstance := by
  rw [comap_vector_past_eq_endpoint_bridges
    (fun i t (q : S × (ι → Omega)) => (t : ℝ) * sigma q.1 i + B i t (q.2 i)) T]
  congr 1
  funext q
  congr 1
  funext i s
  exact brownianBridge_add_drift
    (fun t (q : S × (ι → Omega)) => B i t (q.2 i))
    (fun q => sigma q.1 i) hT s q

end Problem367

end

end OAI

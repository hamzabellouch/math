import OAI.Probability.FreeIsing.Brownian.Bridge
import OAI.Probability.FreeIsing.Gaussian.IncrementLikelihood

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem367

theorem preBrownian_past_drift_withDensity
    {Omega : Type*} [MeasurableSpace Omega]
    {B : ℝ≥0 → Omega → ℝ} {mu : Measure Omega}
    (hB : IsPreBrownianReal B mu) (hmB : ∀ t, Measurable (B t))
    {T : ℝ≥0} (hT : T ≠ 0) (s : ℝ) :
    Measure.map (fun w (t : Set.Iic T) => (t.val : ℝ) * s + B t w) mu =
      (Measure.map (fun w (t : Set.Iic T) => B t w) mu).withDensity
        (fun y : Set.Iic T → ℝ => ENNReal.ofReal
          (gaussianSignalLikelihood T s (y ⟨T, by simp⟩))) := by
  let : IsProbabilityMeasure mu := hB.isGaussianProcess.isProbabilityMeasure
  let R : Omega → Set.Iic T → ℝ := fun w t => brownianBridge B T t w
  let E : Omega → (Set.Iic T → ℝ) × ℝ := fun w => (R w, B T w)
  let Es : Omega → (Set.Iic T → ℝ) × ℝ :=
    fun w => (R w, (T : ℝ) * s + B T w)
  let F : ((Set.Iic T → ℝ) × ℝ) → Set.Iic T → ℝ :=
    fun z t => z.1 t + ((t.val : ℝ) / (T : ℝ)) * z.2
  let L : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (gaussianSignalLikelihood T s x)
  have hR : Measurable R := by
    apply Measurable.of_eval
    intro t
    exact (hmB t).sub ((hmB T).const_mul _)
  have hE : Measurable E := hR.prodMk (hmB T)
  have hEs : Measurable Es := hR.prodMk (measurable_const.add (hmB T))
  have hF : Measurable F := by unfold F; fun_prop
  have hL : Measurable L := by unfold L gaussianSignalLikelihood; fun_prop
  have hind : IndepFun R (B T) mu := preBrownian_bridge_indep_terminal hB hT
  have hlaw : Measure.map E mu = (Measure.map R mu).prod (gaussianReal 0 T) := by
    rw [IndepFun.map_prod_eq_prod_map_map hR.aemeasurable (hmB T).aemeasurable hind,
      (hB.hasLaw_eval T).map_eq]
  have hlaws : Measure.map Es mu =
      (Measure.map R mu).prod (gaussianReal ((T : ℝ) * s) T) := by
    have hshift : Measurable (fun x : ℝ => (T : ℝ) * s + x) := by fun_prop
    have hbt : Measurable (fun w => (T : ℝ) * s + B T w) := by fun_prop
    have hinds : IndepFun R (fun w => (T : ℝ) * s + B T w) mu := by
      simpa only [Function.comp_def, id_eq] using
        hind.comp measurable_id hshift
    change Measure.map (fun w => (R w, (T : ℝ) * s + B T w)) mu = _
    rw [IndepFun.map_prod_eq_prod_map_map hR.aemeasurable
      hbt.aemeasurable hinds]
    congr 1
    simpa only [zero_add] using
      (gaussianReal_const_add (hB.hasLaw_eval T) ((T : ℝ) * s)).map_eq
  have hchange : Measure.map Es mu =
      (Measure.map E mu).withDensity (fun z => L z.2) := by
    rw [hlaws, hlaw, gaussianReal_signal_withDensity T s]
    exact prod_withDensity_right hL
  have hFE : F ∘ E = fun w (t : Set.Iic T) => B t w := by
    funext w t
    dsimp [F, E, R, brownianBridge]
    ring
  have hFEs : F ∘ Es = fun w (t : Set.Iic T) => (t.val : ℝ) * s + B t w := by
    have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    funext w t
    dsimp [F, Es, R, brownianBridge]
    field_simp
    ring
  have hpast : Measurable (fun w (t : Set.Iic T) => B t w) :=
    Measurable.of_eval (fun t => hmB t)
  calc
    Measure.map (fun w (t : Set.Iic T) => (t.val : ℝ) * s + B t w) mu =
        Measure.map F (Measure.map Es mu) := by rw [Measure.map_map hF hEs, hFEs]
    _ = Measure.map F ((Measure.map E mu).withDensity (fun z => L z.2)) := by
      rw [hchange]
    _ = Measure.map F (Measure.map E (mu.withDensity (fun w => L (B T w)))) := by
      congr 1
      exact (map_withDensity_comp_observation mu E hE (fun z => L z.2)
        (hL.comp measurable_snd)).symm
    _ = Measure.map (fun w (t : Set.Iic T) => B t w)
        (mu.withDensity (fun w => L (B T w))) := by rw [Measure.map_map hF hE, hFE]
    _ = _ := map_withDensity_comp_observation mu _ hpast
      (fun y : Set.Iic T → ℝ => L (y ⟨T, by simp⟩)) (hL.comp (measurable_pi_apply _))

theorem preBrownian_past_vector_drift_withDensity
    {Omega V : Type*} [MeasurableSpace Omega] [Fintype V]
    {B : ℝ≥0 → Omega → ℝ} {mu : Measure Omega}
    (hB : IsPreBrownianReal B mu) (hmB : ∀ t, Measurable (B t))
    {T : ℝ≥0} (hT : T ≠ 0) (s : V → ℝ) :
    Measure.pi (fun v : V =>
      Measure.map (fun w (t : Set.Iic T) => (t.val : ℝ) * s v + B t w) mu) =
      (Measure.pi (fun _ : V =>
        Measure.map (fun w (t : Set.Iic T) => B t w) mu)).withDensity
        (fun y => ENNReal.ofReal
          (gaussianVectorLikelihood T s (fun v => y v ⟨T, by simp⟩))) := by
  classical
  let : IsProbabilityMeasure mu := hB.isGaussianProcess.isProbabilityMeasure
  have hpast : Measurable (fun w (t : Set.Iic T) => B t w) :=
    Measurable.of_eval (fun t => hmB t)
  let : IsProbabilityMeasure
      (Measure.map (fun w (t : Set.Iic T) => B t w) mu) :=
    (Measure.isProbabilityMeasure_map_iff hpast.aemeasurable).mpr inferInstance
  have hshift (v : V) :
      Measurable (fun w (t : Set.Iic T) => (t.val : ℝ) * s v + B t w) := by
    apply Measurable.of_eval
    intro t
    exact measurable_const.add (hmB t)
  let (v : V) : IsProbabilityMeasure
      (Measure.map (fun w (t : Set.Iic T) => (t.val : ℝ) * s v + B t w) mu) :=
    (Measure.isProbabilityMeasure_map_iff (hshift v).aemeasurable).mpr inferInstance
  rw [pi_withDensity_of_probability
    (fun _ : V => Measure.map (fun w (t : Set.Iic T) => B t w) mu)
    (fun v : V => Measure.map (fun w (t : Set.Iic T) => (t.val : ℝ) * s v + B t w) mu)
    (fun v (y : Set.Iic T → ℝ) => ENNReal.ofReal
      (gaussianSignalLikelihood T (s v) (y ⟨T, by simp⟩)))
    (fun v => by unfold gaussianSignalLikelihood; fun_prop)
    (fun v => preBrownian_past_drift_withDensity hB hmB hT (s v))]
  apply withDensity_congr_ae
  filter_upwards [] with y
  rw [← ENNReal.ofReal_prod_of_nonneg (fun v hv => by
    unfold gaussianSignalLikelihood; positivity), prod_gaussianSignalLikelihood]

theorem preBrownian_past_spin_drift_withDensity
    {Omega V : Type*} [MeasurableSpace Omega] [Fintype V]
    {B : ℝ≥0 → Omega → ℝ} {mu : Measure Omega}
    (hB : IsPreBrownianReal B mu) (hmB : ∀ t, Measurable (B t))
    {T : ℝ≥0} (hT : T ≠ 0) (s : V → ℝ) (hs : ∀ v, s v ^ 2 = 1) :
    Measure.pi (fun v : V =>
      Measure.map (fun w (t : Set.Iic T) => (t.val : ℝ) * s v + B t w) mu) =
      (Measure.pi (fun _ : V =>
        Measure.map (fun w (t : Set.Iic T) => B t w) mu)).withDensity
        (fun y => ENNReal.ofReal
          (Real.exp ((∑ v, s v * y v ⟨T, by simp⟩) -
            (T : ℝ) * Fintype.card V / 2))) := by
  simpa only [gaussianVectorLikelihood_of_sq_eq_one _ _ _ hs] using
    preBrownian_past_vector_drift_withDensity hB hmB hT s

end Problem367

end

end OAI

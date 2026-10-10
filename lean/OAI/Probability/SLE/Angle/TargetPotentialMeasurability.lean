import OAI.Probability.SLE.Angle.TargetFlowMeasurability

namespace OAI

/-! The exact prescribed disk potential is a measurable path functional.
All definitions, including the killed flow and its time integral, are
retained on every continuous based driver. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma measurable_diskMapInv (θ : ℝ) : Measurable (diskMapInv θ) := by
  unfold diskMapInv
  fun_prop

lemma measurable_initialRadius (θ : ℝ) : Measurable (initialRadius θ) := by
  exact (measurable_const.mul (Complex.measurable_im.comp (measurable_diskMapInv θ))).mul
    (((measurable_deriv (diskMap θ)).comp (measurable_diskMapInv θ)).norm)

private lemma measurable_clockIntegrand (κ θ : ℝ) :
    Measurable (fun q : (ℝ≥0 × (Driver × ℂ)) × ℝ =>
      (flow κ q.1.2.1 (diskMapInv θ q.1.2.2) q.2.toNNReal).im ^ 2 /
        ‖flow κ q.1.2.1 (diskMapInv θ q.1.2.2) q.2.toNNReal -
          (driverValue q.1.2.1 q.2 : ℂ)‖ ^ 4) := by
  have hp : Measurable (fun q : (ℝ≥0 × (Driver × ℂ)) × ℝ =>
      (q.2.toNNReal,(q.1.2.1,diskMapInv θ q.1.2.2))) :=
    (continuous_real_toNNReal.measurable.comp measurable_snd).prodMk
      ((measurable_fst.snd.fst).prodMk
        ((measurable_diskMapInv θ).comp measurable_fst.snd.snd))
  have hF : Measurable (fun q : (ℝ≥0 × (Driver × ℂ)) × ℝ =>
      flow κ q.1.2.1 (diskMapInv θ q.1.2.2) q.2.toNNReal) :=
    @Measurable.comp ((ℝ≥0 × (Driver × ℂ)) × ℝ) (ℝ≥0 × (Driver × ℂ)) ℂ
      inferInstance inferInstance inferInstance (fun q => flow κ q.2.1 q.2.2 q.1)
      (fun q => (q.2.toNNReal,(q.1.2.1,diskMapInv θ q.1.2.2))) (measurable_flow κ) hp
  have hB : Measurable (fun q : (ℝ≥0 × (Driver × ℂ)) × ℝ =>
      driverValue q.1.2.1 q.2) :=
    continuous_eval.measurable.comp (measurable_fst.snd.fst.prodMk
      (continuous_real_toNNReal.measurable.comp measurable_snd))
  exact ((Complex.measurable_im.comp hF).pow_const 2).div ((hF.sub hB.complex_ofReal).norm.pow_const 4)

lemma measurable_clock (κ θ : ℝ) :
    Measurable (fun q : ℝ≥0 × (Driver × ℂ) => clock κ θ q.2.1 q.2.2 q.1) := by
  let A : Set ((ℝ≥0 × (Driver × ℂ)) × ℝ) := {q | 0 ≤ q.2 ∧ q.2 ≤ (q.1.1 : ℝ)}
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst.coe_nnreal_real)
  have hm : StronglyMeasurable (fun q : ℝ≥0 × (Driver × ℂ) => ∫ u : ℝ,
      A.indicator (fun p : (ℝ≥0 × (Driver × ℂ)) × ℝ =>
        (flow κ p.1.2.1 (diskMapInv θ p.1.2.2) p.2.toNNReal).im ^ 2 /
          ‖flow κ p.1.2.1 (diskMapInv θ p.1.2.2) p.2.toNNReal -
            (driverValue p.1.2.1 p.2 : ℂ)‖ ^ 4) (q,u)) :=
    ((measurable_clockIntegrand κ θ).indicator hA).stronglyMeasurable.integral_prod_right'
  convert hm.measurable using 1
  funext q
  rw [clock,← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Icc 0 (q.1 : ℝ)
  · have hu' : (q,u) ∈ A := hu
    simp only [indicator_of_mem hu,indicator_of_mem hu']
    simp only [Real.toNNReal_of_nonneg hu.1,NNReal.coe_mk,centeredFlow]
  · have hu' : (q,u) ∉ A := hu
    simp only [indicator_of_notMem hu,indicator_of_notMem hu']

lemma measurable_angle (κ θ : ℝ) :
    Measurable (fun q : ℝ≥0 × (Driver × ℂ) => angle κ θ q.2.1 q.2.2 q.1) := by
  have hpoint : Measurable (fun q : ℝ≥0 × (Driver × ℂ) =>
      (q.1,(q.2.1,diskMapInv θ q.2.2))) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk
      ((measurable_diskMapInv θ).comp measurable_snd.snd))
  have hF : Measurable (fun q : ℝ≥0 × (Driver × ℂ) =>
      flow κ q.2.1 (diskMapInv θ q.2.2) q.1) :=
    @Measurable.comp (ℝ≥0 × (Driver × ℂ)) (ℝ≥0 × (Driver × ℂ)) ℂ
      inferInstance inferInstance inferInstance (fun q => flow κ q.2.1 q.2.2 q.1)
      (fun q => (q.1,(q.2.1,diskMapInv θ q.2.2))) (measurable_flow κ) hpoint
  have hB : Measurable (fun q : ℝ≥0 × (Driver × ℂ) => driverValue q.2.1 q.1) := by
    simpa only [driverValue,Real.toNNReal_coe,Function.comp_def] using
      (continuous_eval.measurable.comp (measurable_snd.fst.prodMk measurable_fst) :
        Measurable (fun q : ℝ≥0 × (Driver × ℂ) => q.2.1 q.1))
  exact (hF.sub hB.complex_ofReal).carg

lemma measurable_radius (κ θ : ℝ) :
    Measurable (fun q : ℝ≥0 × (Driver × ℂ) => radius κ θ q.2.1 q.2.2 q.1) := by
  exact ((measurable_initialRadius θ).comp measurable_snd.snd).mul
    ((measurable_const.mul (measurable_clock κ θ)).exp)

private lemma measurableSet_disk_surviving (κ θ : ℝ) :
    MeasurableSet {q : ℝ≥0 × (Driver × ℂ) |
      Surviving κ q.2.1 (diskMapInv θ q.2.2) q.1} := by
  have hpoint : Measurable (fun q : ℝ≥0 × (Driver × ℂ) =>
      (q.1,(q.2.1,diskMapInv θ q.2.2))) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk
      ((measurable_diskMapInv θ).comp measurable_snd.snd))
  exact hpoint (measurableSet_surviving κ)

lemma measurable_green (κ θ : ℝ) :
    Measurable (fun q : ℝ≥0 × (Driver × ℂ) => green κ θ q.2.1 q.2.2 q.1) := by
  have hbody : Measurable (fun q : ℝ≥0 × (Driver × ℂ) =>
      radius κ θ q.2.1 q.2.2 q.1 ^ (-α κ) * Real.sin (angle κ θ q.2.1 q.2.2 q.1) ^ p κ) :=
    ((measurable_radius κ θ).pow_const (-α κ)).mul
      ((measurable_angle κ θ).sin.pow_const (p κ))
  unfold green
  exact hbody.ite (measurableSet_disk_surviving κ θ) measurable_const

lemma measurable_potential (κ θ : ℝ) (t : ℝ≥0) :
    Measurable (fun b : Driver => potential κ θ b t) := by
  have hm : Measurable (fun q : Driver × ℂ => ENNReal.ofReal (green κ θ q.1 q.2 t)) :=
    ((measurable_green κ θ).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  exact @Measurable.lintegral_prod_right' _ _ _ _ (volume.restrict diskK) _ _ hm

lemma clock_stopDriver (κ θ : ℝ) (b : Driver) (x : ℂ) (T t : ℝ≥0) (ht : t ≤ T) :
    clock κ θ (stopDriver b T) x t = clock κ θ b x t := by
  unfold clock
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  let s : ℝ≥0 := ⟨u,hu.1⟩
  have hs : s ≤ T := (show s ≤ t from hu.2).trans ht
  have he := (surviving_flow_stopDriver κ b (diskMapInv θ x) T s hs).2
  change flow κ (stopDriver b T) (diskMapInv θ x) u = flow κ b (diskMapInv θ x) u at he
  dsimp only
  rw [he]
  have hb : driverValue (stopDriver b T) u = driverValue b u := by
    simp only [driverValue,stopDriver_apply,Real.toNNReal_of_nonneg hu.1]
    change b (min s T) = b s
    rw [min_eq_left hs]
  simp only [centeredFlow,he,hb]

lemma green_stopDriver (κ θ : ℝ) (b : Driver) (x : ℂ) (T t : ℝ≥0) (ht : t ≤ T) :
    green κ θ (stopDriver b T) x t = green κ θ b x t := by
  have he := surviving_flow_stopDriver κ b (diskMapInv θ x) T t ht
  have hb : driverValue (stopDriver b T) t = driverValue b t := by
    simp only [driverValue,stopDriver_apply,Real.toNNReal_coe,min_eq_left ht]
  simp only [green,he.1,radius,clock_stopDriver κ θ b x T t ht,angle,centeredFlow,he.2,hb]

lemma potential_stopDriver (κ θ : ℝ) (b : Driver) (T t : ℝ≥0) (ht : t ≤ T) :
    potential κ θ (stopDriver b T) t = potential κ θ b t := by
  unfold potential
  apply lintegral_congr
  intro x
  rw [green_stopDriver κ θ b x T t ht]

lemma potential_measurable_past (κ θ : ℝ) (T t : ℝ≥0) (ht : t ≤ T) :
    Measurable[driverFiltration T] (fun b : Driver => potential κ θ b t) := by
  have hm := (measurable_potential κ θ t).comp (stopDriver_measurable_past T)
  simpa only [Function.comp_def,potential_stopDriver κ θ _ T t ht] using hm

theorem potential_continuation_condLExp (κ θ : ℝ) (W : WienerLaw) (hW : IsWiener W)
    (t T : ℝ≥0) :
    (fun b : Driver => ∫⁻ c, potential κ θ (concat b c t) T ∂W) =ᵐ[W]
      W⁻[(fun b : Driver => potential κ θ b T) | driverFiltration t] :=
  continuationMean_condLExp W hW t (fun b => potential κ θ b T)
    (measurable_potential κ θ T)

theorem potential_continuation_finite_condExp (κ θ : ℝ) (W : WienerLaw) (hW : IsWiener W)
    (t T : ℝ≥0) (hfin : (∫⁻ b, potential κ θ b T ∂W) ≠ ∞) :
    (∀ᵐ b ∂W, (∫⁻ c, potential κ θ (concat b c t) T ∂W) < ∞) ∧
    (fun b : Driver => (∫⁻ c, potential κ θ (concat b c t) T ∂W).toReal) =ᵐ[W]
      W[(fun b : Driver => (potential κ θ b T).toReal) | driverFiltration t] :=
  continuationMean_finite_condExp W hW t (fun b => potential κ θ b T)
    (measurable_potential κ θ T) hfin

end SLEExactGauge.Target

end

end OAI

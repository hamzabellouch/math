import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.DynkinIdentity

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
namespace ExactSLEFlow
variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
omit [MeasurableSpace E] [BorelSpace E] in
lemma integral_flow_hasDerivWithinAt
    {A : E → E} (hA : Continuous A) {u f : ℝ≥0 → E}
    (hu : Continuous u) (hf : Continuous f) {x : E}
    (heq : ∀ t, f t = x + ∫ v in (0 : ℝ)..(t : ℝ), A (f v.toNNReal + u v.toNNReal))
    (T : ℝ≥0) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun v : ℝ => f v.toNNReal) (A (f t.toNNReal + u t.toNNReal))
      (Icc (0 : ℝ) T) t := by
  have hc : Continuous (fun v : ℝ => A (f v.toNNReal + u v.toNNReal)) :=
    hA.comp ((hf.comp continuous_real_toNNReal).add (hu.comp continuous_real_toNNReal))
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add x
  apply hd.hasDerivWithinAt.congr_of_mem _ ht
  intro v hv
  simpa only [Real.coe_toNNReal _ hv.1] using heq v.toNNReal

omit [MeasurableSpace E] [BorelSpace E] in
lemma integral_flow_unique
    {A : E → E} {K : ℝ≥0} (hA : LipschitzWith K A) {u v f g : ℝ≥0 → E}
    (hu : Continuous u) (hv : Continuous v) (hf : Continuous f) (hg : Continuous g) {x : E}
    (hfe : ∀ t, f t = x + ∫ w in (0 : ℝ)..(t : ℝ), A (f w.toNNReal + u w.toNNReal))
    (hge : ∀ t, g t = x + ∫ w in (0 : ℝ)..(t : ℝ), A (g w.toNNReal + v w.toNNReal))
    {T : ℝ≥0} (huv : ∀ t ≤ T, u t = v t) {t : ℝ≥0} (ht : t ≤ T) : f t = g t := by
  have hfd := integral_flow_hasDerivWithinAt hA.continuous hu hf hfe T
  have hgd : ∀ w ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun w : ℝ => g w.toNNReal)
      (A (g w.toNNReal + u w.toNNReal)) (Icc (0 : ℝ) T) w := by
    intro w hw
    rw [huv w.toNNReal ((Real.toNNReal_le_toNNReal hw.2).trans_eq (by simp))]
    exact integral_flow_hasDerivWithinAt hA.continuous hv hg hge T w hw
  have hf0 : f 0 = x := by simpa using hfe 0
  have hg0 : g 0 = x := by simpa using hge 0
  have h0 : f 0 = g 0 := hf0.trans hg0.symm
  have he := additive_flow_unique hA
    ((hf.comp continuous_real_toNNReal).continuousOn)
    ((hg.comp continuous_real_toNNReal).continuousOn) hfd hgd (by simpa using h0)
    (show (t : ℝ) ∈ Icc (0 : ℝ) T from ⟨t.coe_nonneg, ht⟩)
  simpa using he

 

theorem additive_flow_adapted
    (A : E → E) (L K : ℝ≥0) (hA : LipschitzWith K A) (hb : ∀ x, ‖A x‖ ≤ L)
    (u : ℝ≥0 → Ω → E) (huc : ∀ ω, Continuous (fun t => u t ω))
    (x : Ω → E) (Y : ℝ≥0 → Ω → E) (hYc : ∀ ω, Continuous (fun t => Y t ω))
    (hYe : ∀ ω t, Y t ω = x ω + ∫ v in (0 : ℝ)..(t : ℝ),
      A (Y v.toNNReal ω + u v.toNNReal ω))
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hum : ∀ t, Measurable[F t] (u t)) (hxm : Measurable[F 0] x) :
    ∀ t, Measurable[F t] (Y t) := by
  intro T
  let : MeasurableSpace Ω := F T
  let uT : ℝ≥0 → Ω → E := fun t ω => u (min t T) ω
  have huTc (ω : Ω) : Continuous (fun t => uT t ω) :=
    (huc ω).comp (continuous_id.min continuous_const)
  have huTm (t : ℝ≥0) : Measurable (uT t) :=
    (hum (min t T)).mono (F.mono (min_le_right _ _)) le_rfl
  have hx : Measurable x := hxm.mono (F.mono bot_le) le_rfl
  obtain ⟨Z, hZc, hZm, hZe⟩ := measurable_additive_flow A L K hA hb uT huTc huTm x hx
  have he : Y T = Z T := by
    funext ω
    exact integral_flow_unique hA (huc ω) (huTc ω) (hYc ω) (hZc ω) (hYe ω) (hZe ω)
      (T := T) (fun t ht => by simp [uT, min_eq_left ht]) le_rfl
  rw [he]
  exact hZm T

end ExactSLEFlow

namespace ExactSLEGenerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

theorem exists_adapted_additive_brownian
    (A : E → E) (L K : ℝ≥0) (hA : LipschitzWith K A) (hb : ∀ x, ‖A x‖ ≤ L)
    (x e : E) :
    ∃ X : ℝ≥0 → Driver → E,
      (∀ b, Continuous (fun t => X t b)) ∧
      (∀ t, Measurable[rawFiltration t] (X t)) ∧
      (∀ b, X 0 b = x) ∧
      (∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment s h b • e +
        ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b)) := by
  let u : ℝ≥0 → Driver → E := fun t b => b.1 t • e
  have huc (b : Driver) : Continuous (fun t => u t b) := b.1.continuous.smul continuous_const
  have hum (t : ℝ≥0) : Measurable (u t) := (driver_eval_measurable t).measurable.smul_const e
  have humF (t : ℝ≥0) : Measurable[rawFiltration t] (u t) := by
    have h := Filtration.stronglyAdapted_natural driver_eval_measurable t
    exact h.measurable.smul_const e
  obtain ⟨Y, hYc, hYm, hYe⟩ := ExactSLEFlow.measurable_additive_flow A L K hA hb
    u huc hum (fun _ => x) measurable_const
  have hYF := ExactSLEFlow.additive_flow_adapted A L K hA hb u huc (fun _ => x)
    Y hYc hYe rawFiltration humF measurable_const
  let X : ℝ≥0 → Driver → E := fun t b => Y t b + u t b
  refine ⟨X, fun b => (hYc b).add (huc b), fun t => (hYF t).add (humF t), ?_, ?_⟩
  · intro b
    have h0 := hYe b 0
    simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero] at h0
    simp [X, u, b.2, h0]
  · intro s h b
    have hc : Continuous (fun t : ℝ => A (X t.toNNReal b)) :=
      hA.continuous.comp (((hYc b).add (huc b)).comp continuous_real_toNNReal)
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable (0 : ℝ) s) (hc.intervalIntegrable (s : ℝ) (s+h : ℝ≥0))
    have hYs := hYe b s
    have hYt := hYe b (s+h)
    change Y (s+h) b + b.1 (s+h) • e =
      Y s b + b.1 s • e + (b.1 (s+h) - b.1 s) • e + ∫ t in (s : ℝ)..(s+h : ℝ≥0), A (X t.toNNReal b)
    change Y s b = x + ∫ t in (0 : ℝ)..(s : ℝ), A (X t.toNNReal b) at hYs
    change Y (s+h) b = x + ∫ t in (0 : ℝ)..(s+h : ℝ≥0), A (X t.toNNReal b) at hYt
    rw [hYs, hYt, ← hi, sub_smul]
    abel

 
omit [CompleteSpace E] in
lemma adapted_intervalIntegral {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (g : ℝ≥0 → Ω → E)
    (hc : ∀ ω, Continuous (fun t => g t ω)) (hm : ∀ t, Measurable[F t] (g t))
    (T : ℝ≥0) :
    Measurable[F T] (fun ω => ∫ t in (0 : ℝ)..(T : ℝ), g t.toNNReal ω) := by
  let : MeasurableSpace Ω := F T
  have hc' (ω : Ω) : Continuous (fun t : ℝ => g (min t.toNNReal T) ω) :=
    (hc ω).comp (continuous_real_toNNReal.min continuous_const)
  have hm' (t : ℝ) : Measurable (g (min t.toNNReal T)) :=
    (hm _).mono (F.mono (min_le_right _ _)) le_rfl
  have hme := stronglyMeasurable_intervalIntegral_of_continuous
    (fun t ω => g (min t.toNNReal T) ω) hc' hm' 0 T
  have he : (fun ω => ∫ t in (0 : ℝ)..(T : ℝ), g t.toNNReal ω) =
      (fun ω => ∫ t in (0 : ℝ)..(T : ℝ), g (min t.toNNReal T) ω) := by
    funext ω
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ≤ (T : ℝ) := (by simpa only [uIcc_of_le T.coe_nonneg] using ht : t ∈ Set.Icc 0 (T : ℝ)).2
    change g t.toNNReal ω = g (min t.toNNReal T) ω
    have htT : t.toNNReal ≤ T := (Real.toNNReal_le_toNNReal ht').trans_eq (by simp)
    rw [min_eq_left htT]
  rw [he]
  exact hme.measurable

end ExactSLEGenerator

namespace ExactSLEGenerator

 

theorem martingale_compensated_of_weighted
    (W : Measure Driver) [IsProbabilityMeasure W]
    (F G : ℝ≥0 → Driver → ℝ)
    (hFm : ∀ t, Measurable[rawFiltration t] (F t))
    (hFi : ∀ t, Integrable (F t) W)
    (hGc : ∀ b, Continuous (fun t => G t b))
    (hGm : ∀ t, Measurable[rawFiltration t] (G t))
    (C : ℝ) (hGb : ∀ b t, |G t b| ≤ C)
    (hw : ∀ (s h : ℝ≥0) (J : Driver → ℝ), Measurable[rawFiltration s] J →
      (∀ b, |J b| ≤ 1) →
      (∫ b, J b * F (s+h) b ∂W) - (∫ b, J b * F s b ∂W) =
        ∫ b, J b * (∫ u in (s : ℝ)..(s+h : ℝ≥0), G u.toNNReal b) ∂W) :
    Martingale (fun t b => F t b - ∫ u in (0 : ℝ)..(t : ℝ), G u.toNNReal b)
      rawFiltration W := by
  let I : ℝ≥0 → Driver → ℝ := fun t b => ∫ u in (0 : ℝ)..(t : ℝ), G u.toNNReal b
  have hIm (t : ℝ≥0) : Measurable[rawFiltration t] (I t) :=
    adapted_intervalIntegral rawFiltration G hGc hGm t
  have hGg (t : ℝ≥0) : Measurable (G t) := (hGm t).mono (rawFiltration.le t) le_rfl
  have hseg (s t : ℝ) : Integrable (fun b => ∫ u in s..t, G u.toNNReal b) W := by
    apply Integrable.of_bound
      (stronglyMeasurable_intervalIntegral_of_continuous (fun u b => G u.toNNReal b)
        (fun b => (hGc b).comp continuous_real_toNNReal) (fun u => hGg _) s t).aestronglyMeasurable
      (C * |t-s|)
    exact ae_of_all W (fun b => intervalIntegral.norm_integral_le_of_norm_le_const
      (fun u hu => by simpa only [Real.norm_eq_abs] using hGb b u.toNNReal))
  have hIi (t : ℝ≥0) : Integrable (I t) W := hseg 0 t
  have hMa (t : ℝ≥0) : StronglyMeasurable[rawFiltration t] (fun b => F t b - I t b) :=
    ((hFm t).sub (hIm t)).stronglyMeasurable
  have hMi (t : ℝ≥0) : Integrable (fun b => F t b - I t b) W := (hFi t).sub (hIi t)
  refine ⟨hMa, ?_⟩
  intro s t hst
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (rawFiltration.le s) (hMi t)
    (fun E hE hEfin => (hMi s).integrableOn) _ (hMa s).aestronglyMeasurable
  intro E hE hEfin
  have hEe : MeasurableSet E := rawFiltration.le s _ hE
  let J : Driver → ℝ := E.indicator (fun _ => 1)
  have hJm : Measurable[rawFiltration s] J := measurable_const.indicator hE
  have hJb (b : Driver) : |J b| ≤ 1 := by
    by_cases hb : b ∈ E <;> simp [J, hb]
  have hJF (H : Driver → ℝ) : (fun b => J b * H b) = E.indicator H := by
    funext b
    by_cases hb : b ∈ E <;> simp [J, hb]
  have he := hw s (t-s) J hJm hJb
  rw [add_tsub_cancel_of_le hst] at he
  simp only [hJF, integral_indicator hEe] at he
  have hIadd (b : Driver) : I t b = I s b + ∫ u in (s : ℝ)..(t : ℝ), G u.toNNReal b := by
    have hc := (hGc b).comp continuous_real_toNNReal
    exact (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable (0 : ℝ) s) (hc.intervalIntegrable (s : ℝ) t)).symm
  have hIset : (∫ b in E, I t b ∂W) = (∫ b in E, I s b ∂W) +
      (∫ b in E, (∫ u in (s : ℝ)..(t : ℝ), G u.toNNReal b) ∂W) := by
    simp_rw [hIadd]
    exact integral_add (hIi s).integrableOn (hseg s t).integrableOn
  change (∫ b in E, F s b - I s b ∂W) = ∫ b in E, F t b - I t b ∂W
  rw [integral_sub (hFi s).integrableOn (hIi s).integrableOn,
    integral_sub (hFi t).integrableOn (hIi t).integrableOn, hIset]
  linarith

end ExactSLEGenerator

namespace ExactSLEGenerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma intervalIntegral_nnreal_shift (H : ℝ≥0 → E) (start s t : ℝ≥0) :
    (∫ u in (s : ℝ)..(t : ℝ), H (start+u.toNNReal)) =
      ∫ u in (start+s : ℝ≥0)..(start+t : ℝ≥0), H u.toNNReal := by
  calc
    _ = ∫ u in (s : ℝ)..(t : ℝ), H (((start : ℝ)+u).toNNReal) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : 0 ≤ u := le_trans (le_min s.coe_nonneg t.coe_nonneg) hu.1
      change H (start+u.toNNReal) = H (((start : ℝ)+u).toNNReal)
      congr 1
      ext
      simp only [NNReal.coe_add, Real.coe_toNNReal _ hu0,
        Real.coe_toNNReal _ (add_nonneg start.coe_nonneg hu0)]
    _ = _ := by
      simpa only [NNReal.coe_add] using
        (intervalIntegral.integral_comp_add_left (fun u : ℝ => H u.toNNReal) (start : ℝ))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma shift_additive_equation
    (X : ℝ≥0 → Driver → E) (A : E → E) (e : E)
    (hXeq : ∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment s h b • e +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b))
    (start s h : ℝ≥0) (b : Driver) :
    X (start+(s+h)) b = X (start+s) b + increment (start+s) h b • e +
      ∫ t in (s : ℝ)..(s+h : ℝ≥0), A (X (start+t.toNNReal) b) := by
  rw [intervalIntegral_nnreal_shift (fun v => A (X v b)) start s (s+h), ← add_assoc]
  exact hXeq (start+s) h b

lemma integrable_intervalIntegral_of_bound
    (W : Measure Driver) [IsProbabilityMeasure W] (G : ℝ≥0 → Driver → ℝ)
    (hc : ∀ b, Continuous (fun t => G t b)) (hm : ∀ t, Measurable (G t))
    (C : ℝ) (hb : ∀ b t, |G t b| ≤ C) (s t : ℝ) :
    Integrable (fun b => ∫ u in s..t, G u.toNNReal b) W := by
  apply Integrable.of_bound
    (stronglyMeasurable_intervalIntegral_of_continuous (fun u b => G u.toNNReal b)
      (fun b => (hc b).comp continuous_real_toNNReal) (fun u => hm _) s t).aestronglyMeasurable
    (C * |t-s|)
  exact ae_of_all W (fun b => intervalIntegral.norm_integral_le_of_norm_le_const
    (fun u hu => by simpa only [Real.norm_eq_abs] using hb b u.toNNReal))

 

theorem additive_brownian_martingale (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (X : ℝ≥0 → Driver → E) (hXc : ∀ b, Continuous (fun t => X t b))
    (hXm : ∀ t, Measurable[rawFiltration t] (X t))
    (A : E → E) (hAc : Continuous A) (K : ℝ) (hK : 0 ≤ K) (hAb : ∀ x, ‖A x‖ ≤ K)
    (e : E) (he : ‖e‖ ≤ 1)
    (hXeq : ∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment s h b • e +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b))
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (hD : ∀ x, HasFDerivAt f (D x) x)
    (hDc : Continuous D)
    (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hLip : ∀ x y, ‖D y - D x‖ ≤ C * ‖y-x‖)
    (hSmooth : ∀ x, ContDiff ℝ 3 (fun w : ℝ => f (x + w • e)))
    (hThird : ∀ x w, |iteratedDeriv 3 (fun r : ℝ => f (x + r • e)) w| ≤ C)
    (hQc : Continuous (fun x => iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0))
    (hfb : ∀ x, |f x| ≤ M) (hDb : ∀ x, ‖D x‖ ≤ M)
    (hQb : ∀ x, |iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0| ≤ M) :
    Martingale (fun t b => f (X t b) - ∫ u in (0 : ℝ)..(t : ℝ),
      ((1/2 : ℝ) * iteratedDeriv 2 (fun r : ℝ => f (X u.toNNReal b + r • e)) 0 +
        D (X u.toNNReal b) (A (X u.toNNReal b)))) rawFiltration W := by
  let Q : E → ℝ := fun x => iteratedDeriv 2 (fun r : ℝ => f (x + r • e)) 0
  let V : E → ℝ := fun x => D x (A x)
  let G : E → ℝ := fun x => (1/2 : ℝ)*Q x + V x
  have hVc : Continuous V := hDc.clm_apply hAc
  have hGc : Continuous G := (continuous_const.mul hQc).add hVc
  have hVb (x : E) : |V x| ≤ M*K := by
    calc
      _ = ‖D x (A x)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖D x‖ * ‖A x‖ := (D x).le_opNorm _
      _ ≤ M*K := mul_le_mul (hDb x) (hAb x) (norm_nonneg _) hM
  have hGb (x : E) : |G x| ≤ M/2 + M*K := by
    calc
      _ ≤ |(1/2 : ℝ)*Q x| + |V x| := abs_add_le _ _
      _ ≤ (1/2 : ℝ)*M + M*K := add_le_add (by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
        exact mul_le_mul_of_nonneg_left (hQb x) (by norm_num)) (hVb x)
      _ = _ := by ring
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  have hXg (t : ℝ≥0) : Measurable (X t) := (hXm t).mono (rawFiltration.le t) le_rfl
  apply martingale_compensated_of_weighted W (fun t b => f (X t b))
    (fun t b => G (X t b))
    (fun t => hfc.measurable.comp (hXm t))
    (fun t => Integrable.of_bound (hfc.measurable.comp (hXg t)).aestronglyMeasurable M
      (ae_of_all W (fun b => by simpa only [Real.norm_eq_abs] using hfb (X t b))))
    (fun b => hGc.comp (hXc b))
    (fun t => hGc.measurable.comp (hXm t)) (M/2+M*K) (fun b t => hGb _) 
  intro s h J hJm hJb
  have hc (b : Driver) : Continuous (fun t => X (s+t) b) :=
    (hXc b).comp (continuous_const.add continuous_id)
  have hdyn := additive_brownian_weighted_dynkin W hW s (fun t b => X (s+t) b)
    hc (fun t => hXm (s+t)) A hAc K hK hAb e he (shift_additive_equation X A e hXeq s)
    f D hD hDc C M hC hM hLip hSmooth hThird hQc hfb hDb hQb J hJm hJb h
  have hiQ (b : Driver) : (∫ u in (0 : ℝ)..(h : ℝ), Q (X (s+u.toNNReal) b)) =
      ∫ u in (s : ℝ)..(s+h : ℝ≥0), Q (X u.toNNReal b) := by
    simpa only [NNReal.coe_zero, add_zero] using
      (intervalIntegral_nnreal_shift (fun t => Q (X t b)) s 0 h)
  have hiV (b : Driver) : (∫ u in (0 : ℝ)..(h : ℝ), V (X (s+u.toNNReal) b)) =
      ∫ u in (s : ℝ)..(s+h : ℝ≥0), V (X u.toNNReal b) := by
    simpa only [NNReal.coe_zero, add_zero] using
      (intervalIntegral_nnreal_shift (fun t => V (X t b)) s 0 h)
  change (∫ b, J b * f (X (s+h) b) ∂W) - (∫ b, J b * f (X (s+0) b) ∂W) =
    (1/2 : ℝ) * (∫ b, J b * (∫ u in (0 : ℝ)..(h : ℝ), Q (X (s+u.toNNReal) b)) ∂W) +
    (∫ b, J b * (∫ u in (0 : ℝ)..(h : ℝ), V (X (s+u.toNNReal) b)) ∂W) at hdyn
  simp_rw [add_zero, hiQ, hiV] at hdyn
  rw [hdyn]
  have hJ : AEStronglyMeasurable J W := (hJm.mono (rawFiltration.le _) le_rfl).aestronglyMeasurable
  have hJi : ∀ᵐ b ∂W, ‖J b‖ ≤ 1 := ae_of_all W (fun b => by simpa only [Real.norm_eq_abs] using hJb b)
  have hQi := integrable_intervalIntegral_of_bound W (fun t b => Q (X t b))
    (fun b => hQc.comp (hXc b)) (fun t => hQc.measurable.comp (hXg t)) M
    (fun b t => hQb _) s (s+h : ℝ≥0)
  have hVi := integrable_intervalIntegral_of_bound W (fun t b => V (X t b))
    (fun b => hVc.comp (hXc b)) (fun t => hVc.measurable.comp (hXg t)) (M*K)
    (fun b t => hVb _) s (s+h : ℝ≥0)
  have hiG (b : Driver) : (∫ u in (s : ℝ)..(s+h : ℝ≥0), G (X u.toNNReal b)) =
      (1/2 : ℝ)*(∫ u in (s : ℝ)..(s+h : ℝ≥0), Q (X u.toNNReal b)) +
      (∫ u in (s : ℝ)..(s+h : ℝ≥0), V (X u.toNNReal b)) := by
    have hqc : Continuous (fun u : ℝ => Q (X u.toNNReal b)) :=
      hQc.comp ((hXc b).comp continuous_real_toNNReal)
    have hvc : Continuous (fun u : ℝ => V (X u.toNNReal b)) :=
      hVc.comp ((hXc b).comp continuous_real_toNNReal)
    rw [show (fun u : ℝ => G (X u.toNNReal b)) =
      (fun u : ℝ => (1/2 : ℝ)*Q (X u.toNNReal b) + V (X u.toNNReal b)) from rfl]
    rw [intervalIntegral.integral_add ((hqc.intervalIntegrable _ _).const_mul _) (hvc.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
  simp_rw [hiG, mul_add, ← mul_assoc, mul_comm _ (1/2 : ℝ), mul_assoc]
  rw [integral_add ((hQi.bdd_mul hJ hJi).const_mul _) (hVi.bdd_mul hJ hJi), integral_const_mul]

end ExactSLEGenerator

namespace ExactSLEGenerator
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def directional (n : ℕ) (f : E → ℝ) (e : E) : E → ℝ :=
  Nat.rec f (fun _ g x => fderiv ℝ g x e) n

omit [CompleteSpace E] in
lemma directional_contDiff (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (e : E) (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (directional n f e) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

omit [CompleteSpace E] in
lemma directional_compact (f : E → ℝ) (hf : HasCompactSupport f) (e : E) (n : ℕ) :
    HasCompactSupport (directional n f e) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.fderiv_apply ℝ e

omit [CompleteSpace E] in
lemma iteratedDeriv_line (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (e x : E) (n : ℕ) :
    iteratedDeriv n (fun r : ℝ => f (x + r • e)) = fun r => directional n f e (x+r • e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext r
    have hd : HasDerivAt (fun r : ℝ => x+r • e) e r := by
      convert (hasDerivAt_const r x).add ((hasDerivAt_id r).smul_const e) using 1 <;> first | rfl | simp only [zero_add,one_smul]
    exact (((directional_contDiff f hf e n).differentiable (by simp) (x+r • e)).hasFDerivAt.comp_hasDerivAt r hd).deriv

omit [CompleteSpace E] in
lemma compact_smooth_fderiv_bound (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x y, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ C * ‖y-x‖ := by
  have hd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdc : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  have hddc : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := hdc.fderiv ℝ
  have hdd : Continuous (fderiv ℝ (fderiv ℝ f)) := hd.continuous_fderiv (by simp)
  have hbnd : ∃ C : ℝ, ∀ x : E, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := HasCompactSupport.exists_bound_of_continuous (f := fderiv ℝ (fderiv ℝ f)) hddc hdd
  obtain ⟨C,hC⟩ := hbnd
  refine ⟨C, fun x y => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun u _ => hd.differentiable (by simp) u) (fun u _ => hC u)
    convex_univ (mem_univ x) (mem_univ y)

omit [CompleteSpace E] in
lemma compact_smooth_line_bound (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hfc : HasCompactSupport f) (e : E) (n : ℕ) :
    ∃ C : ℝ, ∀ x w, |iteratedDeriv n (fun r : ℝ => f (x+r • e)) w| ≤ C := by
  obtain ⟨C,hC⟩ := (directional_compact f hfc e n).exists_bound_of_continuous
    (directional_contDiff f hf e n).continuous
  refine ⟨C, fun x w => ?_⟩
  rw [iteratedDeriv_line f hf e x n]
  exact (show |directional n f e (x+w • e)| ≤ C by
    simpa only [Real.norm_eq_abs] using hC (x+w • e))

omit [CompleteSpace E] in
lemma compact_smooth_test_bounds (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hfc : HasCompactSupport f) (e : E) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      (∀ x y, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ C * ‖y-x‖) ∧
      (∀ x w, |iteratedDeriv 3 (fun r : ℝ => f (x+r • e)) w| ≤ C) ∧
      (∀ x, |f x| ≤ M) ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ M) ∧
      (∀ x, |iteratedDeriv 2 (fun r : ℝ => f (x+r • e)) 0| ≤ M) := by
  obtain ⟨C₀,hC₀⟩ := compact_smooth_fderiv_bound f hf hfc
  obtain ⟨C₁,hC₁⟩ := compact_smooth_line_bound f hf hfc e 3
  obtain ⟨M₀,hM₀⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hdc : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  obtain ⟨M₁,hM₁⟩ := hdc.exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  obtain ⟨M₂,hM₂⟩ := compact_smooth_line_bound f hf hfc e 2
  let C := max 0 (max C₀ C₁)
  let M := max 0 (max M₀ (max M₁ M₂))
  have hC₀' : C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₁' : C₁ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hM₀' : M₀ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM₁' : M₁ ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hM₂' : M₂ ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C,M,le_max_left _ _,le_max_left _ _,?_,?_,?_,?_,?_⟩
  · intro x y
    exact (hC₀ x y).trans (mul_le_mul_of_nonneg_right hC₀' (norm_nonneg _))
  · intro x w
    exact (hC₁ x w).trans hC₁'
  · intro x
    exact (show |f x| ≤ M₀ by simpa only [Real.norm_eq_abs] using hM₀ x).trans hM₀'
  · intro x
    exact (hM₁ x).trans hM₁'
  · intro x
    exact (hM₂ x 0).trans hM₂'

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

end ExactSLEGenerator
end

end OAI

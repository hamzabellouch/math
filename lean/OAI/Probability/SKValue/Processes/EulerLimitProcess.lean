import Mathlib
import OAI.Probability.SKValue.Processes.Volterra

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
noncomputable def eulerLimitProcess (W:BrownianSpace) (γ:OrderParameter) (t:ℝ) (z:W.Ω):ℝ :=
  if 0<t ∧ t<1 then limsup (fun N:ℕ ↦ coupledEuler t γ.coeff (gradient W γ) W.B N N z) atTop else 0
lemma eulerLimitProcess_zero (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω):eulerLimitProcess W γ 0 z=0 :=by
  simp [eulerLimitProcess]
lemma eulerLimitProcess_measurable (W:BrownianSpace) (γ:OrderParameter) (t:ℝ):
    StronglyMeasurable[W.filtration t.toNNReal] (eulerLimitProcess W γ t) := by
  by_cases ht:0<t ∧ t<1
  · change StronglyMeasurable[W.filtration t.toNNReal] (fun z ↦ if 0<t ∧ t<1 then limsup (fun N:ℕ ↦ coupledEuler t γ.coeff (gradient W γ) W.B N N z) atTop else 0)
    simp only [ite_eq_left ht]
    apply Measurable.stronglyMeasurable
    apply Measurable.limsup
    intro N
    by_cases hN:N=0
    · subst N
      exact measurable_const
    have hN':0<N:=Nat.pos_of_ne_zero hN
    have hh:=coupled_euler_past_measurable W.measurable ht.1 hN' γ.coeff (gradient W γ)
      (fun j hj ↦ ((phi_evolution W γ ⟨ht.1.le,ht.2⟩).slices _ (mesh_time_mem ht.1.le hN' hj.le)).jets.smooth.continuous.measurable) N le_rfl
    have he:meshTime t N N=t:=by dsimp [meshTime,stepSize];field_simp
    rw [he] at hh
    exact hh.measurable
  · change StronglyMeasurable[W.filtration t.toNNReal] (fun z ↦ if 0<t ∧ t<1 then limsup (fun N:ℕ ↦ coupledEuler t γ.coeff (gradient W γ) W.B N N z) atTop else 0)
    simp only [ite_eq_right ht]
    exact stronglyMeasurable_const
lemma eulerLimitProcess_eq_path (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω)
    {T:ℝ} (hT:T∈Ico (0:ℝ) 1) {X:ℝ → ℝ}
    (hc:ContinuousOn X (Icc (0:ℝ) T))
    (hi:IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (X s)) volume 0 T)
    (he:∀t∈Icc (0:ℝ) T,X t=W.B t.toNNReal z+∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (X s))
    (h0:X 0=0) {t:ℝ} (ht:t∈Icc (0:ℝ) T):eulerLimitProcess W γ t z=X t := by
  rcases ht.1.eq_or_lt with htz|htz
  · subst t
    rw [eulerLimitProcess_zero,h0]
  have ht1:t<1:=ht.2.trans_lt hT.2
  obtain ⟨K,L,Lu,hLu,hG,hu⟩:=(sourceStripRegularity W γ).core t ⟨htz.le,ht1⟩
  have hsub:Icc (0:ℝ) t⊆Icc (0:ℝ) T:=Icc_subset_Icc le_rfl ht.2
  have hi':IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (X s)) volume 0 t:=hi.mono_set (by
    rw [uIcc_of_le htz.le,uIcc_of_le hT.1];exact hsub)
  have hv:=driven_euler_uniform_convergence
    (Y:=fun N j ↦ coupledEuler t γ.coeff (gradient W γ) W.B N j z) htz.le hLu
    (γ.monotone.mono (fun s hs ↦ ⟨hs.1,hs.2.trans_lt ht1⟩))
    (γ.nonneg 0 (by norm_num)) (fun s hs x ↦ gradient_bound W γ ⟨hs.1,hs.2.trans ht1.le⟩ x)
    hu (hc.mono hsub) hi' (fun s hs ↦ he s (hsub hs)) h0
    (fun N ↦ coupled_euler_zero t γ.coeff (gradient W γ) W.B N z)
    (fun N hN j hj ↦ coupled_euler_step W.B htz γ.coeff (gradient W γ) hN hj z)
  have hl:Tendsto (fun N:ℕ ↦ coupledEuler t γ.coeff (gradient W γ) W.B N N z) atTop (𝓝 (X t)) :=by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩:=eventually_atTop.mp (hv ε hε)
    refine ⟨max N 1,?_⟩
    intro n hn
    have hnpos:0<n:= lt_of_lt_of_le (by norm_num:(0:ℕ)<1) ((le_max_right N 1).trans hn)
    have hh:=hN n ((le_max_left N 1).trans hn) n le_rfl
    have hnt:(n:ℝ)*(t/n)=t:=by field_simp
    simpa only [hnt,Real.dist_eq] using hh
  simpa only [eulerLimitProcess,ite_eq_left (show 0<t ∧ t<1 from ⟨htz,ht1⟩)] using hl.limsup_eq
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
lemma eulerLimitProcess_local_path (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω)
    (hb:Continuous (fun t:ℝ ↦ W.B t.toNNReal z)) (h0:W.B 0 z=0)
    {T:ℝ} (hT:T∈Ico (0:ℝ) 1):
    ContinuousOn (fun t ↦ eulerLimitProcess W γ t z) (Icc (0:ℝ) T) ∧
    IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (eulerLimitProcess W γ s z)) volume 0 T ∧
    ∀t∈Icc (0:ℝ) T,eulerLimitProcess W γ t z=W.B t.toNNReal z+
      ∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (eulerLimitProcess W γ s z) :=by
  obtain ⟨X,hc,hi,he⟩:=exists_local_diffusion_path W γ hT _ hb.continuousOn
  have hz:X 0=0:=by simpa only [Real.toNNReal_zero,h0,intervalIntegral.integral_same,add_zero] using he 0 ⟨le_rfl,hT.1⟩
  have heq (t:ℝ) (ht:t∈Icc (0:ℝ) T):eulerLimitProcess W γ t z=X t:=
    eulerLimitProcess_eq_path W γ z hT hc hi he hz ht
  refine ⟨hc.congr heq,hi.congr (fun s hs ↦ ?_),?_⟩
  · rw [uIoc_of_le hT.1] at hs
    rw [heq s ⟨hs.1.le,hs.2⟩]
  intro t ht
  rw [heq t ht,he t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  dsimp only
  rw [heq s ⟨hs.1,hs.2.trans ht.2⟩]
lemma continuousOn_preterminal_of_strips {f:ℝ → ℝ}
    (h:∀T∈Ico (0:ℝ) 1,ContinuousOn f (Icc (0:ℝ) T)):
    ContinuousOn f (Ico (0:ℝ) 1) :=by
  intro t ht
  obtain ⟨T,htT,hT⟩:=exists_between ht.2
  apply (h T ⟨ht.1.trans htT.le,hT⟩ t ⟨ht.1,htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩
lemma eulerLimitProcess_drift_integrable (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω)
    (hb:Continuous (fun t:ℝ ↦ W.B t.toNNReal z)) (h0:W.B 0 z=0):
    IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (eulerLimitProcess W γ s z)) volume 0 1 :=by
  have hu:ContinuousOn (fun s ↦ gradient W γ s (eulerLimitProcess W γ s z)) (Ico (0:ℝ) 1):=by
    apply continuousOn_preterminal_of_strips
    intro T hT
    obtain ⟨K,L,Lu,hLu,hG,hLip⟩:=(sourceStripRegularity W γ).core T hT
    have hj:ContinuousOn (fun p:ℝ×ℝ ↦ gradient W γ p.1 p.2) {p | p.1∈Icc (0:ℝ) T}:=
      derivative_joint_continuous hLu hLip
    have hp:ContinuousOn (fun s ↦ (s,eulerLimitProcess W γ s z)) (Icc (0:ℝ) T):=
      continuousOn_id.prodMk (eulerLimitProcess_local_path W γ z hb h0 hT).1
    exact ContinuousOn.comp (g:=fun p:ℝ×ℝ ↦ gradient W γ p.1 p.2)
      (f:=fun s ↦ (s,eulerLimitProcess W γ s z)) hj hp (fun s hs ↦ hs)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num:(0:ℝ)≤1)).mpr
  have hm:AEStronglyMeasurable (fun s ↦ gradient W γ s (eulerLimitProcess W γ s z)) (volume.restrict (Ioc (0:ℝ) 1)) :=by
    rw [←Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (hu.mono Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo
  apply γ.integrable.mul_bdd hm (c:=(1:ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simpa only [Real.norm_eq_abs] using gradient_bound W γ ⟨hs.1.le,hs.2⟩ (eulerLimitProcess W γ s z)
end SKValue

end

end OAI

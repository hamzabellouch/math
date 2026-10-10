import Mathlib
import OAI.Probability.SKValue.Control.Regularity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue

structure ForcedTest (T:ℝ) (γ:ℝ → ℝ) (u V b p:ℝ → ℝ → ℝ) (K L:ℝ) : Prop where
  K_nonneg : 0 ≤ K
  L_nonneg : 0 ≤ L
  gamma_nonneg : ∀ t∈Icc (0:ℝ) T,0 ≤ γ t
  gamma_mono : MonotoneOn γ (Icc (0:ℝ) T)
  drift_measurable : ∀ t∈Icc (0:ℝ) T,Measurable (u t)
  drift_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|u t x| ≤ 1
  smooth : ∀ t∈Icc (0:ℝ) T,ContDiff ℝ 3 (V t)
  bound : ∀ t∈Icc (0:ℝ) T,∀ x,|V t x| ≤ K
  first_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|deriv (V t) x| ≤ K
  second_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|deriv (deriv (V t)) x| ≤ K
  third_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|iteratedDeriv 3 (V t) x| ≤ K
  b_measurable : ∀ t∈Icc (0:ℝ) T,Measurable (b t)
  p_measurable : ∀ t∈Icc (0:ℝ) T,Measurable (p t)
  b_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|b t x| ≤ K
  p_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|p t x| ≤ K
  b_lipschitz : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |b s y-b t x| ≤ L*(|s-t|+|y-x|)
  p_lipschitz : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |p s y-p t x| ≤ L*(|s-t|+|y-x|)
  b_integrable : ∀ y,IntervalIntegrable (fun s ↦ b s y) volume 0 T
  p_integrable : ∀ y,IntervalIntegrable (fun s ↦ γ s*p s y) volume 0 T
  pde : ∀ a∈Icc (0:ℝ) T,∀ d∈Icc (0:ℝ) T,∀ x,
    V d x-V a x=∫ s in a..d,(1/2:ℝ)*b s x+γ s*p s x
noncomputable def forcedSource (γ:ℝ → ℝ) (u V b p:ℝ → ℝ → ℝ) (t x:ℝ) : ℝ :=
  (1/2:ℝ)*(b t x+deriv (deriv (V t)) x)+γ t*(p t x+u t x*deriv (V t) x)
lemma ForcedTest.euler_one_step {T K L t δ x z:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) (ht:0 ≤ t) (hδ:0 ≤ δ) (hδ1:δ ≤ 1) (htδ:t+δ ≤ T) :
    let d:=Real.sqrt δ*z+δ*γ t*u t x
    |V (t+δ) (x+d)-V t x-δ*forcedSource γ u V b p t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2:ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) z+δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d:=Real.sqrt δ*z+δ*γ t*u t x
  have htT:t ≤ T := (le_add_of_nonneg_right hδ).trans htδ
  have hT:0 ≤ T := ht.trans htT
  have hsub:Icc t (t+δ) ⊆ Icc (0:ℝ) T := Icc_subset_Icc ht htδ
  have htm:t∈Icc (0:ℝ) T := ⟨ht,htT⟩
  have hem:t+δ∈Icc (0:ℝ) T := ⟨by linarith,htδ⟩
  have hTm:T∈Icc (0:ℝ) T := ⟨hT,le_rfl⟩
  have hbint (y:ℝ):IntervalIntegrable (fun s ↦ b s y) volume t (t+δ) :=
    (h.b_integrable y).mono_set (by rw [uIcc_of_le (by linarith:t ≤ t+δ),uIcc_of_le hT];exact hsub)
  have hpint (y:ℝ):IntervalIntegrable (fun s ↦ γ s*p s y) volume t (t+δ) :=
    (h.p_integrable y).mono_set (by rw [uIcc_of_le (by linarith:t ≤ t+δ),uIcc_of_le hT];exact hsub)
  have hgen:=gradient_generator_quadrature (b:=b) (p:=p) (y:=x+d)
    hδ (h.gamma_nonneg T hTm) h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub)
    (h.gamma_nonneg t htm) (h.gamma_mono htm hTm htT)
    (fun s hs ↦ h.p_bound s (hsub hs) _) (fun s hs ↦ h.b_lipschitz t htm s (hsub hs) x _)
    (fun s hs ↦ h.p_lipschitz t htm s (hsub hs) x _) (hbint _) (hpint _)
  have htime:|(V (t+δ) (x+d)-V t x+u t x-δ*forcedSource γ u V b p t x)-
      (V t (x+d)-V t x+u t x)+δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*u t x*deriv (V t) x)| ≤
      δ*(((1/2:ℝ)+γ T)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq:(V (t+δ) (x+d)-V t x+u t x-δ*forcedSource γ u V b p t x)-
        (V t (x+d)-V t x+u t x)+δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*u t x*deriv (V t) x)=
        (V (t+δ) (x+d)-V t (x+d))-δ*((1/2:ℝ)*b t x+γ t*p t x) := by
      unfold forcedSource;ring
    rw [heq,h.pde t htm (t+δ) hem]
    simpa only [add_sub_cancel_left] using hgen
  have hspace:|(V t (x+d)-V t x+u t x)-u t x-deriv (V t) x*d-
      (1/2:ℝ)*deriv (deriv (V t)) x*d^2| ≤ K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound (h.smooth t htm) h.K_nonneg (h.third_bound t htm) x d
  have hh:=euler_cubic_remainder hδ hδ1 (h.gamma_nonneg T hTm) h.K_nonneg
    (mul_nonneg (by linarith [h.gamma_nonneg T hTm] : 0 ≤ 1/2+γ T) h.L_nonneg)
    (by rw [abs_of_nonneg (h.gamma_nonneg t htm)];exact h.gamma_mono htm hTm htT)
    (h.drift_bound t htm x) (h.second_bound t htm x) hspace htime
  convert! hh using 1
  congr 1
  dsimp only [d,cubicEnvelope]
  ring
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma mean_observable_continuous {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsFiniteMeasure μ] {X:ℝ → Ω → ℝ} {T C:ℝ} {Q:ℝ → ℝ → ℝ}
    (hc:ContinuousOn (fun p:ℝ×ℝ ↦ Q p.1 p.2) (Icc (0:ℝ) T ×ˢ univ))
    (hb:∀ t∈Icc (0:ℝ) T,∀ x,|Q t x|≤C)
    (hXM:∀ t∈Icc (0:ℝ) T,AEStronglyMeasurable (X t) μ)
    (hXC:∀ᵐ z ∂μ,ContinuousOn (fun t ↦ X t z) (Icc (0:ℝ) T)) :
    ContinuousOn (fun t ↦ ∫ z,Q t (X t z) ∂μ) (Icc (0:ℝ) T) := by
  have hqc (t) (ht:t∈Icc (0:ℝ) T):Continuous (Q t) := by
    have hh : ContinuousOn (Q t) univ := hc.comp (continuousOn_const.prodMk continuousOn_id) (fun x _ ↦ ⟨ht,mem_univ x⟩)
    simpa only [continuousOn_univ] using hh
  apply continuousOn_of_dominated (bound:=fun _ ↦ C)
  · intro t ht
    exact ((hqc t ht).measurable.comp_aemeasurable (hXM t ht).aemeasurable).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hb t ht (X t z))
  · exact integrable_const _
  · filter_upwards [hXC] with z hz
    exact hc.comp (continuousOn_id.prodMk hz) (fun t ht ↦ ⟨ht,mem_univ _⟩)

lemma IsDiffusion.weightedObservable_tendsto {W:BrownianSpace} {γ:OrderParameter}
    {X:ℝ → W.Ω → ℝ} (hX:IsDiffusion W γ X) {T C:ℝ} (hT:0<T) (hT1:T<1)
    {η:ℝ → ℝ} (hη:MonotoneOn η (Icc (0:ℝ) T)) (hη0:0≤η 0)
    {Q:ℝ → ℝ → ℝ} (hC:0≤C) {D:ℝ≥0}
    (hc:ContinuousOn (fun p:ℝ×ℝ ↦ Q p.1 p.2) (Icc (0:ℝ) T ×ˢ univ))
    (hb:∀ t∈Icc (0:ℝ) T,∀ x,|Q t x|≤C)
    (hl:∀ t∈Icc (0:ℝ) T,LipschitzWith D (Q t)) :
    Tendsto (fun N ↦ stepSize T N*∑ j:Fin N,η (meshTime T N j)*
      (∫ z,Q (meshTime T N j) (euler T N γ.coeff (gradient W γ) z j) ∂gaussianProduct (Fin (N+1)))) atTop
      (𝓝 (∫ t in (0:ℝ)..T,η t*(∫ z,Q t (X t z) ∂W.μ))) := by
  obtain ⟨Kv,Lv,K,L,D',Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := sourceStripRegularity W γ T ⟨hT.le,hT1⟩
  let E (N:ℕ) := ∫ z,(meshMaxError T X (coupledEuler T γ.coeff (gradient W γ) W.B) N z)^2 ∂W.μ
  let f (t:ℝ) := ∫ z,Q t (X t z) ∂W.μ
  have hXM (t:ℝ) (ht:t∈Icc (0:ℝ) T):MemLp (X t) 2 W.μ := hX.memLp ⟨ht.1,ht.2.trans hT1.le⟩ (by norm_num)
  have hpaths := hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x)
  have hEl:Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence W.brownian.toIsPreBrownianReal
    hT hG hLu hu (fun t ht ↦ (hXM t ht).aestronglyMeasurable) hpaths
  have hEs:Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hEl
  have hf:ContinuousOn f (Icc (0:ℝ) T) := mean_observable_continuous hc hb
    (fun t ht ↦ (hXM t ht).aestronglyMeasurable) (hpaths.mono (fun _ hz ↦ hz.1))
  have hfB (t:ℝ) (ht:t∈Icc (0:ℝ) T):|f t|≤C := by
    simpa only [f,Real.norm_eq_abs,probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ:=W.μ) (C:=C) (f:=fun z ↦ Q t (X t z))
        (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hb t ht (X t z))))
  apply perturbed_monotone_weighted_grid_tendsto (r:=fun N ↦ (D:ℝ)*Real.sqrt (E N)) hT hC hη hη0 hf hfB
    (by simpa only [mul_zero] using hEs.const_mul (D:ℝ))
  filter_upwards [eventually_gt_atTop 0] with N hN j
  exact coupled_lipschitz_expectation_bound W.brownian.toIsPreBrownianReal hT hG hXM
    (hpaths.mono (fun _ hz ↦ hz.2.2)) hN j.isLt.le (hl _ (mesh_time_mem hT.le hN j.isLt.le))
end SKValue

end

end OAI

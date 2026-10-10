import Mathlib
import OAI.Probability.SKValue.Control.StripRegularity
import OAI.Probability.SKValue.Control.PhiRegularity

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma phi_even (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Ico (0 : ℝ) 1) (x : ℝ) : phi W γ t (-x)=phi W γ t x := by
  have hl := (smoothApprox_tendsto W γ).tendsto_at (⟨t,ht⟩,-x)
  have hr := (smoothApprox_tendsto W γ).tendsto_at (⟨t,ht⟩,x)
  exact tendsto_nhds_unique hl (hr.congr (fun n ↦ (smoothApprox_even γ n t x).symm))

lemma phi_gradient_zero (W : BrownianSpace) (γ : OrderParameter) : gradient W γ 0 0=0 :=
  deriv_even_zero (phi_even W γ (by norm_num))

theorem sourceStripRegularity (W : BrownianSpace) (γ : OrderParameter) : SourceStripRegularity W γ := by
  intro T hT
  have h := phi_evolution W γ hT
  have hγ : ∀ t∈Icc (0 : ℝ) T, 0 ≤ γ.coeff t :=
    fun t ht ↦ γ.nonneg _ ⟨ht.1,ht.2.trans_lt hT.2⟩
  have hmono : MonotoneOn γ.coeff (Icc (0 : ℝ) T) :=
    γ.monotone.mono (fun _ ht ↦ ⟨ht.1,ht.2.trans_lt hT.2⟩)
  obtain ⟨Kv,Lv,hV⟩ := h.toValueStrip hT.1 hγ hmono
  obtain ⟨K,L,hG⟩ := h.toGradientStrip hT.1 hγ hmono (phi_gradient_zero W γ)
  obtain ⟨D,hD,hb⟩ := h.bound 1
  obtain ⟨Lu,hLu,hu⟩ := h.jet_joint 0
  obtain ⟨La,hLa,ha⟩ := h.jet_joint 1
  refine ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,?_,?_,?_⟩
  · intro t ht x
    change |deriv (deriv (phi W γ t)) x| ≤ D
    simpa only [iteratedDeriv_one] using hb t ht x
  · intro s hs t ht x y
    simpa only [iteratedDeriv_zero,gradient] using hu s hs t ht y x
  · intro s hs t ht x y
    change |deriv (deriv (phi W γ s)) x-deriv (deriv (phi W γ t)) y| ≤ _
    simpa only [iteratedDeriv_one] using ha s hs t ht y x

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma ValueStrip.drift_one_step {T K L G t δ x z r : ℝ}
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : ValueStrip T γ V K L)
    (ht : 0≤t) (hδ : 0≤δ) (hδ1 : δ≤1) (htδ : t+δ≤T)
    (hG : γ T≤G) (hr : |r|≤G) :
    |V (t+δ) (x+Real.sqrt δ*z+δ*r)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)-
      δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2)| ≤
      δ*Real.sqrt δ*cubicEnvelope G K ((1/2+G)*L) z+
        δ*K*(γ (t+δ)-γ t) := by
  have htT : t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have hT : 0≤T := ht.trans htT
  have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht htδ
  have htm : t∈Icc (0 : ℝ) T := ⟨ht,htT⟩
  have hem : t+δ∈Icc (0 : ℝ) T := ⟨by linarith,htδ⟩
  have hTm : T∈Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hbint (y : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ) :=
    (h.second_integrable y).mono_set (by
      rw [uIcc_of_le (by linarith : t≤t+δ),uIcc_of_le hT]
      exact hsub)
  have hpint (y : ℝ) : IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) y)^2)) volume t (t+δ) :=
    (h.product_integrable y).mono_set (by
      rw [uIcc_of_le (by linarith : t≤t+δ),uIcc_of_le hT]
      exact hsub)
  have hh := value_bounded_drift_one_step (V := V) (γ := γ) (x := x) (z := z)
    hδ hδ1 ((h.gamma_nonneg T hTm).trans hG) h.K_nonneg h.L_nonneg hr
    (h.gamma_mono.mono hsub) (h.gamma_nonneg t htm)
    ((h.gamma_mono htm hTm htT).trans hG) (h.smooth t htm)
    (h.second_bound t htm x) (h.third_bound t htm)
    (fun s hs ↦ h.product_bound s (hsub hs))
    (fun s hs y ↦ h.second_lipschitz t htm s (hsub hs) x y)
    (fun s hs y ↦ h.product_lipschitz t htm s (hsub hs) x y)
    hbint hpint (fun y ↦ h.pde t htm (t+δ) hem y)
  simpa only [add_assoc] using hh

noncomputable def crossFeedback (V U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (deriv (U t) x+deriv (V t) x)/2

lemma crossFeedback_bound {V U : ℝ → ℝ → ℝ} {t x : ℝ}
    (hV : |deriv (V t) x|≤1) (hU : |deriv (U t) x|≤1) :
    |crossFeedback V U t x|≤1 := by
  dsimp [crossFeedback]
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2),div_le_iff₀ (by norm_num : (0 : ℝ)<2)]
  calc |deriv (U t) x+deriv (V t) x| ≤ |deriv (U t) x|+|deriv (V t) x| := abs_add_le _ _
    _ ≤ 1*2 := by linarith

lemma cross_generator_identity (β γ p q : ℝ) :
    (q*(β*((q+p)/2))-(1/2 : ℝ)*β*q^2)-
      (p*(β*((q+p)/2))-(1/2 : ℝ)*γ*p^2) = -(1/2 : ℝ)*(β-γ)*p^2 := by ring

lemma cross_value_one_step {T K L K' L' G t δ x z : ℝ}
    {γ β : ℝ → ℝ} {V U : ℝ → ℝ → ℝ}
    (hV : ValueStrip T γ V K L) (hU : ValueStrip T β U K' L')
    (ht : 0≤t) (hδ : 0≤δ) (hδ1 : δ≤1) (htδ : t+δ≤T)
    (hG : γ T≤G) (hG' : β T≤G) :
    let y := x+Real.sqrt δ*z+δ*(β t*crossFeedback V U t x)
    |(U (t+δ) y-V (t+δ) y)-(U t x-V t x)-
      (deriv (U t) x-deriv (V t) x)*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*(deriv (deriv (U t)) x-deriv (deriv (V t)) x)*(z^2-1)+
      (δ/2)*(β t-γ t)*(deriv (V t) x)^2| ≤
      δ*Real.sqrt δ*(cubicEnvelope G K ((1/2+G)*L) z+
        cubicEnvelope G K' ((1/2+G)*L') z)+
      δ*K*(γ (t+δ)-γ t)+δ*K'*(β (t+δ)-β t) := by
  have htT : t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have htm : t∈Icc (0 : ℝ) T := ⟨ht,htT⟩
  have hβ : 0≤β t := hU.gamma_nonneg t htm
  have hr : |β t*crossFeedback V U t x|≤G := by
    rw [abs_mul,abs_of_nonneg hβ]
    calc β t*|crossFeedback V U t x| ≤ β t*1 :=
        mul_le_mul_of_nonneg_left (crossFeedback_bound (hV.bounded _ htm _) (hU.bounded _ htm _)) hβ
      _ ≤ G := by simpa only [mul_one] using (hU.gamma_mono htm ⟨ht.trans htT,le_rfl⟩ htT).trans hG'
  have hv := hV.drift_one_step (x := x) (z := z) ht hδ hδ1 htδ hG hr
  have hu := hU.drift_one_step (x := x) (z := z) ht hδ hδ1 htδ hG' hr
  dsimp only
  have hab (a b : ℝ) : |a-b|≤|a|+|b| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le a 0 b
  convert (hab _ _).trans (add_le_add hu hv) using 1 <;>
    try dsimp only [crossFeedback]
  all_goals ring_nf

end SKValue

end

end OAI

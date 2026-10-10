import OAI.Analysis.LienardCycles.ProfileDerivatives

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuinticFit
open ScaledProfile PartialCalculus QuadraticCoordinates
noncomputable def M (a : Fin 6 → ℝ) : ℝ × ℝ → ℝ := PositiveTransport.M (QuinticProfile.profile a) 0
noncomputable def V (a : Fin 6 → ℝ) : ℝ × ℝ → ℝ := PositiveTransport.v (QuinticProfile.profile a) 0
lemma M_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (M a) (h,r) :=
  PositiveTransport.M_analytic _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr
lemma V_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (V a) (h,r) :=
  PositiveTransport.v_analytic _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr
lemma M_abs_lt (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : |M a (h,r)|<r :=
  PositiveTransport.M_abs_lt _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr
lemma V_abs_lt (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : |V a (h,r)|<1 :=
  PositiveTransport.v_abs_lt _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr
lemma n_eq_V (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    PositiveFit.n (QuinticProfile.profile a) h (0,r)=V a (h,r) :=
  (PositiveFit.m_hasDerivAt _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr).unique
    (second_hasDerivAt ((M_analytic a hh hr).differentiableAt (by simp)))
lemma fit_eq (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    lambda a (h,r)=QuadraticFit.fitD ((r,M a (h,r)),V a (h,r)) ∧
    kappa a (h,r)=QuadraticFit.fitK ((r,M a (h,r)),V a (h,r)) := by
  simp only [lambda,kappa,PositiveFit.d,PositiveFit.k,n_eq_V a hh hr]
  exact ⟨rfl,rfl⟩
lemma lambda_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (lambda a) (h,r) := by
  have ha := (QuadraticFit.fitD_analytic hr (M_abs_lt a hh hr) (V_abs_lt a hh hr)).comp (h,r)
    ((contDiffAt_snd.prodMk (M_analytic a hh hr)).prodMk (V_analytic a hh hr))
  apply ha.congr_of_eventuallyEq
  filter_upwards [continuousAt_const.eventually_lt continuousAt_fst hh,
    continuousAt_const.eventually_lt continuousAt_snd hr] with q hq hrq
  exact (fit_eq a hq hrq).1
lemma kappa_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (kappa a) (h,r) := by
  have ha := (QuadraticFit.fitK_analytic hr (M_abs_lt a hh hr) (V_abs_lt a hh hr)).comp (h,r)
    ((contDiffAt_snd.prodMk (M_analytic a hh hr)).prodMk (V_analytic a hh hr))
  apply ha.congr_of_eventuallyEq
  filter_upwards [continuousAt_const.eventually_lt continuousAt_fst hh,
    continuousAt_const.eventually_lt continuousAt_snd hr] with q hq hrq
  exact (fit_eq a hq hrq).2
noncomputable def fit (a : Fin 6 → ℝ) (q : ℝ × ℝ) : (ℝ × ℝ) × ℝ := ((lambda a q,kappa a q),q.2)
lemma spec (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    H (fit a (h,r))=M a (h,r) ∧ Hr (fit a (h,r))=V a (h,r) := by
  dsimp only [fit]
  rw [(fit_eq a hh hr).1,(fit_eq a hh hr).2]
  exact QuadraticFit.fit_spec hr (M_abs_lt a hh hr) (V_abs_lt a hh hr)
lemma model_pull_derivatives {f : (ℝ × ℝ) × ℝ → ℝ} {X L K : ℝ × ℝ → ℝ} {h r : ℝ}
    (hf : DifferentiableAt ℝ f ((L (h,r),K (h,r)),r))
    (hX : DifferentiableAt ℝ X (h,r)) (hL : DifferentiableAt ℝ L (h,r)) (hK : DifferentiableAt ℝ K (h,r))
    (he : ∀ᶠ q in 𝓝 (h,r), X q=f ((L q,K q),q.2)) :
    first X (h,r)=first L (h,r)*direction ((1,0),0) f ((L (h,r),K (h,r)),r)+
      first K (h,r)*direction ((0,1),0) f ((L (h,r),K (h,r)),r) ∧
    second X (h,r)=second L (h,r)*direction ((1,0),0) f ((L (h,r),K (h,r)),r)+
      second K (h,r)*direction ((0,1),0) f ((L (h,r),K (h,r)),r)+
      direction ((0,0),1) f ((L (h,r),K (h,r)),r) := by
  have hd₁ := hf.hasFDerivAt.comp_hasDerivAt h
    (((first_hasDerivAt hL).prodMk (first_hasDerivAt hK)).prodMk (hasDerivAt_const h r))
  have hd₂ := hf.hasFDerivAt.comp_hasDerivAt r (f := fun s => ((L (h,s),K (h,s)),s))
    (((second_hasDerivAt hL).prodMk (second_hasDerivAt hK)).prodMk (hasDerivAt_id r))
  rw [fderiv_model] at hd₁ hd₂
  simp only [zero_mul,add_zero,one_mul] at hd₁ hd₂
  exact ⟨(first_hasDerivAt hX).unique (hd₁.congr_of_eventuallyEq
    ((continuousAt_id.prodMk continuousAt_const).eventually he)),
    (second_hasDerivAt hX).unique (hd₂.congr_of_eventuallyEq
    ((continuousAt_const.prodMk continuousAt_id).eventually he))⟩
lemma chain_M (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    first (M a) (h,r)=first (lambda a) (h,r)*P (fit a (h,r))+first (kappa a) (h,r)*Q (fit a (h,r)) ∧
    V a (h,r)=second (lambda a) (h,r)*P (fit a (h,r))+second (kappa a) (h,r)*Q (fit a (h,r))+Hr (fit a (h,r)) := by
  apply model_pull_derivatives ((H_analytic hr).differentiableAt (by simp))
    ((M_analytic a hh hr).differentiableAt (by simp)) ((lambda_analytic a hh hr).differentiableAt (by simp))
    ((kappa_analytic a hh hr).differentiableAt (by simp))
  filter_upwards [continuousAt_const.eventually_lt continuousAt_fst hh,
    continuousAt_const.eventually_lt continuousAt_snd hr] with q hq hrq
  exact (spec a hq hrq).1.symm
lemma Hr_d_direction {d k r : ℝ} (hr : 0<r) : direction ((1,0),0) Hr ((d,k),r)=R ((d,k),r) :=
  direction_comm (H_analytic hr) _ _
lemma Hr_k_direction {d k r : ℝ} (hr : 0<r) : direction ((0,1),0) Hr ((d,k),r)=S ((d,k),r) :=
  direction_comm (H_analytic hr) _ _
lemma chain_V (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    first (V a) (h,r)=first (lambda a) (h,r)*R (fit a (h,r))+first (kappa a) (h,r)*S (fit a (h,r)) ∧
    second (V a) (h,r)=second (lambda a) (h,r)*R (fit a (h,r))+second (kappa a) (h,r)*S (fit a (h,r))+Hrr (fit a (h,r)) := by
  have he := model_pull_derivatives ((Hr_analytic (d:=lambda a (h,r)) (k:=kappa a (h,r)) hr).differentiableAt (by simp))
    ((V_analytic a hh hr).differentiableAt (by simp)) ((lambda_analytic a hh hr).differentiableAt (by simp))
    ((kappa_analytic a hh hr).differentiableAt (by simp)) (by
      filter_upwards [continuousAt_const.eventually_lt continuousAt_fst hh,
        continuousAt_const.eventually_lt continuousAt_snd hr] with q hq hrq
      exact (spec a hq hrq).2.symm)
  rw [Hr_d_direction hr,Hr_k_direction hr] at he
  exact he
noncomputable def α (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ := q.2/(q.2^2-M a q^2)
noncomputable def D (a : Fin 6 → ℝ) (f : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := first f q-α a q*second f q
lemma fit_transport (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    P (fit a (h,r))*second (lambda a) (h,r)+Q (fit a (h,r))*second (kappa a) (h,r)=0 ∧
    D a (kappa a) (h,r)= -R (fit a (h,r))/G (fit a (h,r))*(lambda a (h,r)-slope a h) ∧
    D a (lambda a) (h,r)-kappa a (h,r)= S (fit a (h,r))/G (fit a (h,r))*(lambda a (h,r)-slope a h) := by
  have hs := spec a hh hr
  have hm := chain_M a hh hr
  have hv := chain_V a hh hr
  have ht := PositiveTransport.transport_midpoint (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have htv := PositiveTransport.transport_v (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have hder : deriv (fun u => QuinticProfile.profile a (0,u)) h=slope a h := (profile_hasDerivAt a hh).deriv
  rw [hder] at ht
  change first (M a) (h,r)-α a (h,r)*V a (h,r)=M a (h,r)/(r^2-M a (h,r)^2)-slope a h at ht
  change first (V a) (h,r)-α a (h,r)*second (V a) (h,r)= -2*M a (h,r)*r*(1-V a (h,r)^2)/(r^2-M a (h,r)^2)^2 at htv
  have hb := transport_H (d:=lambda a (h,r)) (k:=kappa a (h,r)) hr
  have hbv := transport_Hr (d:=lambda a (h,r)) (k:=kappa a (h,r)) hr
  change kappa a (h,r)*P (fit a (h,r))-alpha (fit a (h,r))*Hr (fit a (h,r)) = _ at hb
  change kappa a (h,r)*R (fit a (h,r))-alpha (fit a (h,r))*Hrr (fit a (h,r)) = _ at hbv
  have hal : alpha (fit a (h,r))=α a (h,r) := by dsimp only [alpha,gap]; rw [hs.1]; rfl
  have hg : gap (fit a (h,r))=r^2-M a (h,r)^2 := by dsimp only [gap]; rw [hs.1]; rfl
  change _ = H (fit a (h,r))/gap (fit a (h,r))-lambda a (h,r) at hb
  change _ = -2*H (fit a (h,r))*r*(1-Hr (fit a (h,r))^2)/gap (fit a (h,r))^2 at hbv
  rw [hal,hg,hs.1,hs.2] at hb
  rw [hal,hg,hs.1,hs.2] at hbv
  have h₁ : P (fit a (h,r))*(D a (lambda a) (h,r)-kappa a (h,r))+Q (fit a (h,r))*D a (kappa a) (h,r)=lambda a (h,r)-slope a h := by
    dsimp only [D]
    linear_combination -hm.1 + ht - hb + α a (h,r)*hm.2 + α a (h,r)*hs.2
  have h₂ : R (fit a (h,r))*(D a (lambda a) (h,r)-kappa a (h,r))+S (fit a (h,r))*D a (kappa a) (h,r)=0 := by
    dsimp only [D]
    linear_combination -hv.1 + htv - hbv + α a (h,r)*hv.2
  have hG : G (fit a (h,r))≠0 := (G_pos hr).ne'
  refine ⟨?_,?_,?_⟩
  · linear_combination -hs.2 - hm.2
  · rw [div_mul_eq_mul_div]
    apply (eq_div_iff hG).mpr
    dsimp only [G]
    linear_combination P (fit a (h,r))*h₂-R (fit a (h,r))*h₁
  · rw [div_mul_eq_mul_div]
    apply (eq_div_iff hG).mpr
    dsimp only [G]
    linear_combination S (fit a (h,r))*h₁-Q (fit a (h,r))*h₂
end QuinticLienard.QuinticFit

end OAI

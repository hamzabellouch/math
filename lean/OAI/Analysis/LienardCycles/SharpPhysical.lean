import OAI.Analysis.LienardCycles.SharpReturn

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology NNReal
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard.Sharpness
open GlobalODE PartialCalculus
noncomputable def F (ε : ℝ) : Polynomial ℝ := Polynomial.C ε *
  (Polynomial.C 4*Polynomial.X-Polynomial.C (20/3)*Polynomial.X^3+Polynomial.C (8/5)*Polynomial.X^5)
lemma F_eval (ε x : ℝ) : (F ε).eval x=ε*f x := by simp [F,f]
@[simp] lemma F_zero (ε : ℝ) : (F ε).eval 0=0 := by simp [F_eval,f]
lemma F_degree (ε : ℝ) : (F ε).degree≤5 := by unfold F;compute_degree
noncomputable def project : Space →L[ℝ] Plane := (ContinuousLinearMap.fst ℝ Plane ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Plane × ℝ))
lemma eps_deriv {z : ℝ → Space} {t : ℝ} (hz : HasDerivAt z (V (z t)) t) :
    HasDerivAt (fun u=>(z u).1) 0 t := by
  simpa [V] using! (ContinuousLinearMap.fst ℝ ℝ (Plane × ℝ)).hasFDerivAt.comp_hasDerivAt t hz
lemma xy_deriv {z : ℝ → Space} {t ε : ℝ} (hz : HasDerivAt z (V (z t)) t) (he : (z t).1=ε) :
    HasDerivAt (fun u=>(z u).2.1) (vectorField (F ε) (z t).2.1) t := by
  simpa [project,V,vectorField,F_eval,he] using! project.hasFDerivAt.comp_hasDerivAt t hz
lemma q_deriv {z : ℝ → Space} {t : ℝ} (hz : HasDerivAt z (V (z t)) t) :
    HasDerivAt (fun u=>(z u).2.2) (-(z t).2.1.1*f (z t).2.1.1) t := by
  let pr : Space →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ Plane ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Plane × ℝ))
  simpa [pr,V] using! pr.hasFDerivAt.comp_hasDerivAt t hz
lemma eps_constant {z : ℝ → Space} {p : ℝ × ℝ} {T : ℝ} (hT : 0≤T)
    (hc : ContinuousOn z (Icc 0 T)) (hz : ∀ t ∈ Icc 0 T,HasDerivAt z (V (z t)) t)
    (h0 : z 0=initial p) : ∀ t ∈ Icc 0 T,(z t).1=p.1 := by
  apply eq_of_hasDerivAt_eq_on_Icc hc.fst continuousOn_const (fun t ht=>eps_deriv (hz t ht))
    (fun t _=>hasDerivAt_const t p.1) ⟨le_rfl,hT⟩
  simp [h0,initial]
lemma energy_identity {z : ℝ → Space} {p : ℝ × ℝ} {T : ℝ} (hT : 0≤T)
    (hc : ContinuousOn z (Icc 0 T)) (hz : ∀ t ∈ Icc 0 T,HasDerivAt z (V (z t)) t)
    (h0 : z 0=initial p) : ((z T).2.1.1^2+(z T).2.1.2^2-p.2^2)/2=p.1*(z T).2.2 := by
  have he := eps_constant hT hc hz h0
  let E : ℝ → ℝ := fun t=>((z t).2.1.1^2+(z t).2.1.2^2)/2
  let Q : ℝ → ℝ := fun t=>p.1*(z t).2.2+p.2^2/2
  have hEd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt E (p.1*(-(z t).2.1.1*f (z t).2.1.1)) t := by
    have hxy := xy_deriv (hz t ht) (he t ht)
    have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hxy
    have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hxy
    have H := ((hx.pow 2).add (hy.pow 2)).div_const 2
    convert! H using 1
    simp [vectorField,F_eval]
    ring
  have hQd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt Q (p.1*(-(z t).2.1.1*f (z t).2.1.1)) t := by
    exact ((q_deriv (hz t ht)).const_mul p.1).add_const _
  have hEq := eq_of_hasDerivAt_eq_on_Icc (f:=E) (g:=Q)
    (by dsimp [E];fun_prop) (by dsimp [Q];fun_prop) hEd hQd ⟨le_rfl,hT⟩
    (by simp [E,Q,h0,initial]) (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩)
  dsimp [E,Q] at hEq
  linarith
lemma ReturnFamily.physical_deriv (R : ReturnFamily) {p : ℝ × ℝ} {T : ℝ} (hT : 0≤T)
    (hfaith : ∀ t ∈ Icc 0 T,R.W (R.path p t)=V (R.path p t)) :
    ∀ t ∈ Icc 0 T,HasDerivAt (fun u=>(R.path p u).2.1) (vectorField (F p.1) (R.path p t).2.1) t := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt (R.path p) (V (R.path p t)) t := by rw [←hfaith t ht];exact R.deriv p t
  have hc : Continuous (R.path p) := R.continuous.comp (continuous_const.prodMk continuous_id)
  have he := eps_constant hT hc.continuousOn hd (R.path_zero p)
  exact fun t ht=>xy_deriv (hd t ht) (he t ht)
lemma ReturnFamily.closed_of_Q (R : ReturnFamily) {p : ℝ × ℝ}
    (hT : 0<R.σ p) (hs : 0<p.2) (hx : (R.path p (R.σ p)).2.1.1=0)
    (hy : 0<(R.path p (R.σ p)).2.1.2)
    (hfaith : ∀ t ∈ Icc 0 (R.σ p),R.W (R.path p t)=V (R.path p t))
    (hQ : R.Q p=0) : R.path p (R.σ p)=initial p := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 (R.σ p)) : HasDerivAt (R.path p) (V (R.path p t)) t := by rw [←hfaith t ht];exact R.deriv p t
  have hc : Continuous (R.path p) := R.continuous.comp (continuous_const.prodMk continuous_id)
  have he := eps_constant hT.le hc.continuousOn hd (R.path_zero p) (R.σ p) ⟨hT.le,le_rfl⟩
  have henergy := energy_identity hT.le hc.continuousOn hd (R.path_zero p)
  change (R.path p (R.σ p)).2.2=0 at hQ
  rw [hx,hQ] at henergy
  have hyEq : (R.path p (R.σ p)).2.1.2=p.2 := by nlinarith
  exact Prod.ext he (Prod.ext (Prod.ext hx hyEq) hQ)
lemma ReturnFamily.periodic_orbit (R : ReturnFamily) {p : ℝ × ℝ}
    (hT : 0<R.σ p) (hs : 0<p.2)
    (hfaith : ∀ t ∈ Icc 0 (R.σ p),R.W (R.path p t)=V (R.path p t))
    (hclosed : R.path p (R.σ p)=initial p) :
    IsPeriodicOrbit (F p.1) (range (fun t=>(R.path p t).2.1)) := by
  have hp : Function.Periodic (R.path p) (R.σ p) := flow_periodic_of_hit R.W R.lip R.bound hclosed
  let z : ℝ → Plane := fun t=>(R.path p t).2.1
  have hc : Continuous (R.path p) := R.continuous.comp (continuous_const.prodMk continuous_id)
  have hd (t : ℝ) (ht : t ∈ Icc 0 (R.σ p)) : HasDerivAt (R.path p) (V (R.path p t)) t := by rw [←hfaith t ht];exact R.deriv p t
  have he := eps_constant hT.le hc.continuousOn hd (R.path_zero p)
  have hsol : IsSolution (F p.1) z := by
    intro t
    have him : R.path p t ∈ R.path p '' Icc 0 (R.σ p) := by
      rw [show Icc 0 (R.σ p)=Icc 0 (0+R.σ p) by simp,hp.image_Icc hT 0]
      exact mem_range_self t
    obtain ⟨u,hu,heq⟩ := him
    have hw : R.W (R.path p t)=V (R.path p t) := by rw [←heq];exact hfaith u hu
    have het : (R.path p t).1=p.1 := by rw [←heq];exact he u hu
    exact xy_deriv (hw ▸ R.deriv p t) het
  have hz0 : z 0=(0,p.2) := by simp [z,initial]
  have hnon : ∃ u v,z u≠z v := by
    by_contra hn
    push Not at hn
    have hzc : z=(fun _=>(0,p.2)) := funext (fun t=>(hn t 0).trans hz0)
    have H := hsol.x_deriv 0
    rw [hzc] at H
    have hs0 : p.2=0 := by simpa using H.unique (hasDerivAt_const 0 (0:ℝ))
    exact (ne_of_gt hs) hs0
  exact ⟨z,R.σ p,hsol,hT,(fun t=>congrArg (fun v : Space=>v.2.1) (hp t)),hnon,rfl⟩
end QuinticLienard.Sharpness

end OAI

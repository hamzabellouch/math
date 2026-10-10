import OAI.Analysis.LienardCycles.EndpointSigns

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus ModelEndpoint
noncomputable def ar := direction ((0,0),1) alpha
noncomputable def arr := direction ((0,0),1) ar
noncomputable def transport (f : (ℝ × ℝ) × ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  q.1.2*direction ((1,0),0) f q-alpha q*direction ((0,0),1) f q
lemma alpha_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω alpha ((d,k),r) := by
  unfold alpha gap
  have hH := H_analytic (d := d) (k := k) hr
  fun_prop (disch := exact ne_of_gt (H_gap_pos hr))
lemma ar_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω ar ((d,k),r) :=
  direction_contDiffAt (alpha_analytic hr) _
lemma ar_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => alpha ((d,k),s)) (ar ((d,k),r)) r :=
  slice_r ((alpha_analytic hr).differentiableAt (by simp))
lemma arr_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => ar ((d,k),s)) (arr ((d,k),r)) r :=
  slice_r ((ar_analytic hr).differentiableAt (by simp))
lemma Rr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Rr ((d,k),r) :=
  direction_contDiffAt (R_analytic hr) _
lemma Sr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Sr ((d,k),r) :=
  direction_contDiffAt (S_analytic hr) _
lemma W_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω W ((d,k),r) :=
  ((R_analytic hr).mul (Sr_analytic hr)).sub ((S_analytic hr).mul (Rr_analytic hr))

lemma transport_P {d k r : ℝ} (hr : 0 < r) :
    transport P ((d,k),r)=gamma ((d,k),r)*P ((d,k),r)-1 := by
  have hp := slice_d ((P_analytic (d := d) (k := k) hr).differentiableAt (by simp))
  have hH := P_hasDerivAt (d := d) (k := k) hr
  have hg := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  have ht := (((Hr_d_hasDerivAt (d := d) (k := k) hr).const_mul r).add hH).div
    ((hasDerivAt_const d (r^2)).sub (hH.pow 2)) hg
  have he : (fun s => k*P ((s,k),r)+s) =ᶠ[𝓝 d]
      (fun s => (r*Hr ((s,k),r)+H ((s,k),r))/(r^2-(H ((s,k),r))^2)) :=
    Eventually.of_forall (fun s => width_identity (d := s) (k := k) hr)
  have hh := ((hp.const_mul k).add (hasDerivAt_id d)).unique (ht.congr_of_eventuallyEq he)
  dsimp [transport,alpha,gamma,gap]
  change k*direction ((1,0),0) P ((d,k),r)-r/(r^2-H ((d,k),r)^2)*R ((d,k),r)=_
  dsimp at hh
  norm_num only [Nat.cast_ofNat, show 2-1=1 from rfl, pow_one] at hh
  field_simp [hg] at hh ⊢
  nlinarith only [hh]

lemma transport_Q {d k r : ℝ} (hr : 0 < r) :
    transport Q ((d,k),r)=gamma ((d,k),r)*Q ((d,k),r)-P ((d,k),r) := by
  have hp := slice_k ((P_analytic (d := d) (k := k) hr).differentiableAt (by simp))
  have hH := Q_hasDerivAt (d := d) (k := k) hr
  have hg := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  have ht := (((Hr_k_hasDerivAt (d := d) (k := k) hr).const_mul r).add hH).div
    ((hasDerivAt_const k (r^2)).sub (hH.pow 2)) hg
  have he : (fun s => s*P ((d,s),r)+d) =ᶠ[𝓝 k]
      (fun s => (r*Hr ((d,s),r)+H ((d,s),r))/(r^2-(H ((d,s),r))^2)) :=
    Eventually.of_forall (fun s => width_identity (d := d) (k := s) hr)
  have hh := (((hasDerivAt_id k).mul hp).add_const d).unique (ht.congr_of_eventuallyEq he)
  have hc : direction ((0,1),0) P ((d,k),r)=direction ((1,0),0) Q ((d,k),r) :=
    direction_comm (H_analytic hr) _ _
  rw [hc] at hh
  dsimp [transport,alpha,gamma,gap]
  change k*direction ((1,0),0) Q ((d,k),r)-r/(r^2-H ((d,k),r)^2)*S ((d,k),r)=_
  dsimp at hh
  norm_num only [Nat.cast_ofNat, show 2-1=1 from rfl, pow_one] at hh
  field_simp [hg] at hh ⊢
  nlinarith only [hh]

lemma transport_deriv {f : (ℝ × ℝ) × ℝ → ℝ} {d k r : ℝ} (hr : 0 < r)
    (hf : ContDiffAt ℝ ω f ((d,k),r)) :
    HasDerivAt (fun s => transport f ((d,k),s))
      (transport (direction ((0,0),1) f) ((d,k),r)-ar ((d,k),r)*direction ((0,0),1) f ((d,k),r)) r := by
  have hfd := direction_contDiffAt hf (((1,0),0) : (ℝ × ℝ) × ℝ)
  have hfr := direction_contDiffAt hf (((0,0),1) : (ℝ × ℝ) × ℝ)
  have hd := ((slice_r (hfd.differentiableAt (by simp))).const_mul k).sub
    ((ar_deriv (d := d) (k := k) hr).mul (slice_r (hfr.differentiableAt (by simp))))
  have hc := direction_comm hf (((0,0),1) : (ℝ × ℝ) × ℝ) (((1,0),0) : (ℝ × ℝ) × ℝ)
  convert! hd using 1
  dsimp [transport]
  rw [hc]
  ring

lemma transport_R {d k r : ℝ} (hr : 0 < r) :
    transport R ((d,k),r)=(gamma ((d,k),r)+ar ((d,k),r))*R ((d,k),r)+gr ((d,k),r)*P ((d,k),r) := by
  have hh := (transport_deriv hr (P_analytic (d := d) (k := k) hr)).unique
    ((((gr_deriv hr).mul (R_hasDerivAt hr)).sub_const 1).congr_of_eventuallyEq
      ((eventually_gt_nhds hr).mono (fun s hs => transport_P (d := d) (k := k) hs)))
  change transport R ((d,k),r)-ar ((d,k),r)*R ((d,k),r)=_ at hh
  nlinarith only [hh]
lemma transport_S {d k r : ℝ} (hr : 0 < r) :
    transport S ((d,k),r)=(gamma ((d,k),r)+ar ((d,k),r))*S ((d,k),r)+gr ((d,k),r)*Q ((d,k),r)-R ((d,k),r) := by
  have hh := (transport_deriv hr (Q_analytic (d := d) (k := k) hr)).unique
    ((((gr_deriv hr).mul (S_hasDerivAt hr)).sub (R_hasDerivAt hr)).congr_of_eventuallyEq
      ((eventually_gt_nhds hr).mono (fun s hs => transport_Q (d := d) (k := k) hs)))
  change transport S ((d,k),r)-ar ((d,k),r)*S ((d,k),r)=_ at hh
  nlinarith only [hh]
lemma transport_Rr {d k r : ℝ} (hr : 0 < r) :
    transport Rr ((d,k),r)=(gamma ((d,k),r)+2*ar ((d,k),r))*Rr ((d,k),r)+
      (2*gr ((d,k),r)+arr ((d,k),r))*R ((d,k),r)+grr ((d,k),r)*P ((d,k),r) := by
  have hh := (transport_deriv hr (R_analytic (d := d) (k := k) hr)).unique
    (((((gr_deriv hr).add (arr_deriv hr)).mul (Rr_hasDerivAt hr)).add
      ((grr_deriv hr).mul (R_hasDerivAt hr))).congr_of_eventuallyEq
      ((eventually_gt_nhds hr).mono (fun s hs => transport_R (d := d) (k := k) hs)))
  change transport Rr ((d,k),r)-ar ((d,k),r)*Rr ((d,k),r)=_ at hh
  dsimp at hh
  nlinarith only [hh]
lemma transport_Sr {d k r : ℝ} (hr : 0 < r) :
    transport Sr ((d,k),r)=(gamma ((d,k),r)+2*ar ((d,k),r))*Sr ((d,k),r)+
      (2*gr ((d,k),r)+arr ((d,k),r))*S ((d,k),r)+grr ((d,k),r)*Q ((d,k),r)-Rr ((d,k),r) := by
  have hh := (transport_deriv hr (S_analytic (d := d) (k := k) hr)).unique
    ((((((gr_deriv hr).add (arr_deriv hr)).mul (Sr_hasDerivAt hr)).add
      ((grr_deriv hr).mul (S_hasDerivAt hr))).sub (Rr_hasDerivAt hr)).congr_of_eventuallyEq
      ((eventually_gt_nhds hr).mono (fun s hs => transport_S (d := d) (k := k) hs)))
  change transport Sr ((d,k),r)-ar ((d,k),r)*Sr ((d,k),r)=_ at hh
  dsimp at hh
  nlinarith only [hh]

lemma direction_mul_sub {f g h j : (ℝ × ℝ) × ℝ → ℝ} {q : (ℝ × ℝ) × ℝ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q)
    (hh : DifferentiableAt ℝ h q) (hj : DifferentiableAt ℝ j q) (v : (ℝ × ℝ) × ℝ) :
    direction v (fun q => f q*g q-h q*j q) q=
      direction v f q*g q+f q*direction v g q-direction v h q*j q-h q*direction v j q := by
  change (fderiv ℝ (f*g-h*j) q) v=_
  rw [fderiv_sub (hf.mul hg) (hh.mul hj),fderiv_mul hf hg,fderiv_mul hh hj]
  dsimp only [direction]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul]
  ring

lemma transport_W {d k r : ℝ} (hr : 0 < r) :
    transport W ((d,k),r)=(2*gamma ((d,k),r)+3*ar ((d,k),r))*W ((d,k),r)+
      gr ((d,k),r)*(P ((d,k),r)*Sr ((d,k),r)-Q ((d,k),r)*Rr ((d,k),r))-
      grr ((d,k),r)*G ((d,k),r) := by
  have hR := (R_analytic (d := d) (k := k) hr).differentiableAt (by simp)
  have hS := (S_analytic (d := d) (k := k) hr).differentiableAt (by simp)
  have hRr := (Rr_analytic (d := d) (k := k) hr).differentiableAt (by simp)
  have hSr := (Sr_analytic (d := d) (k := k) hr).differentiableAt (by simp)
  have he : transport W ((d,k),r)=transport R ((d,k),r)*Sr ((d,k),r)+R ((d,k),r)*transport Sr ((d,k),r)-
      transport S ((d,k),r)*Rr ((d,k),r)-S ((d,k),r)*transport Rr ((d,k),r) := by
    dsimp only [transport]
    rw [show W = (fun q => R q*Sr q-S q*Rr q) from rfl]
    rw [direction_mul_sub hR hSr hS hRr,direction_mul_sub hR hSr hS hRr]
    ring
  rw [he,transport_R hr,transport_S hr,transport_Rr hr,transport_Sr hr]
  dsimp [W,G]
  ring
end QuinticLienard.QuadraticCoordinates

end OAI

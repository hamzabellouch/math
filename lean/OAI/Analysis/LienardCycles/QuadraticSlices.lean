import OAI.Analysis.LienardCycles.EndpointComparison

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open ScalarArcs CanonicalVariation PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus

lemma fderiv_model (f : (ℝ × ℝ) × ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) (a b c : ℝ) :
    fderiv ℝ f q ((a,b),c) = a*direction ((1,0),0) f q+
      b*direction ((0,1),0) f q+c*direction ((0,0),1) f q := by
  have he : ((a,b),c) = a • (((1,0),0) : (ℝ × ℝ) × ℝ)+
      b • (((0,1),0) : (ℝ × ℝ) × ℝ)+c • (((0,0),1) : (ℝ × ℝ) × ℝ) := by
    ext <;> simp
  rw [he,map_add,map_add,map_smul,map_smul,map_smul]
  rfl

lemma slice_d {f : (ℝ × ℝ) × ℝ → ℝ} {d k r : ℝ}
    (hf : DifferentiableAt ℝ f ((d,k),r)) :
    HasDerivAt (fun s => f ((s,k),r)) (direction ((1,0),0) f ((d,k),r)) d := by
  simpa [direction] using! hf.hasFDerivAt.comp_hasDerivAt d
    (((hasDerivAt_id d).prodMk (hasDerivAt_const d k)).prodMk (hasDerivAt_const d r))
lemma slice_k {f : (ℝ × ℝ) × ℝ → ℝ} {d k r : ℝ}
    (hf : DifferentiableAt ℝ f ((d,k),r)) :
    HasDerivAt (fun s => f ((d,s),r)) (direction ((0,1),0) f ((d,k),r)) k := by
  simpa [direction] using! hf.hasFDerivAt.comp_hasDerivAt k
    (((hasDerivAt_const k d).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))

lemma v_translation (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    v profile (d,k) (h,r) = Hr ((d+k*h,k),r) := by
  have he : (fun s => M profile (d,k) (h,s)) =ᶠ[𝓝 r]
      (fun s => H ((d+k*h,k),s)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact translation d k h hs
  exact (second_hasDerivAt ((M_analytic profile profile_contDiff model_local_flow
    (p := (d,k)) (h := h) hr).differentiableAt (by simp))).unique
      ((Hr_hasDerivAt hr).congr_of_eventuallyEq he)

lemma height_derivative (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    first (M profile (d,k)) (h,r) = k*P ((d+k*h,k),r) := by
  have he : (fun s => M profile (d,k) (s,r)) =
      (fun s => H ((d+k*s,k),r)) := funext (fun s => translation d k s hr)
  have hd := (P_hasDerivAt (d := d+k*h) (k := k) hr).comp h
    (((hasDerivAt_id h).const_mul k).const_add d)
  have hh := (first_hasDerivAt ((M_analytic profile profile_contDiff model_local_flow
    (p := (d,k)) (h := h) hr).differentiableAt (by simp))).unique
      (hd.congr_of_eventuallyEq (Eventually.of_forall (fun s => congrFun he s)))
  simpa only [mul_one,mul_comm] using hh

noncomputable def gap (q : (ℝ × ℝ) × ℝ) : ℝ := q.2^2-(H q)^2
noncomputable def alpha (q : (ℝ × ℝ) × ℝ) : ℝ := q.2/gap q
noncomputable def gamma (q : (ℝ × ℝ) × ℝ) : ℝ :=
  (q.2^2+(H q)^2+2*q.2*H q*Hr q)/(gap q)^2

lemma width_identity {d k r : ℝ} (hr : 0 < r) :
    k*P ((d,k),r)+d=(r*Hr ((d,k),r)+H ((d,k),r))/gap ((d,k),r) := by
  have ht := transport_midpoint profile profile_contDiff model_local_flow
    (p := (d,k)) (h := 0) hr
  rw [height_derivative d k 0 hr,translation d k 0 hr,v_translation d k 0 hr] at ht
  have hder : deriv (fun u => profile ((d,k),u)) 0=d := by
    have hh := (((hasDerivAt_id (0:ℝ)).const_mul d).add
      (((hasDerivAt_id (0:ℝ)).pow 2).const_mul (k/2))).deriv
    simpa [profile] using! hh
  simp only [mul_zero,add_zero,hder] at ht
  dsimp [gap]
  have hg := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  field_simp [hg] at ht ⊢
  nlinarith [ht]

lemma transport_H {d k r : ℝ} (hr : 0 < r) :
    k*P ((d,k),r)-alpha ((d,k),r)*Hr ((d,k),r) = H ((d,k),r)/gap ((d,k),r)-d := by
  have ht := width_identity (d := d) (k := k) hr
  dsimp [alpha]
  rw [add_div,mul_div_assoc] at ht
  linear_combination ht

lemma euler_identity {d k r : ℝ} (hr : 0 < r) :
    r*Hr ((d,k),r)-H ((d,k),r)=d*P ((d,k),r)+3*k*Q ((d,k),r) := by
  have hm : HasDerivAt (fun s : ℝ => ((d*s,k*s^3),(1:ℝ)))
      ((d,3*k*r^2),0) r := by
    convert! (((hasDerivAt_id r).const_mul d).prodMk
      (((hasDerivAt_id r).pow 3).const_mul k)).prodMk (hasDerivAt_const r (1:ℝ)) using 1
    ext <;> dsimp <;> ring
  have hd := (hasDerivAt_id r).mul
    (((H_analytic (d := d*r) (k := k*r^3) (by norm_num : (0:ℝ)<1)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt r hm)
  have he : (fun s => H ((d,k),s)) =ᶠ[𝓝 r] (fun s => s*H ((d*s,k*s^3),1)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact scaling d k hs
  have hc := (Hr_hasDerivAt (d := d) (k := k) hr).unique
    (hd.congr_of_eventuallyEq he)
  rw [fderiv_model] at hc
  change Hr ((d,k),r)=1*H ((d*r,k*r^3),1)+r*(d*P ((d*r,k*r^3),1)+
    (3*k*r^2)*Q ((d*r,k*r^3),1)+0*Hr ((d*r,k*r^3),1)) at hc
  rw [scaling d k hr,P_scaling d k hr,Q_scaling d k hr]
  nlinarith [hc]

lemma Hr_d_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun z => Hr ((z,k),r)) (R ((d,k),r)) d := by
  have hh := slice_d ((Hr_analytic (d := d) (k := k) hr).differentiableAt (by simp))
  have he : direction ((1,0),0) Hr ((d,k),r) = R ((d,k),r) :=
    direction_comm (H_analytic hr) _ _
  rw [he] at hh
  exact hh

lemma Hr_k_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun z => Hr ((d,z),r)) (S ((d,k),r)) k := by
  have hh := slice_k ((Hr_analytic (d := d) (k := k) hr).differentiableAt (by simp))
  have he : direction ((0,1),0) Hr ((d,k),r) = S ((d,k),r) :=
    direction_comm (H_analytic hr) _ _
  rw [he] at hh
  exact hh

noncomputable def Hrr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) Hr
lemma Hrr_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Hr ((d,k),s)) (Hrr ((d,k),r)) r :=
  slice_r ((Hr_analytic hr).differentiableAt (by simp))

lemma v_height_derivative (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    first (v profile (d,k)) (h,r) = k*R ((d+k*h,k),r) := by
  have he : (fun s => v profile (d,k) (s,r)) =
      (fun s => Hr ((d+k*s,k),r)) := funext (fun s => v_translation d k s hr)
  have hd := (Hr_d_hasDerivAt (d := d+k*h) (k := k) hr).comp h
    (((hasDerivAt_id h).const_mul k).const_add d)
  have hh := (first_hasDerivAt ((v_analytic profile profile_contDiff model_local_flow
    (p := (d,k)) (h := h) hr).differentiableAt (by simp))).unique
      (hd.congr_of_eventuallyEq (Eventually.of_forall (fun s => congrFun he s)))
  simpa only [mul_one,mul_comm] using hh

lemma v_width_derivative (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    second (v profile (d,k)) (h,r) = Hrr ((d+k*h,k),r) := by
  have he : (fun s => v profile (d,k) (h,s)) =ᶠ[𝓝 r]
      (fun s => Hr ((d+k*h,k),s)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact v_translation d k h hs
  exact (second_hasDerivAt ((v_analytic profile profile_contDiff model_local_flow
    (p := (d,k)) (h := h) hr).differentiableAt (by simp))).unique
      ((Hrr_hasDerivAt hr).congr_of_eventuallyEq he)

lemma transport_Hr {d k r : ℝ} (hr : 0 < r) :
    k*R ((d,k),r)-alpha ((d,k),r)*Hrr ((d,k),r) =
      -2*H ((d,k),r)*r*(1-(Hr ((d,k),r))^2)/(gap ((d,k),r))^2 := by
  have ht := transport_v profile profile_contDiff model_local_flow
    (p := (d,k)) (h := 0) hr
  rw [v_height_derivative d k 0 hr,v_width_derivative d k 0 hr,
    translation d k 0 hr,v_translation d k 0 hr] at ht
  simpa only [mul_zero,add_zero,alpha,gap] using ht

end QuinticLienard.QuadraticCoordinates

end OAI

import OAI.Geometry.Convex.GeneralMahler.ProfileGrowth
import OAI.Geometry.Convex.GeneralMahler.ScatterField
import OAI.Geometry.Convex.GeneralMahler.LayerMeasure

namespace OAI
/-! μ functionals and integrable density algebra for Section §03-04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Metric Real
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile

namespace rapid
variable {f g:ℝ→ℝ}
lemma rfadd (hf:rapid f) (hg:rapid g) : rapid fun x=> f x+g x := by
  intro n
  obtain ⟨C,hc,h⟩ := hf n
  obtain ⟨D,hd,h'⟩ := hg n
  refine ⟨C+D, by positivity, fun x=>?_⟩
  apply le_trans (mul_le_mul_of_nonneg_right (norm_add_le ..) (by positivity))
  rw [add_mul]; exact add_le_add (h x) (h' x)
lemma rfneg (hf:rapid f) : rapid fun x=> -f x := hf.mono (by simp)
lemma rfsub (hf:rapid f) (hg:rapid g) : rapid fun x=> f x-g x := by
  simpa only [sub_eq_add_neg] using hf.rfadd hg.rfneg
end rapid
lemma poly_st : PolyBound st := PolyBound.of_bound 1 fun x=> by unfold st; split <;> simp
lemma poly_p : PolyBound p := PolyBound.of_bound 1 fun x=>by
  rw [Real.norm_of_nonneg (p_pos x).le]; exact (p_lt_one x).le
lemma rapid_half_a : rapid fun x=> a x*(1-st x) := by
  apply rapid_phi.mono
  intro x
  unfold st; split_ifs with h
  · simp
  rw [sub_zero,mul_one,Real.norm_of_nonneg (a_pos _).le,
    Real.norm_of_nonneg (phi_pos _).le]
  simpa only [neg_neg,neg_phi] using a_high (-x) (by linarith)
lemma rapid_ar : rapid fun x=> a (-x)*st x := by
  apply rapid_phi.mono
  intro x
  unfold st; split_ifs with h
  · rw [mul_one,Real.norm_of_nonneg (a_pos _).le,
      Real.norm_of_nonneg (phi_pos _).le]; exact a_high x h
  simp

-- integrable densities with polynomial weights
def MomentF (f:ℝ→ℝ) :=
  ∀ g : ℝ→ℝ, Measurable g→PolyBound g→Integrable fun x=>f x*g x
namespace MomentF
variable {f g:ℝ→ℝ}
lemma of_rapid (hf:rapid f) (hm:Measurable f) : MomentF f :=
  fun _g hg h=> (hf.product h).integrable_real (hm.mul hg)
lemma inte (hf:MomentF f) : Integrable f := by simpa using hf (fun _ => 1) measurable_const (PolyBound.const _)
lemma add (hf:MomentF f) (hg:MomentF g) : MomentF fun x=>f x+g x := by
  intro u hu h; simp_rw [add_mul]
  exact (hf u hu h).add (hg u hu h)
lemma neg (hf:MomentF f) : MomentF fun x=> -f x := by
  intro u hu h
  simp_rw [neg_mul]; exact (hf u hu h).neg
lemma sub (hf:MomentF f) (hg:MomentF g) : MomentF fun x=> f x-g x := by simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma mul (hf:MomentF f) (hg:PolyBound g) (hm:Measurable g) : MomentF fun x=>f x*g x := by
  intro u hu h
  simp_rw [mul_assoc]; exact hf _ (hm.mul hu) (hg.mul h)
lemma mono (hf:MomentF f) (hm:Measurable g) (h:∀ x,‖g x‖ ≤ ‖f x‖) :
    MomentF g := by
  intro u hu h'
  apply (hf u hu h').mono (hm.mul hu).aestronglyMeasurable
  exact ae_of_all _ fun x=>by rw [Pi.mul_apply,norm_mul,norm_mul]; exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)
end MomentF
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)

-- deltas
def dB (x:ℝ) := q.Bt x-q.s0*a (-x)
def dr (x:ℝ) := q.r1 x-q.s0*(1-p x)
def hDel (x:ℝ) := q.avH x-q.s0*p x
def dm (x:ℝ) := q.layerW x-q.s0*phi x
def delt (j:ℝ→ℝ) :=
  -(∫ x, (2*p x*q.dB x*j x + (p x*q.dr x+q.hDel x)*(2*x*j x-deriv j x)))

lemma Bt_poly : PolyBound q.Bt := by
  have he : q.Bt = fun z=> ((m:ℝ)⁻¹)*⟪q.U,a z • q.U-q.shift z⟫ := by
    ext x; rw [Bt,q.Y_mean]; ring
  rw [he]
  let l := innerSL ℝ q.U
  exact (PolyBound.const _).mul ((PolyBound.clm (show Rn m→L[ℝ]ℝ from l)).comp
    ((poly_a.smul (PolyBound.const _)).sub q.s_poly))

lemma B_tail : rapid fun z=> q.Bt z* st z := by
  let f := fun z x=> st z • q.YT z x
  let v := q.dualMap
  have hy : PolyBound q.YT.uncurry := by
    change PolyBound (fun u:ℝ×Rn m=>coneProj q.D (-(q.Z u.2+q.shift u.1)))
    have hp : PolyBound (fun u:ℝ×Rn m=> -(q.Z u.2+q.shift u.1)) :=
      (((PolyBound.clm q.root.toContinuousLinearMap).comp PolyBound.snd).add
        (q.s_poly.comp PolyBound.fst)).neg
    exact (PolyBound.lipschitz (coneProj_lip q.D)).comp hp
  have hh : mixed f := by
    apply mixed.of_cutoff (show PolyBound f.uncurry from
      (poly_st.comp PolyBound.fst).smul hy)
      (show PolyBound (fun x:Rn m=>v.M*(1+‖x‖)) from
        (PolyBound.const _).mul ((PolyBound.const _).add PolyBound.id.norm))
    intro z x hz
    unfold f st; split_ifs with h
    · rw [Real.norm_of_nonneg h] at hz
      have hi := v.zero_y (-z) x (by simpa using hz)
      rw [show v.y (-z)= _ from q.Y_sc (-z),neg_neg] at hi
      simp only [hi,smul_zero]
    simp
  let l := ((m:ℝ)⁻¹) • (innerSL ℝ q.U)
  have hl (x:Rn m) : l x=⟪q.U,x⟫/(m:ℝ) := by unfold l; simp [div_eq_inv_mul]
  have hi (z:ℝ) : Integrable (f z) (normal m) := (q.Y_int z).smul (st z)
  have he : (fun z=> q.Bt z*st z) = fun z=> ∫ x,l (f z x) ∂normal m := by
    ext z
    rw [l.integral_comp_comm (hi _)]
    unfold f; rw [integral_smul,_root_.map_smul,hl,Bt]
    rw [smul_eq_mul,mul_comm]
  rw [he]
  apply mixed_integral_right _ fun z=>(l.integrable_comp (hi z)).aestronglyMeasurable
  let c := fun (_:ℝ) (_:Rn m)=> ‖l‖
  apply hh.product (show PolyBound c.uncurry from PolyBound.const _)
  intro x y
  apply (l.le_opNorm _).trans
  change ‖l‖*_ ≤ _*‖‖l‖‖
  rw [Real.norm_of_nonneg (norm_nonneg l),mul_comm]

lemma dB_poly : PolyBound q.dB := q.Bt_poly.sub
  ((PolyBound.const _).mul (poly_a.comp PolyBound.id.neg))

lemma dB_tail : rapid fun z=> q.dB z*st z := by
  convert q.B_tail.rfsub (rapid_ar.product (PolyBound.const q.s0)) using 1
  ext x; unfold dB; ring
lemma pB_tail : rapid fun z=> p z*q.dB z := by
  convert ((rapid_p.product q.dB_poly).rfadd q.dB_tail) using 1
  ext x; ring
lemma aB_tail : rapid fun z=> a z*q.dB z := by
  convert (rapid_half_a.product q.dB_poly).rfadd (q.dB_tail.product poly_a) using 1
  ext x; ring
lemma hd_tail : rapid q.hDel := by
  convert q.tail_H.rfsub (rapid_p.product (PolyBound.const q.s0)) using 1
  ext x; unfold hDel; ring

lemma moment_w : MomentF q.layerW := by
  intro f hm h
  obtain ⟨C,n,hc,h⟩ := h
  apply ((q.w_moment n).mul_const C).mono' (q.w_cont.measurable.mul hm).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Pi.mul_apply,norm_mul,Real.norm_of_nonneg (q.w_positive x).le]
  apply le_trans (mul_le_mul_of_nonneg_left (h x) (q.w_positive x).le)
  exact le_of_eq (by ring)
lemma ar_moment : MomentF fun x=>a x*q.r1 x :=
  q.moment_w.mono (ca.measurable.mul q.Bt_cd.continuous_deriv_one.measurable.neg) (fun x=>by
    rw [Real.norm_of_nonneg (mul_nonneg (a_pos x).le (q.r1_pos x).le),
      Real.norm_of_nonneg (q.w_positive x).le]
    exact le_add_of_nonneg_left (mul_nonneg (p_pos x).le (q.Bt_nonneg x)))
lemma a0_id (x:ℝ) : p x*a (-x)+a x*(1-p x)=phi x := by
  simp only [a,neg_phi,neg_p]; ring
lemma arDelta_moment : MomentF fun x=> a x*q.dr x := by
  have hf : MomentF (fun x=>a x*(1-p x)) :=
    (MomentF.of_rapid rapid_phi c_phi.measurable).mono
      (ca.measurable.mul (measurable_const.sub cp.measurable)) (fun x=> by
        rw [Real.norm_of_nonneg (mul_pos (a_pos _) (q_pos _)).le,
          Real.norm_of_nonneg (phi_pos _).le]
        exact (le_add_of_nonneg_left (mul_nonneg (p_pos x).le (a_pos (-x)).le)).trans_eq (a0_id _))
  convert q.ar_moment.sub (hf.mul (PolyBound.const q.s0) measurable_const) using 1
  ext x; unfold dr; ring
lemma prDelta_moment : MomentF fun x=>p x*q.dr x := by
  convert q.arDelta_moment.mul ratio_bound (cp.measurable.div ca.measurable) using 1
  ext x; field_simp [ne_of_gt (a_pos x)]
end ProjField
end GeneralMahler

end

end OAI

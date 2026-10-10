import OAI.Analysis.BernoulliCone.CapExtension

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

def seamHeight (x:Space 7):ℝ:=κ*Cylindrical.lift axis Real.sqrt (fun q:ℝ=>(Real.sqrt q)⁻¹) capH x
lemma seamHeight_formula (x:Space 7):
    seamHeight x=κ*Real.sqrt (Cylindrical.radiusSq axis x)*
      capH (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) := by
  simp only [seamHeight,Cylindrical.lift,div_eq_mul_inv,mul_assoc]
lemma seamHeight_contDiffAt {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    ContDiffAt ℝ ∞ seamHeight x := by
  have hs:ContDiffAt ℝ ∞ Real.sqrt (Cylindrical.radiusSq axis x):=Real.contDiffAt_sqrt hq.ne'
  have hL:ContDiffAt ℝ ∞ (Cylindrical.lift axis Real.sqrt (fun q:ℝ=>(Real.sqrt q)⁻¹) capH) x :=
    Cylindrical.contDiffAt_lift hs (hs.inv (Real.sqrt_pos.mpr hq).ne') capH_contDiff.contDiffAt
  exact contDiffAt_const.mul hL
lemma transverse_smul (a:ℝ) (x:Space 7):
    Cylindrical.transverse axis (a • x)=a • Cylindrical.transverse axis x := by
  rw [Cylindrical.transverse,Cylindrical.transverse,Cylindrical.axis_smul]
  module
lemma gradient_seamHeight {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    gradient seamHeight x=κ • seamGradient ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x) := by
  let q:=Cylindrical.radiusSq axis x
  let r:=Real.sqrt q
  let z:=Cylindrical.axis axis x
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hs:HasDerivAt Real.sqrt (1/(2*r)) q := Real.hasDerivAt_sqrt hq.ne'
  have hi:HasDerivAt (fun q:ℝ=>(Real.sqrt q)⁻¹) (-(1/(2*r))/r^2) q:=hs.inv hr.ne'
  have hh:=hasDerivAt_capH (z*r⁻¹)
  have hl:=Cylindrical.gradient_lift (e:=axis) hs.differentiableAt hi.differentiableAt hh.differentiableAt
  change gradient (fun y=>κ*Cylindrical.lift axis Real.sqrt (fun q:ℝ=>(Real.sqrt q)⁻¹) capH y) x=_
  have hL:DifferentiableAt ℝ (Cylindrical.lift axis Real.sqrt (fun q:ℝ=>(Real.sqrt q)⁻¹) capH) x :=
    (Cylindrical.contDiffAt_lift (Real.contDiffAt_sqrt hq.ne' : ContDiffAt ℝ 1 Real.sqrt q)
      ((Real.contDiffAt_sqrt hq.ne').inv hr.ne') (capH_contDiff.of_le (by simp)).contDiffAt).differentiableAt (by norm_num)
  rw [gradient_const_mul κ hL,hl]
  congr 1
  rw [hs.deriv,hi.deriv,hh.deriv]
  simp only [seamGradient,Cylindrical.axis_smul,transverse_smul]
  change (2*(1/(2*r))*capH (z*r⁻¹)) • Cylindrical.transverse axis x+
    (r*capHP (z*r⁻¹)) • (r⁻¹ • axis+(2*z*(-(1/(2*r))/r^2)) • Cylindrical.transverse axis x)=
      capHP (r⁻¹*z) • axis+(capH (r⁻¹*z)-r⁻¹*z*capHP (r⁻¹*z)) • (r⁻¹ • Cylindrical.transverse axis x)
  rw [mul_comm z r⁻¹]
  simp only [smul_add,smul_smul]
  have he1:r*capHP (r⁻¹*z)*r⁻¹=capHP (r⁻¹*z):=by field_simp
  have he2:2*(1/(2*r))*capH (r⁻¹*z)+r*capHP (r⁻¹*z)*(2*z*(-(1/(2*r))/r^2))=
      (capH (r⁻¹*z)-r⁻¹*z*capHP (r⁻¹*z))*r⁻¹:=by field_simp; ring
  rw [he1]
  calc
    _=capHP (r⁻¹*z) • axis+
      (2*(1/(2*r))*capH (r⁻¹*z)+r*capHP (r⁻¹*z)*(2*z*(-(1/(2*r))/r^2))) • Cylindrical.transverse axis x := by module
    _=_:=by rw [he2]

lemma normalized_radius_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    Cylindrical.radiusSq axis ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x)=1 := by
  rw [Cylindrical.radiusSq_smul,inv_pow,Real.sq_sqrt hq.le,inv_mul_cancel₀ hq.ne']

lemma upperFamily_at_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    upperFamily (Real.sqrt (Cylindrical.radiusSq axis x)) x=max (seamHeight x) 0 := by
  have hr:0<Real.sqrt (Cylindrical.radiusSq axis x):=Real.sqrt_pos.mpr hq
  have he:=normalized_radius_seam hq
  rw [upperFamily,upperSigned_cap he.le,smoothCap_at_seam he,seamHeight_formula,
    Cylindrical.axis_smul,←div_eq_inv_mul]
  rw [mul_max_of_nonneg _ _ (mul_nonneg κ_pos.le hr.le),mul_zero]

lemma upperParameter_seam_iff {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) :
    Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1 ↔ seamHeight p.1≤p.2 := by
  let r:=Real.sqrt (Cylindrical.radiusSq axis p.1)
  let l:=upperParameter p.1 p.2
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hl:0<l:=(upperParameter_spec hp).1
  have hle:Cylindrical.radiusSq axis (l⁻¹ • p.1)≤1 ↔ r≤l := by
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,div_le_iff₀ (sq_pos_of_pos hl),one_mul]
    have he:r^2=Cylindrical.radiusSq axis p.1:=Real.sq_sqrt hq.le
    rw [←he]
    exact sq_le_sq₀ hr.le hl.le
  rw [hle,←not_lt,upperParameter_lt_iff hp hr,upperFamily_at_seam hq,not_lt]
  exact max_le_iff.trans (and_iff_left ((U_nonneg _).trans hp.le))
end Bernoulli.DeSilvaJerison

end
end

end OAI

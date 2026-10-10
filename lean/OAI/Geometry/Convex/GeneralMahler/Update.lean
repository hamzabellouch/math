import OAI.Geometry.Convex.GeneralMahler.Parameter
import OAI.Geometry.Convex.GeneralMahler.HMatrix

namespace OAI
/-! §02 covariance equation from scalar inequalities of §01. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler

def lam : ℝ := 65/100
def mstar : ℝ := 352/1000
def ell0 : ℝ := -37/100
def cupper : ℝ := -341/1000

/-- Regularity and scalar bounds for the covariance update. -/
structure UpdatesOK (C K : ℝ → ℝ) : Prop where
  Cp : PolyBound C
  Kp : PolyBound K
  Cc : Continuous C
  Kc : Continuous K
  lo : ∀ x, 0 ≤ lam*tmin^2+tmin*C x + K x
  hi : ∀ x, lam*tmax^2+tmax*C x+K x ≤ 0
  tan : ∀ x, mstar^2 ≤ 2*ell0*C x-ell0^2-4*lam*K x
  C_hi : ∀ x, C x ≤ cupper

variable {m : ℕ}

def jprod (A B : Mat m) := (1/2:ℝ) • (A*B+B*A)
def updEq (C K T : Mat m) := lam • (T*T)+ jprod C T + K
def updGap (C T : Mat m) := -C-(2*lam) • T

lemma jordan_sym {A B : Mat m} (ha:A.IsHermitian) (hb:B.IsHermitian) :
    (jprod A B).IsHermitian := by
  apply Matrix.IsHermitian.smul _ (show IsSelfAdjoint (1/2:ℝ) from rfl)
  change star (A*B+B*A) = _
  rw [star_add,star_mul,star_mul, (show star A=A from ha),(show star B=B from hb),add_comm]
lemma sqPSD {A : Mat m} (ha:A.IsHermitian) : 0 ≤ A*A := by
  change IsSelfAdjoint A at ha
  conv_lhs => skip
  simpa only [ha.star_eq] using star_mul_self_nonneg A
lemma upd_sym {C K T : Mat m} (hc:C.IsHermitian) (hk:K.IsHermitian) (ht:T.IsHermitian) :
    (updEq C K T).IsHermitian := by
  refine (((Matrix.nonneg_iff_posSemidef.mp (sqPSD ht)).1.smul (show IsSelfAdjoint lam from rfl)).add
    (jordan_sym hc ht)).add hk
lemma upd_form {C K T:Mat m} (ht:T.IsHermitian) {a:ℝ} {v:Rn m}
    (hv:op T v = a • v) :
    ⟪v,op (updEq C K T) v⟫ = ⟪v,op (scalar m (lam*a^2)+a• C + K) v⟫ := by
  have hh := op_iff_hermitian.mp ht v (op C v)
  simp only [updEq,jprod,scalar,_root_.map_add,_root_.map_smul,_root_.map_mul,_root_.map_one,
    _root_.add_apply,_root_.smul_apply,mul_apply_eq_comp,
    inner_add_right,real_inner_smul_right]
  change _ = lam*a^2*⟪v,v⟫+_+_
  rw [← hh,hv]
  simp only [_root_.map_smul, hv,real_inner_smul_left,real_inner_smul_right]
  ring

lemma gap_from_cov {C K T : Mat m} (hC:C.IsHermitian)
    (ht:T∈specBox m tmin tmax)
    (hc:C ≤ scalar m cupper)
    (hh: 0 ≤ scalar m (-(ell0^2)-mstar^2)+(2*ell0)•C+ (-(4*lam))•K)
    (he : updEq C K T = 0) : scalar m mstar ≤ updGap C T := by
  let n := 2*lam
  have hn : 0≤n := by dsimp [n,lam]; norm_num
  have hp : 0 ≤ updGap C T := by
    have h₁ := add_le_add hc (smul_le_smul_of_nonneg_left ht.2.2 hn)
    have h₂ : scalar m cupper+n•scalar m tmax ≤ 0 := by
      simp only [scalar,smul_smul,← add_smul]
      have hi := scalar_le' (m:=m) (cupper+n*tmax) 0 (by dsimp [cupper,tmax,n,lam]; norm_num)
      simpa [scalar] using hi
    change 0 ≤ -C-n•T
    have hi := h₁.trans h₂
    rw [sub_nonneg]
    exact (le_neg_iff_add_nonpos_right).mpr (by simpa only [add_comm] using hi)
  apply sq_order_cancel (scalar_psd (show 0 ≤ mstar by dsimp [mstar]; norm_num)) hp
  rw [← sub_nonneg]
  let d := scalar m ell0
  have hu : 0 ≤ (C-d)*(C-d) := sqPSD (hC.sub (scalar_sym ..))
  apply (add_nonneg hu hh).trans_eq
  have Hk : K = -(lam • (T*T) + jprod C T) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact he)
  rw [Hk]
  dsimp only [updGap,jprod,d]
  simp only [sub_mul,mul_sub,neg_mul,mul_neg,smul_mul_assoc,mul_smul_comm,
    scalar, one_mul,mul_one,smul_add,smul_neg, smul_smul]
  module

namespace ProjField
variable [NeZero m]

def expL (f : ℝ→ℝ) (q : ProjField m) :=
  ∫ x, cfc f (q.Lmat x) ∂normal m

theorem intL (q : ProjField m) {f : ℝ→ℝ} (hm : Continuous f) (hf : PolyBound f) :
    Integrable (fun x=>cfc f (q.Lmat x)) (normal m) := by
  have hc : Continuous fun x=>cfc f (q.Lmat x) :=
    (cfc_continuous_herm f hm).comp_continuous q.L_cont q.L_sym
  obtain ⟨C,n,hc',hf⟩ := hf
  let g := fun x => C*(1+‖q.Lmat x‖)^n
  have h : PolyBound g :=
    (PolyBound.const _).mul (((PolyBound.const 1).add q.L_poly.norm).pow _)
  apply PolyBound.gaussian_integrable _ hc.aestronglyMeasurable
  refine h.mono fun x => ?_
  apply le_trans (spectrum_poly_le _ hc' hf (q.L_sym _))
  change g x ≤ ‖g x‖; exact le_abs_self _

lemma expL_sym (q:ProjField m) {f} (hm : Continuous f) (hf : PolyBound f) :
    (expL f q).IsHermitian :=
  hermitian_integral (q.intL hm hf) (ae_of_all _ fun _ => cfc_herm _ _)

lemma expL_affine_pos (q:ProjField m) {C K : ℝ→ℝ} (hc : Continuous C) (hk : Continuous K)
    (hh : PolyBound C) (hh' : PolyBound K) {x y z : ℝ}
    (he : ∀ t, 0 ≤ x + y*C t+z*K t) :
    0 ≤ scalar m x + y•expL C q + z•expL K q := by
  let f (t:Rn m) := scalar m x + y•cfc C (q.Lmat t)+ z•cfc K (q.Lmat t)
  have ic := (q.intL hc hh).smul y
  have ik := (q.intL hk hh').smul z
  have hp (t:Rn m) : 0 ≤ f t := by
    let A := q.Lmat t
    have hi : IsSelfAdjoint A := q.L_sym t
    have hl := cfc_nonneg (f := (fun t:ℝ=>x+y*C t+z*K t)) (a := A) (fun t _=>he t)
    have HE := cfc_add A (fun t => x+y*C t) (fun t=>z*K t)
      (show ContinuousOn _ (spectrum ℝ A) from (continuous_const.add (continuous_const.mul hc)).continuousOn)
      ((continuous_const.mul hk).continuousOn)
    conv at hl =>
      rhs
      rw [show cfc (fun t=>x+y*C t+z*K t) A = _ from HE, cfc_const_add x (fun t=>y*C t) A ((continuous_const.mul hc).continuousOn) hi, cfc_const_mul y C A hc.continuousOn,cfc_const_mul z K A hk.continuousOn, ← scalar_eq]
    exact hl
  have heq : ∫ t, f t ∂normal m = scalar m x + y•expL C q+z•expL K q := by
    unfold f expL
    rw [integral_add, integral_add, integral_smul,integral_smul]
    · simp; exact integral_smul z _
    all_goals first | exact integrable_const _ | exact ic | exact ik |
      exact (integrable_const _).add ic
  rw [← heq]
  apply Matrix.PosSemidef.nonneg
  exact psd_integral (((integrable_const _).add ic).add ik) (ae_of_all _ fun t=>(hp t).posSemidef)

lemma expL_bounds (q:ProjField m) {C K} (h:UpdatesOK C K) :
    expL C q ≤ scalar m cupper ∧
    0 ≤ scalar m (-(ell0^2)-mstar^2)+(2*ell0)•expL C q + (-(4*lam))•expL K q ∧
    0 ≤ scalar m (lam*tmin^2) + tmin • expL C q+ expL K q ∧
    scalar m (lam*tmax^2) + tmax • expL C q+ expL K q ≤ 0 := by
  have he (x y z) (hi : ∀ t, 0≤ x+y*C t+z*K t) := q.expL_affine_pos h.Cc h.Kc h.Cp h.Kp hi
  refine ⟨?_,he _ _ _ (fun t => by linarith [h.tan t]), ?_,?_⟩
  · have hb := he cupper (-1) 0 (fun t=>by linarith [h.C_hi t])
    simpa [sub_eq_add_neg,← sub_nonneg] using hb
  · have hb := he (lam*tmin^2) tmin 1 (fun t=>by linarith [h.lo t])
    simpa only [one_smul] using hb
  · have hb := he (-(lam*tmax^2)) (-tmax) (-1) (fun t=>by linarith [h.hi t])
    rw [← neg_nonneg]
    simpa only [scalar,neg_smul,one_smul,neg_add] using hb
end ProjField
end GeneralMahler

end

end OAI

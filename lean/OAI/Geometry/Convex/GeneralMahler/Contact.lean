import OAI.Geometry.Convex.GeneralMahler.CovHerm
import OAI.Geometry.Convex.GeneralMahler.Qprimitive
import OAI.Geometry.Convex.GeneralMahler.Indicator

namespace OAI
/-! Layer covariances and scalar contact term. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}
namespace ProjField
variable (q:ProjField m)
def Lr [NeZero m] : rightLayer where
  r := q.r1
  B := q.Bt
  hr := fun x=>(q.r1_pos x).le
  hc := q.Bt_cd.continuous_deriv_one.neg
  drB := q.Bt_d
  hb := q.B_tail
  poly := q.Bt_poly
  hw := q.moment_w

def ct (u:Plane) := (∫ x,⟪q.XT (min u.1 u.2) x,q.YT (max u.1 u.2) x⟫ ∂normal m)/(m:ℝ)
def Ct (f j:ℝ→ℝ) := ∫ u:Plane,q.ct u*(deriv f u.1*deriv j u.2)
lemma ct_pos [NeZero m] (u:Plane) : 0 ≤ q.ct u := by
  unfold ct
  apply div_nonneg _ m_pos.le
  apply integral_nonneg; intro x
  exact mem_posDual.mp (proj_mem ..) (proj_mem ..)

-- local notation centered pairing with normalized inner product
def ipt (f g:Rn m→Rn m) := (∫ x,⟪f x,g x⟫ ∂normal m)/(m:ℝ)
lemma ipt_i {f g:Rn m→Rn m} (hf:regular f) (hg:regular g) :
    Integrable (fun x=>⟪f x,g x⟫) (normal m) :=
  (PolyBound.of_prod_le hf.p hg.p (fun _x=>abs_real_inner_le_norm ..)).gaussian_integrable
    (hf.meas.inner hg.meas)
lemma ipt_sym (f g:Rn m→Rn m) : ipt f g=ipt g f := by
  unfold ipt
  congr 2; ext; exact real_inner_comm ..
lemma regneg {f:Rn m→Rn m} (h:regular f) : regular fun x=> -(f x) :=
  ⟨h.p.neg,h.meas.neg⟩
lemma regsub {f g:Rn m→Rn m} (h:regular f) (hh:regular g) : regular fun x=> f x-g x := by
  simpa only [sub_eq_add_neg] using h.add (regneg hh)
lemma regconst (v:Rn m) : regular (fun _:Rn m=>v) :=
  ⟨PolyBound.const _,aestronglyMeasurable_const⟩
lemma ipt_add {f g h:Rn m→Rn m} (hf:regular f) (hg:regular g) (hh:regular h) :
    ipt (fun x=>f x+g x) h=ipt f h+ipt g h := by
  unfold ipt; simp_rw [inner_add_left,integral_add (ipt_i hf hh) (ipt_i hg hh)]
  ring
lemma ipt_sub {f g h:Rn m→Rn m} (hf:regular f) (hg:regular g) (hh:regular h) :
    ipt (fun x=>f x-g x) h=ipt f h-ipt g h := by
  unfold ipt; simp_rw [inner_sub_left,integral_sub (ipt_i hf hh) (ipt_i hg hh)]
  ring
lemma ipt_smul (f g:Rn m→Rn m) (a:ℝ) :
    ipt (fun x=> a • f x) g=a*ipt f g := by
  unfold ipt; simp_rw [real_inner_smul_left,integral_const_mul]; ring
lemma ipt_const {f:Rn m→Rn m} (hf:regular f) (v:Rn m) :
    ipt (fun _=> v) f=⟪v,∫ x,f x ∂normal m⟫/(m:ℝ) := by
  unfold ipt
  congr 1
  exact (innerSL ℝ v).integral_comp_comm hf.ig

lemma Z_reg : regular q.Z := ⟨PolyBound.clm q.root.toContinuousLinearMap,
  q.root.continuous.aestronglyMeasurable⟩
lemma Z_mean : (∫ x,q.Z x ∂normal m)=0 := by
  have h := affineN_mean q.root 0
  simpa only [affineN,Z,add_zero] using h
lemma X_reg (z:ℝ) : regular (q.XT z) :=
  ⟨poly_sample ..,(q.X_int z).aestronglyMeasurable⟩
lemma Y_reg (z:ℝ) : regular (q.YT z) :=
  ⟨by
    rw [show q.YT z=_ from funext (q.YT_sub z)]
    exact (q.X_reg z).p.sub (q.Z_reg.p.add (PolyBound.const _)),(q.Y_int z).aestronglyMeasurable⟩

lemma zz_cov : ipt q.Z q.Z=q.s0 := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  let l := fun i=> innerSL ℝ (q.Z (b i))
  have he (i) (x:Rn m) : ⟪b i,q.Z x⟫=l i x := by
    unfold l
    change ⟪b i,q.Z x⟫=⟪q.Z _,x⟫; rw [q.Z_def,q.Z_def]; exact (op_iff_hermitian.mp q.pos.1 ..).symm
  have hs (i:Fin m) :
      (∫ x:Rn m, (l i x)^2 ∂normal m)=⟪q.Z (b i),q.Z (b i)⟫ := by
    have h := normal_IBP_lipschitz (l i).lipschitzWith (q.Z (b i))
    calc
      _ = ∫ x:Rn m,⟪x,q.Z (b i)⟫ • (l i x) ∂normal m := by
        congr 1; ext x; rw [real_inner_comm]
        change ⟪q.Z (b i),x⟫^2= _*⟪q.Z (b i),x⟫; ring
      _ = _ := by rw [← h]; simp_rw [ContinuousLinearMap.fderiv]; simp; exact real_inner_self_eq_norm_sq (q.Z (b i))
  unfold ipt s0 trN
  congr 1
  have hx (x) : ⟪q.Z x,q.Z x⟫=∑ i:Fin m,(l i x)^2 := by
    conv_lhs => arg 2; rw [← b.sum_repr (q.Z x)]
    rw [sum_inner]
    congr 1; ext i
    rw [b.repr_apply_apply,real_inner_smul_left]
    rw [he]; ring
  simp_rw [hx]; rw [integral_finsetSum]
  · simp_rw [hs]
    rw [← mul_one q.covMat,q.trace_SPS]
    simp only [q.Z_def,_root_.map_one]
    rfl
  exact fun i _=> ((PolyBound.clm (l i)).pow 2).gaussian_integrable
    (((l i).continuous.pow _).aestronglyMeasurable)

def Xcenter (z:ℝ) (x:Rn m) := q.XT z x-a z • q.U
lemma Xc_reg (z:ℝ) : regular (q.Xcenter z) :=
  regsub (q.X_reg z) (regconst _)
lemma Xc_mean (z:ℝ) : (∫ x,q.Xcenter z x ∂normal m)=0 := by
  unfold Xcenter; rw [integral_sub (q.X_int z) (integrable_const _),q.XT_mean]; simp
lemma xz_cov (z:ℝ) : ipt (q.Xcenter z) q.Z=q.avH z := by
  unfold Xcenter
  rw [ipt_sub (q.X_reg z) (regconst _) q.Z_reg,ipt_const q.Z_reg,q.Z_mean,
    inner_zero_right,zero_div,sub_zero]
  exact (q.avH_as_mean_ip z).symm
lemma xx_cov (z y:ℝ) (hy:z ≤ y) :
    ipt (q.Xcenter z) (q.Xcenter y)=q.avH z-a z*q.Bt y+q.ct (z,y) := by
  have he : q.Xcenter y=fun x=>q.Z x+q.YT y x+(q.shift y - a y • q.U) := by ext x; rw [q.YT_sub]; unfold Xcenter; abel_nf
  rw [ipt_sym,he,ipt_add (q.Z_reg.add (q.Y_reg y)) (regconst _) (q.Xc_reg z),ipt_const (q.Xc_reg z),q.Xc_mean,
    inner_zero_right,zero_div,add_zero,ipt_add q.Z_reg (q.Y_reg y) (q.Xc_reg z),ipt_sym q.Z (q.Xcenter z),q.xz_cov,ipt_sym]
  unfold Xcenter
  rw [ipt_sub (q.X_reg z) (regconst _) (q.Y_reg y),ipt_const (q.Y_reg y),
    real_inner_smul_left]
  have hh : q.ct (z,y) =ipt (q.XT z) (q.YT y) := by unfold ct ipt; simp [hy]
  rw [hh,Bt]; ring

lemma Zs_reg (z:ℝ) : regular fun x:Rn m=>p z • q.Z x :=
  q.Z_reg.smul ⟨PolyBound.const _, aestronglyMeasurable_const⟩
lemma ww_cov0 [NeZero m] (z y:ℝ) (h:z≤y) :
    ipt (q.WW z) (q.WW y) = q.Hcov (z,y)+q.ct (z,y)-q.Lr.Kab (z,y) := by
  have he (z:ℝ) : q.WW z= fun x=>p z • q.Z x-q.Xcenter z x := by
    ext x; unfold WW Xcenter; abel_nf
  rw [he z,he y,ipt_sub (q.Zs_reg z) (q.Xc_reg z) (regsub (q.Zs_reg y) (q.Xc_reg y)),
    ipt_sym (fun x=>p z • q.Z x),ipt_sub (q.Zs_reg y) (q.Xc_reg y) (q.Zs_reg z),
    ipt_sym (q.Xcenter z) (fun x=>_),ipt_sub (q.Zs_reg y) (q.Xc_reg y) (q.Xc_reg z),
    ipt_smul,ipt_sym q.Z (fun x=>_),ipt_smul, q.zz_cov,
    ipt_sym (q.Xcenter y) (fun x=>p z • q.Z x),ipt_smul,
    ipt_smul, ipt_sym q.Z (q.Xcenter z),ipt_sym q.Z (q.Xcenter y), q.xz_cov,q.xz_cov,
    ipt_sym, q.xx_cov z y h]
  unfold Hcov rightLayer.Kab
  simp only [min_eq_left h,max_eq_right h,Lr]; ring

lemma WW_pair_cov [NeZero m] (u:Plane) :
    ipt (q.WW u.1) (q.WW u.2) = q.Hcov u+q.ct u-q.Lr.Kab u := by
  rcases u with ⟨z,y⟩
  rcases le_total z y with h|h
  · exact q.ww_cov0 z y h
  rw [ipt_sym]; convert q.ww_cov0 y z h using 1
  unfold Hcov rightLayer.Kab ct
  simp only [min_comm,max_comm]
  ring

end ProjField
end GeneralMahler

end

end OAI

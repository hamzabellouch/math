import OAI.Geometry.Convex.GeneralMahler.BoundField
import OAI.Geometry.Convex.GeneralMahler.MatrixBox
import OAI.Geometry.Convex.GeneralMahler.Transform

namespace OAI
/-! Coordinate and covariance parameters in compact boxes. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}

-- Exact finite decimals of the paper as rationals cast to ℝ
def tmin : ℝ := -22/1000
def tmax : ℝ := 64/1000

-- Use S bounded coarsely between I/2 and 2I; precise equation maintained.
lemma add_cov_box {T : Mat m} (ht : T∈specBox m tmin tmax) :
    1+T∈specBox m (1/4:ℝ) 4 := by
  refine ⟨Matrix.isHermitian_one.add ht.1,?_,?_⟩
  · calc
      _ ≤ scalar m (1+tmin) := scalar_le' _ _ (by norm_num [tmin])
      _ = 1+scalar m tmin := by unfold scalar; rw [add_smul,one_smul]
      _ ≤ _ := add_le_add le_rfl ht.2.1
  · calc
      _ ≤ 1+scalar m tmax := add_le_add le_rfl ht.2.2
      _ = scalar m (1+tmax) := by unfold scalar; rw [add_smul,one_smul]
      _ ≤ _ := scalar_le' _ _ (by norm_num [tmax])

lemma scalar_mul (a b : ℝ) :
    scalar m a * scalar m b = scalar m (a*b) := by simp [scalar_eq]

lemma scalar_psd {a:ℝ} (h:0 ≤ a) : 0 ≤ scalar m a := by
  simpa [scalar] using (scalar_le' (m:=m) 0 a h)

lemma root_box {T : Mat m} (ht : T∈specBox m tmin tmax) :
    CFC.sqrt (1+T)∈specBox m (1/2:ℝ) 2 := by
  have hh := add_cov_box ht
  have he := (form_posDef (by norm_num) hh).posSemidef.nonneg
  have hpos := (CFC.sqrt_nonneg (1+T))
  have heq := CFC.sqrt_mul_sqrt_self _ he
  refine ⟨hpos.posSemidef.1,sq_order_cancel (scalar_psd (by norm_num)) hpos ?_,
    sq_order_cancel hpos (scalar_psd (by norm_num)) ?_⟩
  · rw [scalar_mul,heq]; convert hh.2.1 using 1; norm_num
  rw [heq, scalar_mul]; convert hh.2.2 using 1; norm_num

def equivPD {A : Mat m} (h:A.PosDef) : Rn m ≃L[ℝ] Rn m :=
  (pd_equiv h).choose
@[simp] lemma equivPD_spec {A : Mat m} (h:A.PosDef) : (equivPD h).toContinuousLinearMap=op A :=
  (pd_equiv h).choose_spec

lemma inv_norm_box (Q:ℝ) (hq : 0<Q) {A:Mat m} (hA:A∈specBox m Q⁻¹ Q)
    (e:Rn m≃L[ℝ]Rn m) (he : e.toContinuousLinearMap = op A) :
    ‖A‖ ≤ Q ∧ ‖e.symm.toContinuousLinearMap‖ ≤ Q := by
  have hi := inv_pos.mpr hq
  refine ⟨spectrum_norm_box hq.le hA.1 ((scalar_le' _ _ (by linarith)).trans hA.2.1)
    hA.2.2,e.symm.toContinuousLinearMap.opNorm_le_bound hq.le fun x=>?_⟩
  change ‖e.symm x‖ ≤ Q*‖x‖
  let y := e.symm x
  have hv := (mem_box_form.mp hA).2.1 y
  have hh : op A y=x := by rw [← he]; exact e.apply_symm_apply x
  rw [hh] at hv
  by_cases hz:y=0
  · change ‖y‖ ≤ _
    rw [hz,norm_zero]; positivity
  apply le_of_sub_nonneg
  have ha := hv.trans (real_inner_le_norm y x)
  rw [inv_mul_eq_div, div_le_iff₀ hq] at ha
  have hp := norm_pos_iff.mpr hz
  change 0 ≤ Q*‖x‖-‖y‖
  nlinarith

def params (m : ℕ) (R : ℝ) : Set (Mat m × Mat m) :=
  (specBox m R⁻¹ R) ×ˢ (specBox m tmin tmax)

abbrev Param (m : ℕ) (R:ℝ) := ↥(params m R)

variable {R : ℝ}

namespace Param
def B (x : Param m R) := x.val.1
def T (x : Param m R) := x.val.2
lemma in_box (x : Param m R) :
    x.B∈specBox m R⁻¹ R ∧ x.T∈specBox m tmin tmax := x.property

def S (x : Param m R) := CFC.sqrt (1+x.T)
lemma S_box (x : Param m R) : x.S ∈ specBox m (1/2:ℝ) 2 := root_box x.in_box.2
lemma S_pos (x : Param m R) : x.S.PosDef := form_posDef (by norm_num) x.S_box

def transE (x : Param m R) (hr : 0<R) :=
  equivPD (form_posDef (inv_pos.mpr hr) x.in_box.1)

lemma trans_apply (x : Param m R) (hr : 0<R) (a) :
    x.transE hr a = op x.B a :=
  congrFun (congrArg DFunLike.coe (equivPD_spec (form_posDef (inv_pos.mpr hr) x.in_box.1))) a

lemma contra_eq (x : Param m R) (hr : 0<R) :
    contra (x.transE hr).toLinearEquiv = (x.transE hr).symm.toLinearEquiv := by
  let b := x.transE hr
  ext y : 1
  apply ext_inner_left ℝ
  intro z
  obtain ⟨z,rfl⟩ := b.surjective z
  have hi (z v : Rn m) : ⟪b z,v⟫=⟪z,b v⟫ := by
    unfold b
    rw [x.trans_apply hr,x.trans_apply hr]; exact op_iff_hermitian.mp x.in_box.1.1 z v
  change ⟪b z,contra b.toLinearEquiv y⟫=⟪b z,b.symm y⟫
  rw [hi z (b.symm y), b.apply_symm_apply]
  apply pair_contra b.toLinearEquiv

def instanceQ (x : Param m R) (hr : 0<R) (q : ProjField m) :
    ProjField m where
  C := pushCone (x.transE hr).toLinearEquiv q.C
  U := x.transE hr q.U
  V := contra (x.transE hr).toLinearEquiv q.V
  U_in := apply_mem_interior_pushCone.mpr q.U_in
  V_in := by rw [dual_pushCone]; exact apply_mem_interior_pushCone.mpr q.V_in
  ip := (pair_contra (x.transE hr).toLinearEquiv ..).trans q.ip
  S := x.S
  pos := x.S_pos
  root := equivPD x.S_pos
  matrix_eq := equivPD_spec _

lemma sigma_choice (x : Param m R) (hr : 0<R) (q : ProjField m) :
    (x.instanceQ hr q).covMat= 1+x.T :=
  CFC.sqrt_mul_sqrt_self _ ((form_posDef (by norm_num)
    (add_cov_box x.in_box.2)).posSemidef.nonneg)

lemma Bound_instance (x : Param m R) (hr : 2 ≤ R) (h : 0<R) {q:ProjField m} {K:ℝ}
    (hk : q.Bound K) :
    (x.instanceQ h q).Bound (K*R) := by
  have hv := inv_norm_box R h x.in_box.1 (x.transE h) (equivPD_spec _)
  have hew := (inv_norm_box 2 (by norm_num) (A := x.S) (by simpa using x.S_box)
    (equivPD x.S_pos) (equivPD_spec _))
  let b := x.transE h
  let b' := contra b.toLinearEquiv
  have hb (y : Rn m) : ‖b y‖ ≤ R * ‖y‖ := by
    rw [show b y = op x.B y from x.trans_apply h y]
    apply ((op x.B).le_opNorm y).trans
    rw [op_norm]; gcongr; exact hv.1
  have hb' (y : Rn m) : ‖b' y‖ ≤ R*‖y‖ := by
    dsimp only [b',b]; rw [contra_eq]
    apply ((x.transE h).symm.toContinuousLinearMap.le_opNorm y).trans
    apply mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
  have HH := hk.one_le
  have hkR : 2 ≤ K*R := by nlinarith
  refine ⟨by linarith,?_ ,?_ , hew.1.trans hkR, hew.2.trans hkR, ?_,?_⟩
  · apply (hb q.U).trans
    nlinarith [hk.Ub]
  · apply (hb' q.V).trans; nlinarith [hk.Vb]
  · intro y hy
    change y ∈ posDual (pushCone b.toLinearEquiv q.C) at hy
    obtain ⟨y,rfl⟩ := b'.surjective y
    rw [dual_pushCone] at hy
    have hu : y∈q.D := by simpa only [b',mem_pushCone,LinearEquiv.symm_apply_apply] using hy
    change ‖b' y‖ ≤ K*R*⟪b.toLinearEquiv q.U,b' y⟫
    rw [show ⟪b.toLinearEquiv q.U,b' y⟫ = _ from pair_contra ..]
    apply (hb' y).trans
    nlinarith [hk.inC y hu]
  · intro y hy
    obtain ⟨y,rfl⟩ := b.surjective y
    have hu : y∈q.C := by
      change b.toLinearEquiv y∈pushCone b.toLinearEquiv q.C at hy
      simpa using hy
    change ‖b y‖ ≤ K*R*⟪b' q.V,b.toLinearEquiv y⟫
    rw [real_inner_comm,show ⟪b.toLinearEquiv y,b' q.V⟫ = _ from pair_contra .., real_inner_comm q.V]
    apply (hb y).trans; nlinarith [hk.inD y hu]
end Param
end GeneralMahler

end

end OAI

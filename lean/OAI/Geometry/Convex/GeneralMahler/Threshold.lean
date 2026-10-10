import OAI.Geometry.Convex.GeneralMahler.Frame.Diagonal
import OAI.Geometry.Convex.GeneralMahler.CovHerm
import OAI.Geometry.Convex.GeneralMahler.Indicator

namespace OAI
/-! Thresholds of arbitrary moderate-growth random Hermitian fields
(in particular A and L) §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}
structure FieldMat (m:ℕ) where
  A : Rn m→Mat m
  sym : ∀ x,(A x).IsHermitian
  hM : StronglyMeasurable A
  poly : PolyBound A
namespace ProjField
variable [NeZero m] (q:ProjField m)
def FA : FieldMat m where
  A := q.Amat
  sym := q.H_hermitian poly_id_der
  hM := q.A_SM
  poly := q.A_poly
def FL : FieldMat m where
  A := q.Lmat
  sym := q.L_sym
  hM := q.L_cont.stronglyMeasurable
  poly := q.L_poly
end ProjField

namespace FieldMat
variable (B:FieldMat m)
lemma reg : regular B.A := ⟨B.poly,B.hM.aestronglyMeasurable⟩

def Fr (x:Rn m) := Frm.fr (⟨B.A x,B.sym x⟩:Frm.SH m)
lemma Fr_D (x) : (B.Fr x).Dgn (B.A x) := Frm.fr_d _
lemma fr_m : Measurable B.Fr := Frm.fr_m.comp (B.hM.measurable.subtype_mk (h:=B.sym))
def ev (x:Rn m) := (B.Fr x).eig (B.A x)
lemma ev_m (i) : Measurable fun x=> B.ev x i :=
  (measurable_pi_iff.mp (Frm.cdiag.measurable.comp
    (Frm.cont_loc.measurable.comp (B.hM.measurable.prodMk B.fr_m)))) i

def eval (f:ℝ→ℝ) (x:Rn m) := cfc f (B.A x)
lemma evfrm (x) (f) :
    (B.Fr x).loc (B.eval f x)= Matrix.diagonal (fun i=> f (B.ev x i)) :=
  Frm.loc_cfc _ (B.sym x) (B.Fr_D x) f
lemma evfrm' (x) (f) : B.eval f x= (B.Fr x).fixMat (Matrix.diagonal (fun i=> f (B.ev x i))) := by
  rw [← B.evfrm x f,Frm.fix_loc]

lemma theta_gen_meas {f:ℝ→ℝ→ℝ} (hf:Measurable f.uncurry) :
    Measurable (fun u:ℝ × Rn m=>B.eval (f u.1) u.2) := by
  simp_rw [B.evfrm',Frm.fixMat]
  have hg : Measurable (fun u:ℝ×Rn m=>(B.Fr u.2).val) :=
    measurable_subtype_coe.comp (B.fr_m.comp measurable_snd)
  have hh : Measurable fun u:ℝ×Rn m=> Matrix.diagonal (fun i=> f u.1 (B.ev u.2 i)) :=
    Frm.cdiagonal.measurable.comp (measurable_pi_iff.mpr fun i=> hf.comp
      (measurable_fst.prodMk ((B.ev_m _).comp measurable_snd)))
  exact (hg.mul hh).mul (continuous_star.measurable.comp hg)

lemma eval_reg {f:ℝ→ℝ} (hf:TestF f) : regular (B.eval f) := by
  have hm : Measurable (B.eval f) := by
    have h := B.theta_gen_meas (f:=fun _ x=>f x) (hf.cont.measurable.comp measurable_snd)
    exact h.comp (show Measurable (fun x:Rn m=>((0:ℝ),x)) by fun_prop)
  obtain ⟨C,n,hc,h⟩ := hf.poly
  have hp : PolyBound (fun x=>C*(1+‖B.A x‖)^n) :=
    (PolyBound.const _).mul (((PolyBound.const _).add B.poly.norm).pow _)
  refine ⟨hp.mono (fun x=>?_ ), hm.aestronglyMeasurable⟩
  apply le_trans (spectrum_poly_le f hc h (B.sym x)); exact le_abs_self _

def Θ (z:ℝ) (x:Rn m) := B.eval (jump z) x
lemma thetaM : StronglyMeasurable B.Θ.uncurry := (B.theta_gen_meas jump_m).stronglyMeasurable
lemma theta_nn (z x) : 0 ≤ B.Θ z x := by
  have hi : IsSelfAdjoint (B.A x) := B.sym x
  apply cfc_nonneg
  intro y _; unfold jump; split_ifs <;> norm_num
lemma theta_le (z x) : B.Θ z x ≤ 1 := by
  have hi := (scalar_cfc_order (jump z) (B.A x) (B.sym x) (l:=0) (r:=1)).2.mpr
    (fun y _=> by unfold jump; split_ifs <;> norm_num)
  simpa [Θ,eval,scalar] using hi
lemma theta_norm (z x) : ‖B.Θ z x‖ ≤ 1 := by
  apply spectrum_norm_box zero_le_one (B.theta_nn ..).posSemidef.1
  · apply le_trans _ (B.theta_nn z x)
    have he := scalar_le' (m:=m) (-1) 0 (by norm_num)
    simpa only [scalar, zero_smul] using he
  simpa [scalar] using B.theta_le z x

def QP (z:ℝ) (x:Rn m) := B.Θ z x-st z • (1:Mat m)
lemma theta_exact (z x) (hx : ‖B.A x‖< |z|) : B.QP z x=0 := by
  let A := B.A x
  have hi : IsSelfAdjoint A := B.sym x
  have he (t:ℝ) (ht:t∈spectrum ℝ A) : ‖t‖ ≤ ‖A‖ := by
    have h := norm_apply_le_norm_cfc id A ht
    rw [cfc_id ℝ A] at h
    exact h
  have hh : cfc (jump z) A=cfc (fun _=>st z) A := cfc_congr fun t ht=> by
    have hv := he t ht
    change ‖A‖<_ at hx
    unfold jump st; rw [Real.norm_eq_abs] at hv; split_ifs <;> grind
  unfold QP; change cfc (jump z) A-_ = _
  rw [hh,cfc_const (st z) A hi,Algebra.algebraMap_eq_smul_one,sub_self]
lemma qp_mixed : mixed B.QP := by
  apply mixed.of_cutoff
    (show PolyBound B.QP.uncurry from
      (PolyBound.of_bound (f:=B.Θ.uncurry) 1 (fun ⟨z,x⟩=>B.theta_norm z x)).sub
        ((poly_st.comp PolyBound.fst).smul (PolyBound.const (1:Mat m))))
    B.poly.norm
  exact fun z x=> B.theta_exact z x
end FieldMat
namespace ProjField
variable [NeZero m] (q:ProjField m) (B:FieldMat m)
def EZ (z:ℝ) (x:Rn m) := q.Pmat z x-B.Θ z x
lemma eM : mixed (q.EZ B) := by
  convert q.Pstep_mixed.sub B.qp_mixed using 1
  funext y x; simp only [EZ,Pstep,Gstep,FieldMat.QP]; abel
lemma eSM : StronglyMeasurable (q.EZ B).uncurry :=
  q.edge.meas.stronglyMeasurable.sub B.thetaM

def zE (f:ℝ→ℝ) (z:ℝ) (x:Rn m) := deriv f z • q.EZ B z x
lemma zm {f:ℝ→ℝ} (hf:TestF f) : mixed (q.zE B f) := by
  apply (q.eM B).product (g:=fun z _=>deriv f z)
    (show PolyBound (fun u:ℝ × Rn m=>deriv f u.1) from hf.der.poly.comp PolyBound.fst)
  intro z x; unfold zE; rw [norm_smul,mul_comm]
lemma zSM (f) : StronglyMeasurable (q.zE B f).uncurry :=
  (((measurable_deriv f).comp measurable_fst).stronglyMeasurable).smul (q.eSM B)
lemma zi {f:ℝ→ℝ} (hf:TestF f) (x) :
    Integrable fun z=>q.zE B f z x := mixed_integrable_left (q.zm B hf) x
      (((q.zSM B f).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)

def MB (f:ℝ→ℝ) (x:Rn m) := q.Hmat f x-B.eval f x+scalar m (ga f)
lemma mb_eq {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    q.MB B f x= -(∫ z,q.zE B f z x) := by
  have iH := q.H_left_int hf.der.poly x; have iZ := q.zi B hf x
  let u := B.Fr x
  let g := fun z=> q.kerH f z x + q.zE B f z x
  have he (z) :
      u.loc (g z)=Matrix.diagonal (fun i=>ss f z (B.ev x i)) := by
    unfold g kerH zE PD EZ
    rw [← smul_add]
    have ht : p z • (1:Mat m)-q.Pmat z x+(q.Pmat z x-B.Θ z x)= p z • 1-B.Θ z x := by abel
    rw [ht, u.loc_smul,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.Θ z x)= _ from B.evfrm x _]
    ext i j
    by_cases h:i=j
    · subst j; simp [ss,score,mul_comm]
    simp [h]
  let l : Mat m→L[ℝ]Mat m := LinearMap.toContinuousLinearMap (𝕜:=ℝ)
    { toFun:=u.loc, map_add':=u.loc_add, map_smul':=u.loc_smul }
  have hl : ∫ z,g z = B.eval f x - scalar m (ga f) := by
    apply u.loc_inj
    rw [u.loc_sub,u.loc_smul, u.loc_one,show u.loc (B.eval f x)= _ from B.evfrm x f]
    have hi := iH.add iZ
    have ig : Integrable g := iH.add iZ
    change l _=_
    rw [← l.integral_comp_comm ig]
    have hh (z) : l (g z)= _ := he z
    have hh' (i j:Fin m) := (coeffMap i j).integral_comp_comm
      (l.integrable_comp ig)
    ext i j
    rw [show (∫ z,l (g z)) i j=(∫ z,l (g z) i j) from (hh' i j).symm]
    simp_rw [hh]
    by_cases h:i=j
    · subst j
      simpa using centered_s hf (B.ev x i)
    simp [h]
  have h := integral_add iH iZ
  change ∫ z,g z=_ at h
  rw [hl] at h
  unfold MB Hmat
  rw [show (∫ z,q.kerH f z x)=_ from eq_sub_of_add_eq h.symm]
  abel

end ProjField
end GeneralMahler

end

end OAI

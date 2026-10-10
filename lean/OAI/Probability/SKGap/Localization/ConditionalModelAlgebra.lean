import Mathlib
import OAI.Probability.SKGap.Localization.ConditionalRankAlgebra
import OAI.Probability.SKGap.Matrix.GOEBlockExpansion

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def conditionalBlockMatrix (r j q s S a B κ ell : ℝ) (u Z : ι → ℝ)
    (g : MatrixCoordinates ι → ℝ) : Matrix ι ι ℝ :=
  goeBlockResidual r κ ell u g+
    vecMulVec u ((j*sqrt (q/s)) • Z-(j*a/s) • u)+
    vecMulVec ((j*sqrt (q/s)) • Z-(j*a/s) • u) u+
    (2*j*(a+B*q)/S) • vecMulVec u u

def conditionalMeanCoefficient (j q s S a B BA κ : ℝ) :=
  conditionalCoefficient j
    ((2*j*q-2*j*a/s+2*j*(a+B*q)/S+2*BA*(κ-1))/q)
    j ((κ-1)*sqrt BA/sqrt q)

def conditionalScalarCoefficient (q κ ell : ℝ) :=
  conditionalCoefficient 0 ((ell-2*κ+1)/q) 0 0

lemma conditionalCoefficient_add_scalar (j cM cG cN z w : ℝ) :
    conditionalCoefficient j cM cG cN+
      z • conditionalCoefficient 0 w 0 0=
      conditionalCoefficient j (cM+z*w) cG cN := by
  ext i k
  cases i with
  | inl i => cases k with
    | inl k => fin_cases i <;> fin_cases k <;>
        simp [conditionalCoefficient]
    | inr k => fin_cases i <;> simp [conditionalCoefficient,conditionalCoupling]
  | inr i => cases k with
    | inl k => fin_cases k <;> simp [conditionalCoefficient,conditionalCoupling]
    | inr k => simp [conditionalCoefficient]

lemma conditionalMeanCoefficient_equality {j q s b κ : ℝ}
    (hs : 0 < s) (hq : 0 < q) (hj : 0 ≤ j) :
    conditionalMeanCoefficient j q s (s+j*q) (s*b) (j*b) (j*b) κ=
      conditionalCoefficient j ((2*j*q+2*(j*b)*(κ-1))/q) j ((κ-1)*sqrt (j*b)/sqrt q) := by
  have hS : s+j*q ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hs (mul_nonneg hj hq.le))
  unfold conditionalMeanCoefficient
  congr 1
  field_simp
  ring

theorem conditional_hessian_rank_form (r j a B κ ell : ℝ)
    {q s S BA : ℝ} (hq : 0 < q) (hs : 0 < s) (hBA : 0 < BA)
    (X u Z : ι → ℝ) (D : Matrix ι ι ℝ) (g : MatrixCoordinates ι → ℝ) :
    let W := goeMatrix r g
    let Q := conditionalColumns X (sqrt q • u) ((sqrt s)⁻¹ • Z)
      (residualGramVector BA W u)
    1+D*(B • (1 : Matrix ι ι ℝ)-conditionalBlockMatrix r j q s S a B κ ell u Z g-
      j • vecMulVec X X-(2*j*q) • vecMulVec u u)*D=
      (1-D*(W-BA • (1 : Matrix ι ι ℝ))*D)-
      D*Q*(conditionalMeanCoefficient j q s S a B BA κ+
        goeBilinear r u u g • conditionalScalarCoefficient q κ ell)*Qᵀ*D+
      (B-BA) • (D*D) := by
  dsimp only
  have hroot : sqrt (q/s)*sqrt s/sqrt q=1 := by
    rw [Real.sqrt_div hq.le]
    field_simp
  have hz : j*sqrt (q/s)*sqrt s/sqrt q=j := by
    calc
      _ = j*(sqrt (q/s)*sqrt s/sqrt q) := by ring
      _ = _ := by rw [hroot,mul_one]
  have hrank := conditional_rank_change_basis X u Z (goeMatrix r g*ᵥu) j
    (2*j*q-2*j*a/s+2*j*(a+B*q)/S+(ell-2*κ+1)*goeBilinear r u u g)
    (j*sqrt (q/s)) (κ-1) hq hs hBA
  dsimp only at hrank
  rw [hz] at hrank
  have hc : conditionalMeanCoefficient j q s S a B BA κ+
      goeBilinear r u u g • conditionalScalarCoefficient q κ ell=
      conditionalCoefficient j
        ((2*j*q-2*j*a/s+2*j*(a+B*q)/S+(ell-2*κ+1)*goeBilinear r u u g+2*BA*(κ-1))/q)
        j ((κ-1)*sqrt BA/sqrt q) := by
    unfold conditionalMeanCoefficient conditionalScalarCoefficient
    rw [conditionalCoefficient_add_scalar]
    congr 1
    ring
  rw [hc]
  change _ = (1-D*(goeMatrix r g-BA • (1 : Matrix ι ι ℝ))*D)-D*_*_*_*D+_
  have hrank' := congrArg (fun M => D*M*D) hrank
  simp only [Matrix.mul_assoc] at hrank'
  simp only [residualGramVector] at *
  rw [show D*conditionalColumns X (sqrt q • u) ((sqrt s)⁻¹ • Z)
        ((sqrt BA)⁻¹ • (goeMatrix r g*ᵥu-BA • u))*
        conditionalCoefficient j
          ((2*j*q-2*j*a/s+2*j*(a+B*q)/S+(ell-2*κ+1)*goeBilinear r u u g+2*BA*(κ-1))/q)
          j ((κ-1)*sqrt BA/sqrt q)*
        (conditionalColumns X (sqrt q • u) ((sqrt s)⁻¹ • Z)
          ((sqrt BA)⁻¹ • (goeMatrix r g*ᵥu-BA • u)))ᵀ*D=
        D*(j • vecMulVec X X+
          (2*j*q-2*j*a/s+2*j*(a+B*q)/S+(ell-2*κ+1)*goeBilinear r u u g) • vecMulVec u u+
          (j*sqrt (q/s)) • (vecMulVec u Z+vecMulVec Z u)+
          (κ-1) • (vecMulVec u (goeMatrix r g*ᵥu)+vecMulVec (goeMatrix r g*ᵥu) u))*D by
          simpa only [Matrix.mul_assoc] using hrank']
  unfold conditionalBlockMatrix
  rw [goeBlockResidual_expand]
  have he : vecMulVec u ((j*sqrt (q/s)) • Z-(j*a/s) • u)+
      vecMulVec ((j*sqrt (q/s)) • Z-(j*a/s) • u) u=
      (j*sqrt (q/s)) • (vecMulVec u Z+vecMulVec Z u)-(2*j*a/s) • vecMulVec u u := by
    ext i k
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,vecMulVec_apply,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hcombine : goeMatrix r g+
      (κ-1) • (vecMulVec u (goeMatrix r g*ᵥu)+vecMulVec (goeMatrix r g*ᵥu) u)+
      ((ell-2*κ+1)*goeBilinear r u u g) • vecMulVec u u+
      vecMulVec u ((j*sqrt (q/s)) • Z-(j*a/s) • u)+
      vecMulVec ((j*sqrt (q/s)) • Z-(j*a/s) • u) u=
      goeMatrix r g+(κ-1) • (vecMulVec u (goeMatrix r g*ᵥu)+vecMulVec (goeMatrix r g*ᵥu) u)+
      ((ell-2*κ+1)*goeBilinear r u u g) • vecMulVec u u+
      ((j*sqrt (q/s)) • (vecMulVec u Z+vecMulVec Z u)-(2*j*a/s) • vecMulVec u u) := by
    rw [← he]
    abel
  rw [hcombine]
  simp only [Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,Matrix.sub_mul,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_one,sub_smul,add_smul]
  abel
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators Matrix.Norms.Frobenius

def conditionalKappa (j : ℝ) (p : ScalarPoint) : ℝ := sqrt ((p.2.1+p.2.2^2)/scalarS j p)
def conditionalEll (j : ℝ) (p : ScalarPoint) : ℝ :=
  sqrt ((p.2.1+p.2.2^2)/(scalarS j p+j*scalarQMoment p.1))
def conditionalMeanData (j : ℝ) (p : ScalarPoint) (r : ℝ) :
    Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  conditionalMeanCoefficient j (scalarQMoment p.1) (scalarS j p)
    (scalarS j p+j*scalarQMoment p.1) (scalarA j p)
    (j*scalarBMoment p.1) (j*scalarBMoment p.1+r) (conditionalKappa j p)
def conditionalScalarData (j : ℝ) (p : ScalarPoint) :
    Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  conditionalScalarCoefficient (scalarQMoment p.1) (conditionalKappa j p) (conditionalEll j p)
def curveKappa (j t : ℝ) : ℝ := sqrt (t/scalarFixedPoint j t)
def curveCoefficient (j t : ℝ) : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  conditionalCoefficient j
    ((2*j*scalarQ j t+2*(j*scalarBMoment (scalarCurve j t))*(curveKappa j t-1))/scalarQ j t)
    j ((curveKappa j t-1)*sqrt (j*scalarBMoment (scalarCurve j t))/sqrt (scalarQ j t))

lemma conditionalKappa_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    conditionalKappa j (scalarCurve j t,t,0)=curveKappa j t := by
  simp only [conditionalKappa,curveKappa,scalarS_curve hj hj1 ht,zero_pow (by decide : 2 ≠ 0),add_zero]

lemma curveKappa_sq {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    curveKappa j t^2=1-j*scalarQ j t/scalarFixedPoint j t := by
  have hs := (scalar_fixed_pos hj hj1 ht).1
  unfold curveKappa
  rw [Real.sq_sqrt (div_nonneg ht.le hs.le)]
  have he := (scalarFixedPoint_spec hj hj1 ht.le).2
  change scalarFixedPoint j t=t+j*scalarQ j t at he
  field_simp
  linarith

lemma conditionalMeanData_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    conditionalMeanData j (scalarCurve j t,t,0) 0=curveCoefficient j t := by
  unfold conditionalMeanData curveCoefficient
  rw [scalarQMoment_curve hj hj1 ht.le,scalarS_curve hj hj1 ht.le,
    scalarA_curve hj hj1 ht,conditionalKappa_curve hj hj1 ht.le,add_zero]
  exact conditionalMeanCoefficient_equality (scalar_fixed_pos hj hj1 ht).1
    (scalar_fixed_pos hj hj1 ht).2 hj.le

lemma continuousAt_conditionalCoefficient {X : Type*} [TopologicalSpace X]
    {j a b c : X → ℝ} {x : X} (hj : ContinuousAt j x) (ha : ContinuousAt a x)
    (hb : ContinuousAt b x) (hc : ContinuousAt c x) :
    ContinuousAt (fun x=>conditionalCoefficient (j x) (a x) (b x) (c x)) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  cases i with
  | inl i => cases k with
    | inl k => fin_cases i <;> fin_cases k <;>
        simp only [conditionalCoefficient,fromBlocks_apply₁₁,Matrix.of_apply,Matrix.cons_val,Fin.reduceFinMk] <;> first | exact hj | exact ha | exact hb | exact continuousAt_const
    | inr k => fin_cases i <;> simp [conditionalCoefficient,conditionalCoupling] <;> first | exact hc | exact continuousAt_const
  | inr i => cases k with
    | inl k => fin_cases k <;> simp [conditionalCoefficient,conditionalCoupling] <;> first | exact hc | exact continuousAt_const
    | inr k => simp [conditionalCoefficient]; exact continuousAt_const

lemma continuousAt_conditionalMeanCoefficient {p : ℝ × (ℝ × (ℝ × (ℝ × (ℝ × (ℝ × ℝ)))))}
    (hq : 0 < p.1) (hs : p.2.1 ≠ 0) (hS : p.2.2.1 ≠ 0) (j : ℝ) :
    ContinuousAt (fun p : ℝ × (ℝ × (ℝ × (ℝ × (ℝ × (ℝ × ℝ))))) =>
      conditionalMeanCoefficient j p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        p.2.2.2.2.2.1 p.2.2.2.2.2.2) p := by
  have hq0 := hq.ne'
  have hsq := (sqrt_pos.mpr hq).ne'
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  cases i with
  | inl i => cases k with
    | inl k => fin_cases i <;> fin_cases k <;>
        simp only [conditionalMeanCoefficient,conditionalCoefficient,fromBlocks_apply₁₁,Matrix.of_apply,Matrix.cons_val,Fin.reduceFinMk] <;> fun_prop (disch := assumption)
    | inr k => fin_cases i <;> simp [conditionalMeanCoefficient,conditionalCoefficient,conditionalCoupling] <;> fun_prop (disch := assumption)
  | inr i => cases k with
    | inl k => fin_cases k <;> simp [conditionalMeanCoefficient,conditionalCoefficient,conditionalCoupling] <;> fun_prop (disch := assumption)
    | inr k => simp [conditionalMeanCoefficient,conditionalCoefficient]; fun_prop

lemma continuousAt_conditionalScalarCoefficient {p : ℝ × (ℝ × ℝ)} (hq : p.1 ≠ 0) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => conditionalScalarCoefficient p.1 p.2.1 p.2.2) p := by
  unfold conditionalScalarCoefficient conditionalCoefficient conditionalCoupling
  fun_prop (disch := assumption)

lemma continuousAt_conditionalData {X : Type*} [TopologicalSpace X]
    {R j : ℝ} (hR : 0 ≤ R) (f : X → ScalarPoint) (hf : Continuous f)
    (hdom : ∀ x,f x ∈ scalarMomentDomain R) (r : X → ℝ) (hr : Continuous r)
    {x : X} (hq : 0 < scalarQMoment (f x).1) (hs : 0 < scalarS j (f x))
    (hS : 0 < scalarS j (f x)+j*scalarQMoment (f x).1) :
    ContinuousAt (fun x=>conditionalMeanData j (f x) (r x)) x ∧
    ContinuousAt (fun x=>conditionalScalarData j (f x)) x := by
  have hcq : Continuous (fun x=>scalarQMoment (f x).1) := continuous_scalarQMoment.comp (continuous_fst.comp hf)
  have hcs : Continuous (fun x=>scalarS j (f x)) := (continuous_scalarS j).comp hf
  have hcS : Continuous (fun x=>scalarS j (f x)+j*scalarQMoment (f x).1) := hcs.add (continuous_const.mul hcq)
  have hca : Continuous (fun x=>scalarA j (f x)) := (continuousOn_scalarA hR j).comp_continuous hf hdom
  have hcb : Continuous (fun x=>j*scalarBMoment (f x).1) := continuous_const.mul (continuous_scalarBMoment.comp (continuous_fst.comp hf))
  have hcn : Continuous (fun x=>(f x).2.1+(f x).2.2^2) := by fun_prop
  have hk : ContinuousAt (fun x=>conditionalKappa j (f x)) x := (hcn.continuousAt.div hcs.continuousAt hs.ne').sqrt
  have hl : ContinuousAt (fun x=>conditionalEll j (f x)) x := (hcn.continuousAt.div hcS.continuousAt hS.ne').sqrt
  have hq' := hcq.continuousAt (x := x)
  have hs' := hcs.continuousAt (x := x)
  have hS' := hcS.continuousAt (x := x)
  have ha' := hca.continuousAt (x := x)
  have hb' := hcb.continuousAt (x := x)
  have hba := hb'.add hr.continuousAt
  have hM : ContinuousAt (fun x =>
      (2*j*scalarQMoment (f x).1-2*j*scalarA j (f x)/scalarS j (f x)+
        2*j*(scalarA j (f x)+j*scalarBMoment (f x).1*scalarQMoment (f x).1)/(scalarS j (f x)+j*scalarQMoment (f x).1)+
        2*(j*scalarBMoment (f x).1+r x)*(conditionalKappa j (f x)-1))/scalarQMoment (f x).1) x :=
    ((((continuousAt_const.mul hq').sub ((continuousAt_const.mul ha').div hs' hs.ne')).add
      ((continuousAt_const.mul (ha'.add (hb'.mul hq'))).div hS' hS.ne')).add
      ((continuousAt_const.mul hba).mul (hk.sub continuousAt_const))).div hq' hq.ne'
  have hN : ContinuousAt (fun x => (conditionalKappa j (f x)-1)*sqrt (j*scalarBMoment (f x).1+r x)/sqrt (scalarQMoment (f x).1)) x :=
    ((hk.sub continuousAt_const).mul hba.sqrt).div hq'.sqrt (sqrt_pos.mpr hq).ne'
  constructor
  · exact continuousAt_conditionalCoefficient continuousAt_const hM continuousAt_const hN
  · have hM' : ContinuousAt (fun x => (conditionalEll j (f x)-2*conditionalKappa j (f x)+1)/scalarQMoment (f x).1) x :=
      ((hl.sub (continuousAt_const.mul hk)).add continuousAt_const).div hq' hq.ne'
    exact continuousAt_conditionalCoefficient continuousAt_const hM' continuousAt_const continuousAt_const

lemma continuous_curve_statistics {j t0 T : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht0 : 0 < t0) :
    Continuous (fun t : Icc t0 T=>scalarFixedPoint j t) ∧
    Continuous (fun t : Icc t0 T=>scalarQ j t) ∧
    Continuous (fun t : Icc t0 T=>scalarBMoment (scalarCurve j t)) ∧
    Continuous (fun t : Icc t0 T=>scalarEMoment (scalarCurve j t)) ∧
    Continuous (fun t : Icc t0 T=>curveKappa j t) ∧
    Continuous (fun t : Icc t0 T=>curveCoefficient j t) := by
  let inc : Icc t0 T → Ici (0:ℝ) := fun t=>⟨t,ht0.le.trans t.2.1⟩
  have hi : Continuous inc := continuous_subtype_val.subtype_mk _
  have hs := (continuous_scalarFixedPoint_nonneg hj hj1).comp hi
  have hcurve := (continuous_scalarCurve_nonneg hj hj1).comp hi
  have hq : Continuous (fun t : Icc t0 T=>scalarQ j t) := by
    convert continuous_scalarQMoment.comp hcurve using 1
    funext t
    exact (scalarQMoment_curve hj hj1 (ht0.le.trans t.2.1)).symm
  have hb := continuous_scalarBMoment.comp hcurve
  have he := continuous_scalarEMoment.comp hcurve
  have hk : Continuous (fun t : Icc t0 T=>curveKappa j t) :=
    (continuous_subtype_val.div hs (fun t=>(scalar_fixed_pos hj hj1 (ht0.trans_le t.2.1)).1.ne')).sqrt
  refine ⟨hs,hq,hb,he,hk,?_⟩
  apply continuous_iff_continuousAt.mpr
  intro t
  have hqt : 0 < scalarQ j (t:ℝ) := (scalar_fixed_pos hj hj1 (ht0.trans_le t.2.1)).2
  have hq' := hq.continuousAt (x := t)
  have hb' := hb.continuousAt (x := t)
  have hk' := hk.continuousAt (x := t)
  have hM : ContinuousAt (fun t : Icc t0 T =>
      (2*j*scalarQ j t+2*(j*scalarBMoment (scalarCurve j t))*(curveKappa j t-1))/scalarQ j t) t :=
    ((continuousAt_const.mul hq').add
      ((continuousAt_const.mul (continuousAt_const.mul hb')).mul (hk'.sub continuousAt_const))).div hq' hqt.ne'
  have hN : ContinuousAt (fun t : Icc t0 T => (curveKappa j t-1)*sqrt (j*scalarBMoment (scalarCurve j t))/sqrt (scalarQ j t)) t :=
    ((hk'.sub continuousAt_const).mul (continuousAt_const.mul hb').sqrt).div hq'.sqrt (sqrt_pos.mpr hqt).ne'
  exact continuousAt_conditionalCoefficient continuousAt_const hM continuousAt_const hN
end SKGap
end
end

end OAI

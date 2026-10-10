import OAI.Geometry.Convex.GeneralMahler.Threshold

namespace OAI
/-! Primitive identities and notation for layer to spectral comparisons. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

lemma pj_sym (B A C:Mat m) : Pj B A C=Pj B C A := by simp only [Pj,jprod,add_comm]
lemma j_smul_left (A C:Mat m) (a:ℝ) : jprod (a•A) C=a•jprod A C := by
  simp only [jprod,smul_mul_assoc,mul_smul_comm,smul_add]; rw [smul_comm,smul_comm (1/2:ℝ) a]
lemma pj_norm {A B C:Mat m} :
    ‖Pj B A C‖ ≤ (‖etL B‖ * ‖A‖)*‖C‖ := by
  rw [Pj,← etL_apply]
  have h : ‖jprod A C‖≤‖A‖*‖C‖ := by
    unfold jprod; rw [norm_smul,Real.norm_of_nonneg (by norm_num)]
    have hh := norm_add_le (A*C) (C*A)
    linarith [norm_mul_le A C,norm_mul_le C A]
  apply ((etL B).le_opNorm _).trans
  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
lemma pj_scale (a b:ℝ) (B A C:Mat m) :
    Pj B (a•A) (b•C)=a*(b*Pj B A C) := by
  unfold Pj
  have h (x y:Mat m):jprod x y=jprod y x := by unfold jprod; rw [add_comm]
  rw [j_smul_left,h A,j_smul_left,h C]
  simp only [mul_smul_comm,trN_smul]

lemma mixed_proj {X Y E F:Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f:X→Y→E} (hf:mixed f) (l:E→L[ℝ]F) :
    mixed fun x y=> l (f x y) := by
  apply hf.product (g:=fun _ _=>‖l‖)
    (show PolyBound (fun _:X×Y=>‖l‖) from PolyBound.const _)
  intro x y
  calc
    _ ≤ ‖l‖*‖f x y‖ := l.le_opNorm _
    _ = _ := by rw [Real.norm_of_nonneg (norm_nonneg l),mul_comm]

namespace FieldMat
variable (B:FieldMat m)
def eVal (f:ℝ→ℝ) (z:ℝ) (x:Rn m) := B.eval f x-scalar m (f z)
lemma pEval {f} (hf:TestF f) : PolyBound (B.eVal f).uncurry :=
  (((B.eval_reg hf).p).comp PolyBound.snd).sub
    ((hf.poly.comp PolyBound.fst).smul (PolyBound.const _))
lemma smEval {f} (hf:TestF f) : StronglyMeasurable (B.eVal f).uncurry :=
  ((B.theta_gen_meas (f:=fun _ y=>f y) (hf.cont.measurable.comp measurable_snd)).stronglyMeasurable).sub
    (((hf.cont.comp continuous_fst).stronglyMeasurable).smul stronglyMeasurable_const)

def EC (v:Plane) (x:Rn m) := scalar m (jump v.2 v.1) - B.Θ v.2 x
lemma Em : StronglyMeasurable B.EC.uncurry :=
  ((jump_m.comp (measurable_swap.comp measurable_fst)).stronglyMeasurable.smul stronglyMeasurable_const).sub
    (B.thetaM.comp_measurable ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
lemma Ep : PolyBound B.EC.uncurry :=
  ((PolyBound.of_bound (f:=fun v:Plane × Rn m=>jump v.1.2 v.1.1) 1
    (fun v=>by unfold jump; split_ifs <;> simp)).smul (PolyBound.const _)).sub
    (PolyBound.of_bound (f:=fun v:Plane × Rn m=>B.Θ v.1.2 v.2) 1 (fun v=>B.theta_norm ..))

lemma vanishEC (x:Rn m) (u:Plane) (h: max ‖u.1‖ ‖B.A x‖ < ‖u.2‖) :
    B.EC u x=0 := by
  unfold EC
  obtain ⟨hv,hx⟩ := max_lt_iff.mp h
  have he := B.theta_exact u.2 x hx
  unfold QP at he; rw [sub_eq_zero.mp he]
  have ht : jump u.2 u.1=st u.2 := by
    simp only [Real.norm_eq_abs] at hv
    unfold jump st; split_ifs <;> grind
  rw [ht,scalar,sub_self]

lemma gapM (x:Rn m) (z:ℝ) {f:ℝ→ℝ} (hf:TestF f) :
    Integrable fun y:ℝ=> deriv f y • B.EC (z,y) x := by
  let g := fun y (_:ℝ)=> deriv f y • B.EC (z,y) x
  have hi : mixed g := by
    have hh : PolyBound (fun v:ℝ×ℝ=>B.EC (z,v.1) x) :=
      PolyBound.of_bound 2 fun v=> by
        have h := norm_sub_le (scalar m (jump v.1 z)) (B.Θ v.1 x)
        have hh : ‖scalar m (jump v.1 z)‖≤1 := by
          rcases subsingleton_or_nontrivial (Mat m) with h | h
          · have h0 : scalar m (jump v.1 z) = 0 := @Subsingleton.elim _ h _ 0
            rw [h0, norm_zero]
            exact zero_le_one
          · let : Nontrivial (Mat m) := h
            unfold jump scalar
            split <;> simp
        apply h.trans
        linarith [B.theta_norm v.1 x]
    apply mixed.of_cutoff (show PolyBound g.uncurry from (hf.der.poly.comp PolyBound.fst).smul hh)
      (PolyBound.const (X:=ℝ) (max ‖z‖ ‖B.A x‖))
    intro y w h; unfold g; rw [B.vanishEC _ _ h,smul_zero]
  apply mixed_integrable_left hi 0
  exact ((hf.der.cont.stronglyMeasurable).smul (B.Em.comp_measurable
    ((measurable_const.prodMk measurable_id).prodMk measurable_const))).aestronglyMeasurable

def LL (u:Frm m) : Mat m →L[ℝ] Mat m :=
  LinearMap.toContinuousLinearMap (𝕜:=ℝ) {
    toFun := u.loc
    map_add' := u.loc_add
    map_smul' := u.loc_smul }
lemma gap (x:Rn m) (z:ℝ) {f:ℝ→ℝ} (hf:TestF f) :
    B.eVal f z x= ∫ y,deriv f y • B.EC (z,y) x := by
  let u := B.Fr x
  let l := LL u
  let g := fun y=> deriv f y • B.EC (z,y) x
  have hi := B.gapM x z hf
  apply u.loc_inj
  rw [eVal,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.eval f x)= _ from B.evfrm x f]
  change _=l (∫ y,g y)
  rw [← l.integral_comp_comm hi]
  ext i j
  rw [show (∫ y,l (g y)) i j=∫ y,l (g y) i j from
    ((coeffMap i j).integral_comp_comm (l.integrable_comp hi)).symm]
  have he (y) : l (g y) = deriv f y • (scalar m (jump y z)-Matrix.diagonal (fun i=>jump y (B.ev x i))) := by
    change u.loc (deriv f y • (scalar m (jump y z)-B.Θ y x))=_
    rw [u.loc_smul,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.Θ y x)=_ from B.evfrm x (jump y)]
  simp_rw [he]
  by_cases h:i=j
  · subst j
    have ht (y) : (deriv f y • (scalar m (jump y z)-Matrix.diagonal (fun i=>jump y (B.ev x i)))) i i =
        ss f y (B.ev x i)-ss f y z := by
      simp [ss,score,scalar]; ring
    have hh (x) := centered_s hf x
    have hp (x:ℝ) : Integrable fun y=>ss f y x :=
      mixed_integrable_left (ss_m hf) x ((ss_sm f).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    simp_rw [ht]; rw [integral_sub (hp _) (hp _),hh,hh]; simp
  simp [scalar,h]

lemma nest (x:Rn m) (z y:ℝ) (hz:z≤y) :
    B.Θ z x* B.Θ y x=B.Θ z x ∧ B.Θ y x*B.Θ z x=B.Θ z x := by
  let u := B.Fr x
  have hi (t:ℝ) : u.loc (B.Θ t x)= Matrix.diagonal (fun i=>jump t (B.ev x i)) := B.evfrm x (jump t)
  constructor <;> apply u.loc_inj <;> rw [u.loc_mul] <;>
    simp only [hi,Matrix.diagonal_mul_diagonal] <;> congr 1 <;> funext i <;>
    unfold jump <;> split_ifs <;> grind
end FieldMat
end GeneralMahler

end

end OAI

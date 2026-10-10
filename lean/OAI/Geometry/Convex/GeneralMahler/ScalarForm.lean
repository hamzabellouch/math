import OAI.Geometry.Convex.GeneralMahler.Forms

namespace OAI
/-! Integrating functionals; ext modulo constants. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ} [NeZero m]
-- simple contractions
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)
def Iw (f:ℝ→ℝ) := ∫ x,q.layerW x*f x
def Idw (f:ℝ→ℝ) := ∫ x,q.dm x*f x

lemma dm_e {f:ℝ→ℝ} (hf:TestF f) : q.Idw f=q.Iw f-q.s0*ga f := by
  unfold Idw dm Iw ga; simp_rw [sub_mul,mul_assoc]
  rw [integral_sub (q.moment_w.int_test hf)
    (show Integrable (fun x=> q.s0*(phi x*f x)) from (ga_i hf).const_mul _),integral_const_mul]
lemma Id_add {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    q.Idw (fun x=>f x+g x)=q.Idw f+q.Idw g := by
  unfold Idw; simp_rw [mul_add]
  exact integral_add (q.dm_m.int_test hf) (q.dm_m.int_test hg)
lemma Id_sub {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    q.Idw (fun x=>f x-g x)=q.Idw f-q.Idw g := by
  unfold Idw; simp_rw [mul_sub]
  exact integral_sub (q.dm_m.int_test hf) (q.dm_m.int_test hg)
omit [NeZero m] in
lemma Id_cmul (c:ℝ) (f:ℝ→ℝ) :
    q.Idw (fun x=>c*f x)=c*q.Idw f := by
  unfold Idw; simp_rw [mul_left_comm (dm q _),integral_const_mul]
lemma Id_ext {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (he:deriv f=deriv g) :
    q.Idw f=q.Idw g := by unfold Idw; rw [q.hd_test hf,q.hd_test hg,he]
omit [NeZero m] in
lemma L_ext {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (he:deriv f=deriv g) :
    LDel B W f=LDel B W g := by
  let h := fun x=> f x-g x
  have ih := fun x=>((hf.diff x).hasDerivAt.fun_sub (hg.diff x).hasDerivAt)
  have hh (x) : HasDerivAt h 0 x := by
    have h := ih x; rw [he,sub_self] at h
    exact h
  have eq : h=fun x=> h 0 := by
    ext x
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=x)
      (f:=h) (f':=fun _=> (0:ℝ)) (fun x _=>hh x) (continuous_const.intervalIntegrable ..)
    simp only [intervalIntegral.integral_zero] at hi; exact sub_eq_zero.mp hi.symm
  have H : LDel B W h=0 := by
    unfold LDel etw et BDiff
    rw [eq,ga_const]
    simp [B.eval_const,trN]
  have hi := Delta_sub B W hf hg
  change LDel B W h=_ at hi; linarith
omit [NeZero m] in
lemma L_cmul (a:ℝ) {f:ℝ→ℝ} (hf:TestF f) :
    LDel B W (fun x=>a*f x)=a*LDel B W f := by
  unfold LDel etw et
  have hi (x) : BDiff B (fun x=>a*f x) x=a• BDiff B f x := by
    rw [BDiff,B.eval_scale hf,ga_mul]
    unfold scalar BDiff; module
  simp_rw [hi,mul_smul_comm,trN_smul,integral_const_mul]

omit [NeZero m] in
lemma L_formula {f:ℝ→ℝ} (hf:TestF f) :
    etw W (B.eval f) = LDel B W f+trN W*ga f := by
  unfold LDel etw et BDiff
  simp_rw [mul_sub,scalar,mul_smul_comm,mul_one,trN_sub,trN_smul]
  rw [integral_sub (int_etw W (B.eval_reg hf).ig) (integrable_const _)]
  simp; ring
omit [NeZero m] in
lemma delt_scale (f:ℝ→ℝ) (hf:TestF f) (c:ℝ) :
    q.delt (fun x=>c*f x) = c*q.delt f := by
  have he (x) := ((hf.diff x).hasDerivAt.const_mul c).deriv
  unfold delt
  simp_rw [he]
  rw [mul_neg, ← integral_const_mul]; congr 2; ext; ring

lemma ga_prod_comm (f g:ℝ→ℝ) : ga (fun x=>f x*g x)=ga (fun x=>g x*f x) := by
  congr 1; ext; ring
omit [NeZero m] in
lemma S0_e : trN q.covMat=q.s0 := rfl
end ProjField
end GeneralMahler

end

end OAI

import Mathlib
import OAI.Probability.SKGap.Matrix.NormalizedPrimaryRecipe
import OAI.Probability.SKGap.Stability.ImplicitPerturb
import OAI.Probability.SKGap.Localization.LiteralInitialRecipe

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

def initialU (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ) (r e : Fin n→ℝ) : VectorFields n :=
  fun x i=>f.eval (z x i) (r i) (a x)/phi (z x i) (r i) (a x)*e i

def initialP (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ) (r e : Fin n→ℝ) : VectorFields n :=
  fun x i=>(f.dz.eval (z x i) (r i) (a x)-logSlope (z x i) (r i) (a x)*f.eval (z x i) (r i) (a x))*e i

lemma ratio_dz_phi (f : KernelExpr) (z r a : ℝ) :
    phi z r a*((RatioExpr.kernel f).d .z).eval z r a=
      f.dz.eval z r a-logSlope z r a*f.eval z r a := by
  change phi z r a*(f.dz.eval z r a/phi z r a+
    -1*(f.eval z r a/phi z r a*(phiExpr.dz.eval z r a/phi z r a)))=_
  rw [phiExpr_dz,logSlope]
  field_simp [(phi_pos z r a).ne']
  ring

lemma initialP_ratio (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ) (r e : Fin n→ℝ) :
    initialP f z a r e=fun x i=>phi (z x i) (r i) (a x)*
      (((RatioExpr.kernel f).d .z).eval (z x i) (r i) (a x)*e i) := by
  ext x i
  rw [←mul_assoc,ratio_dz_phi]
  rfl

lemma literalInitial_partial_source (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n)
    (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x) :
    (literalInitial J j d f z m a c r e).implicitPartial y x=
      fun i=>logSlope (z x i) (r i) (a x)*w x i+initialP f z a r e x i := by
  ext i
  rw [literalInitial_partial _ _ _ _ _ _ _ _ _ _ _ hd,hw,literalInitial_source _ _ _ _ _ _ _ _ _ _ _ hd]
  dsimp only [initialP,logSlope]
  field_simp [(phi_pos (z x i) (r i) (a x)).ne']
  ring

lemma literalInitial_field (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
    (hc : c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x) :
    (literalInitial J j d f z m a c r e).fieldOf 1 (fun _=>w) (fun _=>y) x=
      fun i=>J.mulVec (w x) i-j*siteMean (fun x i=>phi (z x i) (r i) (a x)) x*w x i-j*c x*m x i := by
  ext i
  simp only [OrdinaryData.fieldOf,←hw,Fintype.sum_unique]
  change J.mulVec (w x) i-j*(siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x*m x i)-
    j*(siteMean ((literalInitial J j d f z m a c r e).implicitCoefficient) x*w x i)=_
  have he : (literalInitial J j d f z m a c r e).implicitCoefficient=fun x i=>phi (z x i) (r i) (a x) := by
    ext v k; exact literalInitial_coefficient ..
  rw [he,←hc]
  ring

lemma initial_scalar_equation (f : KernelExpr) (z w : VectorFields n)
    (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) :
    c x=(n:ℝ)⁻¹*inner ℝ (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)
        (WithLp.toLp 2 (w x))+siteMean (initialP f z a r e) x ↔
      c x=siteMean (fun x i=>logSlope (z x i) (r i) (a x)*w x i+initialP f z a r e x i) x := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,siteMean,
    Finset.sum_add_distrib,div_eq_mul_inv]
  simp [mul_comm,add_comm,mul_add]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma fixed_root_ratio_regular (f : RatioExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l : ι) (α : κ) (r : Fin n→ℝ) :
    SegmentRegular H θ (fun i u=>eval3 f.eval (phiSelect l α u+(0,(r i,0))))
      (fun i u=>(f.gradient (phiSelect l α u+(0,(r i,0)))).comp (phiSelect l α)) x
      (f.dBudget+f.ddBudget) := by
  have h:=phi_ratio_segmentRegular f H θ x (phiSelect l α) (fun i=>(0,(r i,0)))
  apply h.mono
  have h1:=phiSelect_norm l α
  have h2:=pow_le_pow_left₀ (norm_nonneg (phiSelect l α)) h1 2
  simpa only [mul_one,one_pow] using add_le_add
    (mul_le_mul_of_nonneg_left h1 f.dBudget_nonneg)
    (mul_le_mul_of_nonneg_left h2 f.ddBudget_nonneg)

lemma SegmentRegular.coefficientBound {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {L A T : ℝ} (h : SegmentRegular H θ F F' x L)
    (hA : 0≤A) (hT : 0≤T) (ha : ∀i,|F i (localArgs H θ x i)|≤A)
    (hD : (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)≤T) :
    CoefficientBound (coefficient H θ F) x A (L*T) := by
  refine ⟨hA,mul_nonneg h.nonneg hT,ha,?_⟩
  intro i
  have hr:=(coefficient_row_bound H θ F F' x i h.nonneg (h.deriv i) (h.bound i)).trans
    (mul_le_mul_of_nonneg_left hD h.nonneg)
  simpa only [vectorNorm_sq] using pow_le_pow_left₀ (vectorNorm_nonneg _) hr 2

lemma fixed_root_kernel_coefficientBound (f : KernelExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l : ι) (α : κ) (r : Fin n→ℝ)
    {R T : ℝ} (hT : 0≤T) (hx : |θ α x|≤R) (hf : ∀k,|θ α (flip x k)|≤R)
    (hD : (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)≤T) :
    CoefficientBound (fun y i=>f.eval (H l y i) (r i) (θ α y)) x
      (f.mass*Real.exp (R/2)) ((f.dBudget R+f.ddBudget R)*T) := by
  have h:=fixed_root_kernel_regular f H θ x l α r R hx hf
  have hb:=h.coefficientBound (mul_nonneg f.mass_nonneg (Real.exp_pos _).le) hT
    (fun i=>f.absolute_bound (R:=R) (x:=phiSelect l α (localArgs H θ x i)+(0,(r i,0)))
      (by simpa [strip,phiSelect,localArgs] using hx)) hD
  simp only [eval3,phiSelect_apply,Prod.fst_add,Prod.snd_add,zero_add,add_zero] at hb
  exact hb

lemma fixed_root_ratio_coefficientBound (f : RatioExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l : ι) (α : κ) (r : Fin n→ℝ)
    {T : ℝ} (hT : 0≤T)
    (hD : (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)≤T) :
    CoefficientBound (fun y i=>f.eval (H l y i) (r i) (θ α y)) x
      f.mass ((f.dBudget+f.ddBudget)*T) := by
  have h:=fixed_root_ratio_regular f H θ x l α r
  have hb:=h.coefficientBound f.mass_nonneg hT (fun i=>f.bounded _ _ _) hD
  simp only [eval3,phiSelect_apply,Prod.fst_add,Prod.snd_add,zero_add,add_zero] at hb
  exact hb
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem
variable {n : ℕ}

def kernelSmallBudget (f : KernelExpr) (R T : ℝ) : ℝ :=
  f.mass*Real.exp (R/2)+3*((f.dBudget R+f.ddBudget R)*T)
def ratioSmallBudget (f : RatioExpr) (T : ℝ) : ℝ :=
  f.mass+3*((f.dBudget+f.ddBudget)*T)
lemma kernelSmallBudget_nonneg (f : KernelExpr) (R T : ℝ) (hT : 0≤T) :
    0≤kernelSmallBudget f R T := by
  exact add_nonneg (mul_nonneg f.mass_nonneg (Real.exp_pos _).le)
    (mul_nonneg (by norm_num) (mul_nonneg (add_nonneg (f.dBudget_nonneg _) (f.ddBudget_nonneg _)) hT))
lemma ratioSmallBudget_nonneg (f : RatioExpr) (T : ℝ) (hT : 0≤T) :
    0≤ratioSmallBudget f T := by
  exact add_nonneg f.mass_nonneg
    (mul_nonneg (by norm_num) (mul_nonneg (add_nonneg f.dBudget_nonneg f.ddBudget_nonneg) hT))

lemma initial_kernel_bound (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r : Fin n→ℝ) (x : Spin n) {R T : ℝ} (hT : 0≤T)
    (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    CoefficientBound (fun v i=>f.eval (z v i) (r i) (a v)) x
      (f.mass*Real.exp (R/2)) ((f.dBudget R+f.ddBudget R)*T) := by
  apply fixed_root_kernel_coefficientBound f (fun _ : Unit=>z) (fun _ : Unit=>a) x () () r hT ha haf
  simpa only [Fintype.sum_unique] using hD

lemma initial_ratio_bound (f : RatioExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r : Fin n→ℝ) (x : Spin n) {T : ℝ} (hT : 0≤T)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    CoefficientBound (fun v i=>f.eval (z v i) (r i) (a v)) x
      f.mass ((f.dBudget+f.ddBudget)*T) := by
  apply fixed_root_ratio_coefficientBound f (fun _ : Unit=>z) (fun _ : Unit=>a) x () () r hT
  simpa only [Fintype.sum_unique] using hD

lemma initialU_small (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) {T : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    SmallBound (initialU f z a r e) x (ratioSmallBudget (.kernel f) T) := by
  have H:=(initial_ratio_bound (.kernel f) z a r x hT hD).small_product ((SmallBound.seed e x).mono he)
  simp only [one_mul] at H
  convert! H using 1

lemma initialP_small (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) {R T : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
    (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    SmallBound (initialP f z a r e) x
      (ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T) := by
  have hu:=(initial_ratio_bound ((RatioExpr.kernel f).d .z) z a r x hT hD).small_product ((SmallBound.seed e x).mono he)
  simp only [one_mul] at hu
  have hp:=(initial_kernel_bound phiExpr z a r x hT ha haf hD).small_product hu
  rw [initialP_ratio]
  convert! hp using 1
  ext v i
  rw [phiExpr,KernelExpr.eval,moment_base]

lemma scaledMean_norm (hn : 0<n) (U : VectorFields n) (x : Spin n) {C : ℝ}
    (hU : SmallBound U x C) :
    Real.sqrt (n:ℝ)*|siteMean U x|≤C ∧
      Real.sqrt (n:ℝ)*‖derivativeVector (siteMean U) x‖≤C := by
  constructor
  · have H:=scaledMean_size hn U x hU.nonneg hU.size
    simpa only [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] using H
  · apply nonneg_le_nonneg_of_sq_le_sq hU.nonneg
    simp only [←sq]
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
    exact siteMean_derivative_square_bound hn ((Primary.opNorm_le_frobenius _).trans hU.derivative)

lemma logSlope_ratio (z r a : ℝ) :
    logSlope z r a=(RatioExpr.kernel phiExpr.dz).eval z r a := by
  rw [RatioExpr.eval,phiExpr_dz,logSlope]

end SKGapCutoff.Recipe

end
end

end OAI

import Mathlib
import OAI.Probability.SKGap.Localization.LiteralInitialRecipe
import OAI.Probability.SKGap.Localization.ResidualAdmissibility

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma SegmentRegular.const_mul {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {C : ℝ} (h : SegmentRegular H θ F F' x C) (b : ℝ) :
    SegmentRegular H θ (fun i u=>b*F i u) (fun i u=>b • F' i u) x (|b| *C) := by
  refine ⟨mul_nonneg (abs_nonneg _) h.nonneg,?_,?_,?_⟩
  · intro i k t ht; exact (h.deriv i k t ht).const_mul b
  · intro i k t ht
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (h.bound i k t ht) (abs_nonneg _)
  · intro i k t ht
    rw [←smul_sub b (F' i _) (F' i _),norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (h.lip i k t ht) (abs_nonneg _)).trans_eq (by ring)

omit [DecidableEq ι] [DecidableEq κ] in
lemma parameter_regular (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (α : κ) :
    SegmentRegular H θ (fun _ u=>u (.inr α))
      (fun _ _=>ContinuousLinearMap.proj (.inr α)) x 1 := by
  refine ⟨by norm_num,?_,?_,?_⟩
  · intro i k t ht; exact (ContinuousLinearMap.proj (Sum.inr α : ι ⊕ κ) : Args (ι:=ι) (κ:=κ) →L[ℝ] ℝ).hasFDerivAt
  · intro i k t ht
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    simpa using norm_le_pi_norm u (.inr α)
  · intro i k t ht; simp

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma parameter_segment_value (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n)
    (α : κ) {B : ℝ} (hx : |θ α x|≤B) (hf : ∀k,|θ α (flip x k)|≤B)
    (i k : Fin n) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    |(localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)) (.inr α)|≤B := by
  change |θ α x+t*(θ α (flip x k)-θ α x)|≤B
  have hx' := abs_le.mp hx
  have hf' := abs_le.mp (hf k)
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hf'.1),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hx'.1)]
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hf'.2),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hx'.2)]

lemma initialKernel_regular (f : KernelExpr) (H : Unit→VectorFields n)
    (θ : Bool→Spin n→ℝ) (x : Spin n) (r : Fin n→ℝ) (R : ℝ)
    (hx : |θ false x|≤R) (hf : ∀k,|θ false (flip x k)|≤R) :
    SegmentRegular H θ (fun i=>initialKernel f (r i))
      (fun i=>initialGradient f (r i)) x (f.dBudget R+f.ddBudget R) := by
  convert fixed_root_kernel_regular f H θ x () false r R hx hf using 1
  · ext i u; simp [initialKernel,phiSelect_apply,eval3]
  · rfl

lemma initialKernel_segment_value (f : KernelExpr) (H : Unit→VectorFields n)
    (θ : Bool→Spin n→ℝ) (x : Spin n) (r : Fin n→ℝ) (R : ℝ)
    (hx : |θ false x|≤R) (hf : ∀k,|θ false (flip x k)|≤R)
    (i k : Fin n) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    |initialKernel f (r i) (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))|≤
      f.mass*Real.exp (R/2) := by
  change |eval3 f.eval (_, r i, _)| ≤ _
  apply f.absolute_bound
  exact parameter_segment_value H θ x false hx hf i k t ht

def initialRegularBudget (f : KernelExpr) (j R B : ℝ) : ℝ :=
  f.dBudget R+f.ddBudget R+(phiExpr.dBudget R+phiExpr.ddBudget R)+
    |j| *(B*(phiExpr.dBudget R+phiExpr.ddBudget R)+phiExpr.mass*Real.exp (R/2)+
      2*(phiExpr.dBudget R+phiExpr.ddBudget R))

lemma literalInitial_regular (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    {R B : ℝ} (hB : 0≤B) (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hc : |d*c x|≤B) (hcf : ∀k,|d*c (flip x k)|≤B) :
    let D:=literalInitial J j d f z m a c r e
    (∀s,SegmentRegular D.H D.θ (D.seedFunction 1 s) (D.seedDerivative 1 s) x
      (initialRegularBudget f j R B)) ∧
    SegmentRegular D.H D.θ (D.auxFunction 1 0) (D.auxDerivative 1 0) x
      (initialRegularBudget f j R B) := by
  let D:=literalInitial J j d f z m a c r e
  have hp:=initialKernel_regular phiExpr D.H D.θ x r R ha haf
  have hF:=initialKernel_regular f D.H D.θ x r R ha haf
  have hT:=parameter_regular D.H D.θ x true
  have hm:=hT.mul hp hB (mul_nonneg phiExpr.mass_nonneg (Real.exp_pos _).le)
    (parameter_segment_value D.H D.θ x true hc hcf)
    (initialKernel_segment_value phiExpr D.H D.θ x r R ha haf)
  have hm':=hm.const_mul (-j)
  simp only [abs_neg,mul_one] at hm'
  have hphi : 0≤phiExpr.dBudget R+phiExpr.ddBudget R:=add_nonneg (phiExpr.dBudget_nonneg _) (phiExpr.ddBudget_nonneg _)
  have hf0 : 0≤f.dBudget R+f.ddBudget R:=add_nonneg (f.dBudget_nonneg _) (f.ddBudget_nonneg _)
  have he : 0≤|j| *(B*(phiExpr.dBudget R+phiExpr.ddBudget R)+phiExpr.mass*Real.exp (R/2)+
      2*(phiExpr.dBudget R+phiExpr.ddBudget R)):=by positivity [phiExpr.mass_nonneg]
  constructor
  · intro s
    cases s
    · exact hF.mono (by dsimp [initialRegularBudget]; linarith)
    · convert hm'.mono (show |j| *(B*(phiExpr.dBudget R+phiExpr.ddBudget R)+phiExpr.mass*Real.exp (R/2)+
          2*(phiExpr.dBudget R+phiExpr.ddBudget R))≤ initialRegularBudget f j R B by
          dsimp [initialRegularBudget]; linarith) using 1
      · ext i u
        dsimp [D,literalInitial]
        ring
      · rfl
  · exact hp.mono (by dsimp [initialRegularBudget]; linarith)
end SKGapCutoff.Recipe

end
end

end OAI

import Mathlib
import OAI.Probability.SKGap.Localization.RecipeCoefficientClosure

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma two_field_kernel_value (f : KernelExpr) (H : ι→VectorFields n)
    (θ : κ→Spin n→ℝ) (x : Spin n) (l m : ι) (α : κ) (R : ℝ)
    (hx : |θ α x|≤R) (hf : ∀k,|θ α (flip x k)|≤R) :
    SegmentValue H θ (fun _ u=>eval3 f.eval (phiPairSelect l m α u)) x (f.mass*Real.exp (R/2)) := by
  intro i k t ht
  apply f.absolute_bound
  have hb : phiPairSelect l m α (localArgs H θ x i)∈strip R := by
    simpa [strip,phiPairSelect,localArgs] using hx
  have he : phiPairSelect l m α (localArgs H θ (flip x k) i)∈strip R := by
    simpa [strip,phiPairSelect,localArgs] using hf k
  have := (convex_strip R).add_smul_sub_mem hb he ht
  simpa only [map_add,map_smul,map_sub] using this

def steinCoefficientBudget (R : ℝ) : ℝ :=
  let f:=KernelExpr.atom 0 0 false
  f.mass*Real.exp (R/2)+f.dBudget R+f.ddBudget R
lemma steinCoefficientBudget_nonneg (R : ℝ) : 0 ≤ steinCoefficientBudget R := by
  have h0:= (KernelExpr.atom 0 0 false).mass_nonneg
  have h1:= (KernelExpr.atom 0 0 false).dBudget_nonneg R
  have h2:= (KernelExpr.atom 0 0 false).ddBudget_nonneg R
  unfold steinCoefficientBudget
  positivity

namespace OrdinaryData
omit [Fintype σ] in
lemma CoefficientClass.appendStein {D : OrdinaryData n ι κ σ} {N : ℕ} {x : Spin n} {K : ℝ}
    (h : D.CoefficientClass N x K) (l m : ι) (α : κ) (R : ℝ)
    (hx : |D.θ α x|≤R) (hf : ∀k,|D.θ α (flip x k)|≤R) :
    (D.appendStein N l m α).CoefficientClass (N+1) x (K+4*steinCoefficientBudget R*K) := by
  apply h.appendProduct (steinCoefficientBudget_nonneg R)
  · apply (two_field_kernel_regular (KernelExpr.atom 0 0 false) D.H D.θ x l m α R hx hf).mono
    exact le_add_of_nonneg_left (mul_nonneg (KernelExpr.atom 0 0 false).mass_nonneg (Real.exp_pos _).le) |>.trans_eq (by unfold steinCoefficientBudget; ring)
  · intro i k t ht
    exact (two_field_kernel_value (KernelExpr.atom 0 0 false) D.H D.θ x l m α R hx hf i k t ht).trans
      (by unfold steinCoefficientBudget; linarith [(KernelExpr.atom 0 0 false).dBudget_nonneg R,(KernelExpr.atom 0 0 false).ddBudget_nonneg R])
end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI

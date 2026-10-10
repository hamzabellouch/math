import OAI.Geometry.PolarProducts.Model

namespace OAI

universe u1 u2

section LowerBoundInline

open Set Filter Function
open scoped Topology ContDiff NNReal

namespace SmoothContraction

variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable section

def fixedPoint {f : E × F → F} {L : ℝ≥0}
    (hL : L < 1) (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (x : E) : F :=
  ContractingWith.fixedPoint (fun y => f (x, y)) ⟨hL, hLip x⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedSpace ℝ F] in
theorem fixedPoint_eq {f : E × F → F} {L : ℝ≥0}
    (hL : L < 1) (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (x : E) :
    f (x, fixedPoint hL hLip x) = fixedPoint hL hLip x :=
  (show ContractingWith L (fun y => f (x, y)) from ⟨hL, hLip x⟩).fixedPoint_isFixedPt

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedSpace ℝ F] in
theorem eq_fixedPoint {f : E × F → F} {L : ℝ≥0}
    (hL : L < 1) (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (x : E) {y : F}
    (hy : f (x, y) = y) : y = fixedPoint hL hLip x :=
  (show ContractingWith L (fun y => f (x, y)) from ⟨hL, hLip x⟩).fixedPoint_unique hy

omit [CompleteSpace E] in

theorem partial_isInvertible {f : E × F → F} {L : ℝ≥0}
    (hf : Differentiable ℝ f) (hL : L < 1)
    (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (u : E × F) :
    ((fderiv ℝ (fun p : E × F => p.2 - f p) u).comp
      (ContinuousLinearMap.inr ℝ E F)).IsInvertible := by
  let A := (fderiv ℝ f u).comp (ContinuousLinearMap.inr ℝ E F)
  have hA : HasFDerivAt (fun y => f (u.1, y)) A u.2 :=
    (hf u).hasFDerivAt.comp u.2 (hasFDerivAt_prodMk_right u.1 u.2)
  have hnorm : ‖A‖ < 1 := by
    rw [← hA.fderiv]
    exact (norm_fderiv_le_of_lipschitz ℝ (hLip u.1)).trans_lt (by exact_mod_cast hL)
  have heq : (fderiv ℝ (fun p : E × F => p.2 - f p) u).comp
      (ContinuousLinearMap.inr ℝ E F) = 1 - A := by
    change (fderiv ℝ (Prod.snd - f) u).comp _ = _
    rw [(hasFDerivAt_snd.sub (hf u).hasFDerivAt).fderiv]
    ext y
    simp [A]
  rw [heq]
  obtain ⟨v, hv⟩ := isUnit_one_sub_of_norm_lt_one hnorm
  exact ⟨ContinuousLinearEquiv.ofUnit v, hv⟩

theorem contDiff_fixedPoint {f : E × F → F} {L : ℝ≥0}
    (hf : ContDiff ℝ ∞ f) (hL : L < 1)
    (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) :
    ContDiff ℝ ∞ (fixedPoint hL hLip) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let y := fixedPoint hL hLip x
  let g : E × F → F := fun p => p.2 - f p
  have hg : ContDiffAt ℝ ∞ g (x, y) := (contDiff_snd.sub hf).contDiffAt
  have hi := partial_isInvertible (hf.differentiable (by simp)) hL hLip (x, y)
  let ψ := hg.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ x := hg.contDiffAt_implicitFunction (by simp) hi
  have hzero : g (x, y) = 0 := sub_eq_zero.mpr (fixedPoint_eq hL hLip x).symm
  have hnear : ψ =ᶠ[𝓝 x] fixedPoint hL hLip := by
    filter_upwards [hg.eventually_apply_implicitFunction (by simp) hi] with x' hx'
    apply eq_fixedPoint hL hLip x'
    have : g (x', ψ x') = 0 := hx'.trans hzero
    exact (sub_eq_zero.mp this).symm
  exact hψ.congr_of_eventuallyEq hnear.symm

end
end SmoothContraction

end LowerBoundInline

end OAI

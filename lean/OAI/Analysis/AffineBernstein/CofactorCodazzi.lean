import Mathlib
import OAI.Analysis.AffineBernstein.PiolaAlgebra

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_adjugate_entries (M : E → Matrix ι ι ℝ) (x : E)
    (hM : ∀ l m, DifferentiableAt ℝ (fun y => M y l m) x) (i j : ι) (v : E) :
    fderiv ℝ (fun y => (M y).adjugate j i) x v =
      ∑ l, (((M x).updateRow i (Pi.single j 1)).updateRow l
        (if l = i then 0 else fun m => fderiv ℝ (fun y => M y l m) x v)).det := by
  let N : E → (ι → ι → ℝ) := fun y =>
    Function.update (fun l m => M y l m) i (Pi.single j 1)
  let D : E →L[ℝ] (ι → ι → ℝ) := ContinuousLinearMap.pi fun l =>
    if l = i then 0 else ContinuousLinearMap.pi fun m => fderiv ℝ (fun y => M y l m) x
  have hD : HasFDerivAt N D x := by
    dsimp [N, D]
    apply hasFDerivAt_pi.mpr
    intro l
    by_cases hli : l = i
    · subst l
      simp only [Function.update_self, ite_true]
      exact hasFDerivAt_const (Pi.single j 1) x
    · simp only [Function.update_of_ne hli, ite_eq_right hli]
      exact hasFDerivAt_pi.mpr (fun m => (hM l m).hasFDerivAt)
  have hAdj : (fun y => (M y).adjugate j i) = continuousDetRows ∘ N := by
    funext y
    rw [Matrix.adjugate_apply]
    rfl
  have hc := (continuousDetRows.hasFDerivAt (N x)).comp x hD
  rw [hAdj, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hli : l = i
  · subst l
    simp only [D, ContinuousLinearMap.pi_apply, ite_true, zero_apply]
    rfl
  · simp only [D, ContinuousLinearMap.pi_apply, ite_eq_right hli]
    rfl

/- Cofactor divergence vanishes for every differentiable Codazzi matrix field,
including size one and the empty angular block. No invertibility is required. -/
theorem cofactor_divergence_of_codazzi (M : E → Matrix ι ι ℝ) (x : E) (e : ι → E)
    (hM : ∀ l m, DifferentiableAt ℝ (fun y => M y l m) x)
    (hCodazzi : ∀ l j m, fderiv ℝ (fun y => M y l m) x (e j) =
      fderiv ℝ (fun y => M y l j) x (e m)) (i : ι) :
    (∑ j, fderiv ℝ (fun y => (M y).adjugate j i) x (e j)) = 0 := by
  simp_rw [fderiv_adjugate_entries M x hM]
  exact piola_cancel (M x) i (fun l j m => fderiv ℝ (fun y => M y l m) x (e j)) hCodazzi

end AffineBernstein
end

end OAI

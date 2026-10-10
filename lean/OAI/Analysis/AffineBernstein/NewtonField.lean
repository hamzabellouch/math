import Mathlib
import OAI.Analysis.AffineBernstein.NewtonTensor
import OAI.Analysis.AffineBernstein.NewtonPiola

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_newtonTensor_entry (A V : ι → ι → ℝ) (i j : ι) :
    fderiv ℝ (fun B : ι → ι → ℝ => newtonTensor (Matrix.of B) i j) A V =
      fderiv ℝ (fderiv ℝ (fun B : ι → ι → ℝ => (Matrix.of B).adjugate i j)) A V
        (fun l m => (1 : Matrix ι ι ℝ) l m) := by
  let G : (ι → ι → ℝ) → ℝ := fun B => (Matrix.of B).adjugate i j
  let I : ι → ι → ℝ := fun l m => (1 : Matrix ι ι ℝ) l m
  have hd : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) A) A :=
    (((contDiff_adjugate_entry i j).fderiv_right (m := ∞) (by simp)).differentiable
      (by simp) A).hasFDerivAt
  have hh := hd.clm_apply (hasFDerivAt_const I A)
  have he : (fun B : ι → ι → ℝ => newtonTensor (Matrix.of B) i j) =
      fun B => fderiv ℝ G B I := rfl
  rw [he, hh.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add]
  rfl

/- Newton divergence for a genuine differentiable Codazzi field in constant
coordinates. Its sole tensor hypothesis is the third derivative symmetry. -/
theorem newtonTensor_divergence_of_codazzi (M : E → Matrix ι ι ℝ) (x : E) (e : ι → E)
    (hM : ∀ l m, DifferentiableAt ℝ (fun y => M y l m) x)
    (hCodazzi : ∀ l j m, fderiv ℝ (fun y => M y l m) x (e j) =
      fderiv ℝ (fun y => M y l j) x (e m)) (i : ι) :
    (∑ j, fderiv ℝ (fun y => newtonTensor (M y) j i) x (e j)) = 0 := by
  let B : E → ι → ι → ℝ := fun y l m => M y l m
  have hdB : DifferentiableAt ℝ B x := differentiableAt_pi.mpr fun l =>
    differentiableAt_pi.mpr (hM l)
  have he (j : ι) : fderiv ℝ (fun y => newtonTensor (M y) j i) x (e j) =
      fderiv ℝ (fderiv ℝ (fun A : ι → ι → ℝ => (Matrix.of A).adjugate j i)) (B x)
        (fun l m => fderiv ℝ (fun y => M y l m) x (e j))
        (fun l m => (1 : Matrix ι ι ℝ) l m) := by
    have hη (y : E) : Matrix.of (B y) = M y := by ext l m; rfl
    have hc := ((contDiff_newtonTensor_entry j i).differentiable (by simp) (B x)).hasFDerivAt.comp x
      hdB.hasFDerivAt
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L (e j)) hc.fderiv
    simp only [Function.comp_def, hη, ContinuousLinearMap.comp_apply] at hh
    let D : E →L[ℝ] (ι → ι → ℝ) := ContinuousLinearMap.pi fun l =>
      ContinuousLinearMap.pi fun m => fderiv ℝ (fun y => M y l m) x
    have hBD : HasFDerivAt B D x := hasFDerivAt_pi.mpr fun l =>
      hasFDerivAt_pi.mpr fun m => (hM l m).hasFDerivAt
    rw [hh, fderiv_newtonTensor_entry, hBD.fderiv]
    rfl
  simp_rw [he]
  apply newton_linear_piola (B x) (fun j l m => fderiv ℝ (fun y => M y l m) x (e j))
  intro l j m
  exact hCodazzi l j m

end AffineBernstein
end

end OAI

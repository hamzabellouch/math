import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.Adjugate
import OAI.Geometry.NodalSets.Elliptic.ContravariantPullback

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

def jacobian (F : Coord → Coord) (x : Coord) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ (fderiv ℝ F x (Pi.single j 1)) i

lemma jacobian_smooth (F : Coord → Coord) (hF : ContDiff ℝ ∞ F) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ jacobian F x i j) :=
  (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const)

lemma jacobian_closed (F : Coord → Coord) (hF : ContDiff ℝ ∞ F)
    (x : Coord) (a i j : Fin 4) :
    fderiv ℝ (fun z ↦ jacobian F z a j) x (Pi.single i 1) =
      fderiv ℝ (fun z ↦ jacobian F z a i) x (Pi.single j 1) := by
  have hd := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have he (k : Fin 4) : fderiv ℝ (fun z ↦ jacobian F z a k) x =
      (ContinuousLinearMap.proj a : Coord →L[ℝ] ℝ).comp
        ((fderiv ℝ (fun z ↦ fderiv ℝ F z) x).flip (Pi.single k 1)) := by
    change fderiv ℝ ((ContinuousLinearMap.proj a : Coord →L[ℝ] ℝ) ∘
      (fun z ↦ fderiv ℝ F z (Pi.single k 1))) x = _
    rw [fderiv_comp x (ContinuousLinearMap.proj a : Coord →L[ℝ] ℝ).differentiableAt
      (hd.clm_apply (differentiableAt_const _)), ContinuousLinearMap.fderiv]
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [he,he]
  exact congrArg (fun v : Coord ↦ v a)
    (hF.contDiffAt.isSymmSndFDerivAt (by simp) (Pi.single i 1) (Pi.single j 1))

lemma clm_coord_sum (L : Coord →L[ℝ] ℂ) (v : Coord) :
    L v = ∑ j : Fin 4, (v j : ℂ) * L (Pi.single j 1) := by
  have hv : v = ∑ j : Fin 4, v j • Pi.single j (1:ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, Complex.real_smul]

lemma coordPartial_comp (F : Coord → Coord) (x : Coord)
    (hF : DifferentiableAt ℝ F x) (u : Coord → ℂ)
    (hu : DifferentiableAt ℝ u (F x)) (i : Fin 4) :
    coordPartial i (u ∘ F) x =
      ∑ j : Fin 4, (jacobian F x j i : ℂ) * coordPartial j u (F x) := by
  unfold coordPartial
  rw [fderiv_comp x hu hF]
  exact clm_coord_sum (fderiv ℝ u (F x)) (fderiv ℝ F x (Pi.single i 1))

lemma coordPartial_sum_at (f : Fin 4 → Coord → ℂ) (x : Coord)
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (i : Fin 4) :
    coordPartial i (fun z ↦ ∑ j, f j z) x = ∑ j, coordPartial i (f j) x := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun j _ ↦ hf j)]
  simp

lemma adjugate_entry_smooth (F : Coord → Coord) (hF : ContDiff ℝ ∞ F) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun z ↦ (jacobian F z).adjugate i j) := by
  simp only [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three,
    Matrix.submatrix_apply]
  have hJ := jacobian_smooth F hF
  fun_prop

end
end Yau.Geometry

end OAI

import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicSquare
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace OAI

/-! # Directional differentiation commutes with the Euclidean Laplacian -/

open Set Metric InnerProductSpace Laplacian
open scoped ContDiff BigOperators
noncomputable section
namespace RegularPointCoordinates

theorem second_directional_symmetric {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (x v w : Euclidean n) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hsym : ((fderiv ℝ (fderiv ℝ f) x) w) v =
      ((fderiv ℝ (fderiv ℝ f) x) v) w :=
    (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)) w v
  simpa [fderiv_clm_apply hd (differentiableAt_const _)] using hsym

theorem laplacian_directional_commute {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 3 f) (x v : Euclidean n) :
    (Δ (fun y => fderiv ℝ f y v)) x = fderiv ℝ (Δ f) x v := by
  classical
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hd (w : Euclidean n) : ContDiff ℝ 2 (fun y => fderiv ℝ f y w) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  rw [laplacian_eq_sum_second_directional (hd v),
    laplacian_eq_sum_second_directional hf2]
  have hdd (i : Fin n) : DifferentiableAt ℝ
      (fun y => fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) y
        (EuclideanSpace.single i 1)) x :=
    (((hd _).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num) x
  rw [fderiv_fun_sum (fun i _ => hdd i), sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y (EuclideanSpace.single i 1)) =
      (fun y => fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) y v) :=
    funext fun y => second_directional_symmetric hf2 y v _
  rw [he]
  exact second_directional_symmetric (hd _) x v _

end RegularPointCoordinates

end

end OAI

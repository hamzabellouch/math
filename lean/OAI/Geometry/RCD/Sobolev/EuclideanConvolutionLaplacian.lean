import OAI.Geometry.RCD.Metric.EuclideanGreenIdentity
import OAI.Geometry.RCD.Coordinates.GevreyConvolution

namespace OAI

/-! # Differentiating the compact factor in Euclidean scalar convolution -/

open Set MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff Convolution
noncomputable section
namespace RegularPointCoordinates

theorem scalar_convolution_directional {n : ℕ} {f g : Euclidean n → ℝ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (v : Euclidean n) :
    (fun x => fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g) x v)=
      f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] (fun x => fderiv ℝ g x v) := by
  funext x
  rw [(hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hg x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hgc.fderiv ℝ)
    (hg.continuous_fderiv (by norm_num)) x v

theorem scalar_convolution_laplacian {n : ℕ} {f g : Euclidean n → ℝ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Δ (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g)=
      f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] (Δ g) := by
  classical
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hconv : ContDiff ℝ 2 (f ⋆[L,volume] g) := hgc.contDiff_convolution_right L hf hg
  rw [laplacian_eq_sum_second_directional hconv]
  funext x
  have hsecond (v : Euclidean n) :
      (fun x => fderiv ℝ (fun y => fderiv ℝ (f ⋆[L,volume] g) y v) x v)=
        f ⋆[L,volume] (fun x => fderiv ℝ (fun y => fderiv ℝ g y v) x v) := by
    rw [scalar_convolution_directional hf (hg.of_le (by norm_num)) hgc v]
    exact scalar_convolution_directional hf
      ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
      (hgc.fderiv_apply ℝ v) v
  simp_rw [show ∀ v, fderiv ℝ (fun y => fderiv ℝ (f ⋆[L,volume] g) y v) x v=
    (f ⋆[L,volume] (fun x => fderiv ℝ (fun y => fderiv ℝ g y v) x v)) x from
      fun v => congrFun (hsecond v) x]
  have hi (i : Fin n) : Integrable (fun y => f y*
      fderiv ℝ (fun z => fderiv ℝ g z (EuclideanSpace.single i 1)) (x-y)
        (EuclideanSpace.single i 1)) := by
    have hd : ContDiff ℝ 1 (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) :=
      (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact ((hgc.fderiv_apply ℝ (EuclideanSpace.single i 1)).fderiv_apply ℝ
      (EuclideanSpace.single i 1)).convolutionExists_right L hf
        ((hd.continuous_fderiv (by norm_num)).clm_apply continuous_const) x
  simp only [convolution_def,ContinuousLinearMap.mul_apply',L]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  congr 1
  funext y
  rw [laplacian_eq_sum_second_directional hg]
  exact (Finset.mul_sum _ _ _).symm

end RegularPointCoordinates

end

end OAI

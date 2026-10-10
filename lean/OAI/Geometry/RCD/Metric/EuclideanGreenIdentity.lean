import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicModel
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

namespace OAI

/-! # Compact-test Green identity in Euclidean space -/

open Set MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff

noncomputable section
namespace RegularPointCoordinates

/-- Two integrations by parts move a second directional derivative to
its compactly supported test function. -/
theorem integral_second_directional_commute {n : ℕ} {f g : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g)
    (v : Euclidean n) :
    (∫ x, f x*fderiv ℝ (fun y => fderiv ℝ g y v) x v) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v*g x := by
  let df := fun x => fderiv ℝ f x v
  let dg := fun x => fderiv ℝ g x v
  have hdf : ContDiff ℝ 1 df := (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdg : ContDiff ℝ 1 dg := (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdgs : HasCompactSupport dg := hgs.fderiv_apply ℝ v
  have hddgc : Continuous (fun x => fderiv ℝ dg x v) :=
    (hdg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hddfc : Continuous (fun x => fderiv ℝ df x v) :=
    (hdf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h1 : (∫ x, f x*fderiv ℝ dg x v) = -∫ x, df x*dg x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hdf.continuous.mul hdg.continuous).integrable_of_hasCompactSupport hdgs.mul_left)
      ((hf.continuous.mul hddgc).integrable_of_hasCompactSupport (hdgs.fderiv_apply ℝ v).mul_left)
      ((hf.continuous.mul hdg.continuous).integrable_of_hasCompactSupport hdgs.mul_left)
      (fun x _ => hf.differentiable (by norm_num) x)
      (fun x _ => hdg.differentiable (by norm_num) x)
  have h2 : (∫ x, df x*fderiv ℝ g x v) = -∫ x, fderiv ℝ df x v*g x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hddfc.mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left)
      ((hdf.continuous.mul hdg.continuous).integrable_of_hasCompactSupport hdgs.mul_left)
      ((hdf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left)
      (fun x _ => hdf.differentiable (by norm_num) x)
      (fun x _ => hg.differentiable (by norm_num) x)
  rw [h2,neg_neg] at h1
  exact h1

/-- A first-order gradient pairing against a compact test equals the
negative second directional pairing. -/
theorem integral_directional_pairing {n : ℕ} {f g : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) (hgs : HasCompactSupport g)
    (v : Euclidean n) :
    (∫ x, fderiv ℝ f x v*fderiv ℝ g x v) =
      -∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v*g x := by
  have hdf : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdgc : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hddfc : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x v) :=
    (hdf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hddfc.mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left)
    ((hdf.continuous.mul hdgc).integrable_of_hasCompactSupport (hgs.fderiv_apply ℝ v).mul_left)
    ((hdf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left)
    (fun x _ => hdf.differentiable (by norm_num) x)
    (fun x _ => hg.differentiable (by norm_num) x)

/-- The coordinate trace of the actual second derivative. -/
theorem laplacian_eq_sum_second_directional {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) :
    Δ f = fun x => ∑ i : Fin n,
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin n) ℝ)]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply,iteratedFDeriv_two_apply,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x) (differentiableAt_const _)]
  simp

/-- Green's identity with no boundary term for a compact test. -/
theorem integral_laplacian_commute {n : ℕ} {f g : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g) :
    (∫ x, f x*(Δ g) x) = ∫ x, (Δ f) x*g x := by
  classical
  rw [laplacian_eq_sum_second_directional hf,laplacian_eq_sum_second_directional hg]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  have hfg (i : Fin n) : Integrable (fun x => f x*
      fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) := by
    have hd : ContDiff ℝ 1 (fun x => fderiv ℝ g x (EuclideanSpace.single i 1)) :=
      (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (hf.continuous.mul ((hd.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      ((hgs.fderiv_apply ℝ (EuclideanSpace.single i 1)).fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left
  have hgf (i : Fin n) : Integrable (fun x =>
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)*g x) := by
    have hd : ContDiff ℝ 1 (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
      (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (((hd.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  rw [integral_finsetSum _ (fun i _ => hfg i),integral_finsetSum _ (fun i _ => hgf i)]
  exact Finset.sum_congr rfl (fun i _ => integral_second_directional_commute hf hg hgs _)

end RegularPointCoordinates

end

end OAI

import OAI.Geometry.RCD.Harmonic.EuclideanRadialWeight

namespace OAI

/-! # The radial dilation pairing of a Euclidean harmonic function -/

open Set Metric MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- The derivative of radial averages is a compactly supported Laplacian
pairing. This identity is valid before imposing harmonicity. -/
theorem integral_radial_dilation_eq_laplacian {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) :
    (∫ x, fderiv ℝ f x x*euclideanRadialWeight n x) =
      ∫ x, (Δ f) x*euclideanRadialPotential n x := by
  classical
  let ψ := euclideanRadialPotential n
  have hψ : ContDiff ℝ 1 ψ := (euclideanRadialPotential_smooth n).of_le (by simp)
  have hsψ : HasCompactSupport ψ := euclideanRadialPotential_compact n
  have heq (x : Euclidean n) : fderiv ℝ f x x*euclideanRadialWeight n x =
      -∑ i : Fin n, fderiv ℝ f x (EuclideanSpace.single i 1)*
        fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
    simp only [ψ,euclideanRadialPotential_fderiv,EuclideanSpace.inner_single_right,
      RCLike.conj_to_real,one_mul]
    have hsum := euclidean_linear_form_sum (fderiv ℝ f x) x
    calc
      _ = (∑ i : Fin n, fderiv ℝ f x (EuclideanSpace.single i 1)*x i)*euclideanRadialWeight n x := by rw [hsum]
      _ = _ := by rw [Finset.sum_mul,← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  have hi (i : Fin n) : Integrable (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)*
      fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    have hdf : ContDiff ℝ 1 (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
      (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (hdf.continuous.mul ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hsψ.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left
  have hdi (i : Fin n) : Integrable (fun x =>
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)*ψ x) := by
    have hdf : ContDiff ℝ 1 (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
      (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (((hdf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hψ.continuous).integrable_of_hasCompactSupport hsψ.mul_left
  simp_rw [heq]
  rw [integral_neg,integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_directional_pairing hf hψ hsψ]
  rw [Finset.sum_neg_distrib,neg_neg]
  rw [laplacian_eq_sum_second_directional hf]
  simp_rw [Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ => hdi i)).symm

/-- Harmonicity on the support of the potential makes the radial dilation
pairing vanish. -/
theorem integral_radial_dilation_eq_zero {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hh : InnerProductSpace.HarmonicOnNhd f (closedBall 0 1)) :
    (∫ x, fderiv ℝ f x x*euclideanRadialWeight n x) = 0 := by
  rw [integral_radial_dilation_eq_laplacian hf]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport (euclideanRadialPotential n)
  · have hz := (hh x (euclideanRadialPotential_support n hx)).2.self_of_nhds
    rw [hz]
    simp only [Pi.zero_apply,zero_mul]
  · have hz : euclideanRadialPotential n x = 0 := by
      by_contra hn
      exact hx (subset_tsupport _ hn)
    simp only [hz,mul_zero,Pi.zero_apply]

end RegularPointCoordinates

end

end OAI

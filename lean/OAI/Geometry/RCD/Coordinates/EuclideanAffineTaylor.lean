import OAI.Geometry.RCD.Coordinates.TaylorControl
import OAI.Geometry.RCD.Harmonic.AffineProjection

namespace OAI

/-! # A quantitative affine Taylor bound in the actual local L² space

The only analytic hypothesis is an interior second derivative bound.
The scale factor is exactly quadratic; no affine approximation hypothesis
is used. This is the Euclidean calculation in harmonic affine improvement.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Taylor's estimate on every radial segment of an interior ball. -/
theorem affine_taylor_bound_on_ball {f : E → ℝ} {df : E → E →L[ℝ] ℝ}
    {ddf : E → E →L[ℝ] (E →L[ℝ] ℝ)} {r R C : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hC : 0 ≤ C)
    (hf : ∀ z ∈ ball (0 : E) R, HasFDerivAt f (df z) z)
    (hdf : ∀ z ∈ ball (0 : E) R, HasFDerivAt df (ddf z) z)
    (hbound : ∀ z ∈ ball (0 : E) R, ‖ddf z‖ ≤ C)
    {z : E} (hz : z ∈ ball (0 : E) r) :
    |f z - f 0 - df 0 z| ≤ C * r ^ 2 := by
  have h0 : (0 : E) ∈ ball (0 : E) r := mem_ball_self hr
  have hs : segment ℝ (0 : E) z ⊆ ball (0 : E) R :=
    ((convex_ball (0 : E) r).segment_subset h0 hz).trans (ball_subset_ball hrR)
  have hh := norm_taylor_remainder_le hC (fun y hy => hf y (hs hy))
    (fun y hy => hdf y (hs hy)) (fun y hy => hbound y (hs hy))
  simp only [sub_zero, Real.norm_eq_abs] at hh
  have hzr : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hz
  exact hh.trans (mul_le_mul_of_nonneg_left
    (by nlinarith [norm_nonneg z] : ‖z‖ ^ 2 ≤ r ^ 2) hC)

/-- The radial Taylor polynomial bounds the local L² error. The norm of
the constant function records the square root of the ball's measure. -/
theorem l2_affine_taylor_bound (μ : Measure E)
    {f : E → ℝ} {df : E → E →L[ℝ] ℝ}
    {ddf : E → E →L[ℝ] (E →L[ℝ] ℝ)} {r R C : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hC : 0 ≤ C)
    (hf : ∀ z ∈ ball (0 : E) R, HasFDerivAt f (df z) z)
    (hdf : ∀ z ∈ ball (0 : E) R, HasFDerivAt df (ddf z) z)
    (hbound : ∀ z ∈ ball (0 : E) R, ‖ddf z‖ ≤ C)
    (F A one : Lp ℝ 2 (μ.restrict (ball (0 : E) r)))
    (hF : F =ᵐ[μ.restrict (ball (0 : E) r)] f)
    (hA : A =ᵐ[μ.restrict (ball (0 : E) r)] fun z => f 0 + df 0 z)
    (hone : one =ᵐ[μ.restrict (ball (0 : E) r)] fun _ => (1 : ℝ)) :
    ‖F - A‖ ≤ C * r ^ 2 * ‖one‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hF, hA, hone, Lp.coeFn_sub F A,
    ae_restrict_mem measurableSet_ball] with z hzF hzA hzone hzsub hz
  rw [hzsub, Pi.sub_apply, hzF, hzA, hzone]
  simp only [norm_one, mul_one, Real.norm_eq_abs]
  have hh := affine_taylor_bound_on_ball hr hrR hC hf hdf hbound hz
  simpa only [sub_add_eq_sub_sub] using hh

/-- Evaluation of a linear form in the standard Euclidean coordinates. -/
theorem euclidean_linear_form_sum {n : ℕ} (ell : Euclidean n →L[ℝ] ℝ)
    (z : Euclidean n) :
    (∑ i, ell (EuclideanSpace.single i 1) * z i) = ell z := by
  have hz : (∑ i, z i • EuclideanSpace.single i 1) = z := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [← hz]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_smul, smul_eq_mul, mul_comm]

/-- The Taylor polynomial is an actual affine combination of the
constant and coordinate functions in the local L² space. -/
theorem l2_coordinate_affine_taylor_bound {n : ℕ} (μ : Measure (Euclidean n))
    {f : Euclidean n → ℝ} {df : Euclidean n → Euclidean n →L[ℝ] ℝ}
    {ddf : Euclidean n → Euclidean n →L[ℝ] (Euclidean n →L[ℝ] ℝ)}
    {r R C : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hC : 0 ≤ C)
    (hf : ∀ z ∈ ball (0 : Euclidean n) R, HasFDerivAt f (df z) z)
    (hdf : ∀ z ∈ ball (0 : Euclidean n) R, HasFDerivAt df (ddf z) z)
    (hbound : ∀ z ∈ ball (0 : Euclidean n) R, ‖ddf z‖ ≤ C)
    (F one : Lp ℝ 2 (μ.restrict (ball (0 : Euclidean n) r)))
    (u : Fin n → Lp ℝ 2 (μ.restrict (ball (0 : Euclidean n) r)))
    (hF : F =ᵐ[μ.restrict (ball (0 : Euclidean n) r)] f)
    (hone : one =ᵐ[μ.restrict (ball (0 : Euclidean n) r)] fun _ => (1 : ℝ))
    (hu : ∀ i, u i =ᵐ[μ.restrict (ball (0 : Euclidean n) r)] fun z => z i) :
    ‖F - f 0 • one - ∑ i, df 0 (EuclideanSpace.single i 1) • u i‖ ≤
      C * r ^ 2 * ‖one‖ := by
  let a := fun i => df 0 (EuclideanSpace.single i 1)
  let A := f 0 • one + ∑ i, a i • u i
  have hA : A =ᵐ[μ.restrict (ball (0 : Euclidean n) r)] fun z => f 0 + df 0 z := by
    filter_upwards [Lp.coeFn_add (f 0 • one) (∑ i, a i • u i),
      Lp.coeFn_smul (f 0) one, hone,
      Lp.coeFn_finsetSum Finset.univ (fun i => a i • u i),
      (ae_all_iff.2 fun i => Lp.coeFn_smul (a i) (u i)), ae_all_iff.2 hu]
      with z hadd hsmul hone hsum hterms hcoords
    change (f 0 • one + ∑ i, a i • u i) z = _
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hsmul, hsum]
    simp only [Pi.smul_apply, smul_eq_mul, hone, mul_one, Finset.sum_apply]
    congr 1
    calc
      _ = ∑ i, a i * z i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hterms i]
        simp only [Pi.smul_apply, smul_eq_mul, hcoords i]
      _ = df 0 z := euclidean_linear_form_sum (df 0) z
  have hh := l2_affine_taylor_bound μ hr hrR hC hf hdf hbound F A one hF hA hone
  simpa only [A, sub_add_eq_sub_sub] using hh

end RegularPointCoordinates

end

end OAI

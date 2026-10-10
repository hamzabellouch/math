import OAI.Geometry.RCD.Sobolev.PoissonHarmonicCompactnessInput
import OAI.Geometry.RCD.Sobolev.WeakEulerRigidity

namespace OAI

/-! # Reassembling weak Euclidean Euler pairings -/

open Set Metric MeasureTheory Function
open scoped InnerProductSpace BigOperators ContDiff

noncomputable section
namespace RegularPointCoordinates

theorem interior_test_mul_integrable {n : ℕ} {S : ℝ} (ψ g : Euclidean n → ℝ)
    (hψ : InteriorSmoothTest n S ψ) (hg : ContinuousOn g (ball 0 S)) :
    Integrable (fun x => ψ x * g x) (volume : Measure (Euclidean n)) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((support_mul_subset_left ψ g).trans (subset_tsupport ψ))).mp
  exact (hψ.1.continuous.continuousOn.mul (hg.mono hψ.2.2)).integrableOn_compact' hψ.2.1
    (isClosed_tsupport ψ).measurableSet

/-- Separate limits of the derivative, value, constant and coordinate
pairings give the weak Euler equation with the limiting coefficients. -/
theorem euler_equation_of_average_pairings {n : ℕ} {S : ℝ} (hS : 0 < S)
    (w : Euclidean n → ℝ) (hw : ContDiffOn ℝ 2 w (ball 0 S))
    (ell : Euclidean n →L[ℝ] ℝ) (k : ℝ)
    (hpair : ∀ ψ : Euclidean n → ℝ, InteriorSmoothTest n S ψ →
      (volume.real (ball (0 : Euclidean n) S))⁻¹ *
          (∫ x in ball 0 S, ψ x * fderiv ℝ w x x) =
        (volume.real (ball (0 : Euclidean n) S))⁻¹ * (∫ x in ball 0 S, ψ x * w x) +
        (∑ j, ell (EuclideanSpace.single j 1) *
          ((volume.real (ball (0 : Euclidean n) S))⁻¹ * (∫ x in ball 0 S, ψ x * x j))) +
        k * ((volume.real (ball (0 : Euclidean n) S))⁻¹ * (∫ x in ball 0 S, ψ x))) :
    ∀ x ∈ ball 0 S, fderiv ℝ w x x = w x + ell x + k := by
  have hvol : volume.real (ball (0 : Euclidean n) S) ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume 0 hS)) measure_ball_ne_top)
  apply euler_equation_of_test_integrals w hw ell k
  intro ψ hψ hs hsub
  have htest : InteriorSmoothTest n S ψ := ⟨hψ, hs, hsub⟩
  have hD : ContDiffOn ℝ 1 (fderiv ℝ w) (ball 0 S) :=
    hw.fderiv_of_isOpen isOpen_ball (by norm_num)
  have iD : IntegrableOn (fun x => ψ x * fderiv ℝ w x x) (ball 0 S) volume :=
    (interior_test_mul_integrable ψ (fun x => fderiv ℝ w x x) htest
    (hD.continuousOn.clm_apply continuousOn_id)).integrableOn
  have iw : IntegrableOn (fun x => ψ x * w x) (ball 0 S) volume :=
    (interior_test_mul_integrable ψ w htest hw.continuousOn).integrableOn
  have il : IntegrableOn (fun x => ψ x * ell x) (ball 0 S) volume :=
    (interior_test_mul_integrable ψ ell htest ell.continuous.continuousOn).integrableOn
  have iψ : IntegrableOn ψ (ball (0 : Euclidean n) S) volume :=
    (hψ.continuous.integrable_of_hasCompactSupport hs).integrableOn
  have icoord (j : Fin n) : IntegrableOn (fun x : Euclidean n => ψ x * x j) (ball 0 S) volume :=
    (interior_test_mul_integrable ψ (fun x => x j) htest
      (EuclideanSpace.proj j).continuous.continuousOn).integrableOn
  have hell : (∫ x in ball 0 S, ψ x * ell x) =
      ∑ j, ell (EuclideanSpace.single j 1) * (∫ x in ball 0 S, ψ x * x j) := by
    calc
      _ = ∫ x in ball 0 S, ∑ j, ell (EuclideanSpace.single j 1) * (ψ x * x j) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [← euclidean_linear_form_sum ell x, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun j _ => (icoord j).const_mul _)]
        simp only [integral_const_mul]
  have hp := hpair ψ htest
  have hp' : (∫ x in ball 0 S, ψ x * fderiv ℝ w x x) =
      (∫ x in ball 0 S, ψ x * w x) + (∫ x in ball 0 S, ψ x * ell x) +
        k * (∫ x in ball 0 S, ψ x) := by
    rw [hell]
    have hf : (volume.real (ball (0 : Euclidean n) S))⁻¹ *
        ((∫ x in ball 0 S, ψ x * w x) +
          (∑ j, ell (EuclideanSpace.single j 1) * (∫ x in ball 0 S, ψ x * x j)) +
          k * (∫ x in ball 0 S, ψ x)) =
        (volume.real (ball (0 : Euclidean n) S))⁻¹ * (∫ x in ball 0 S, ψ x * w x) +
          (∑ j, ell (EuclideanSpace.single j 1) *
            ((volume.real (ball (0 : Euclidean n) S))⁻¹ * (∫ x in ball 0 S, ψ x * x j))) +
          k * ((volume.real (ball (0 : Euclidean n) S))⁻¹ * (∫ x in ball 0 S, ψ x)) := by
      rw [mul_add, mul_add, Finset.mul_sum]
      have hsum : (∑ j, (volume.real (ball (0 : Euclidean n) S))⁻¹ *
          (ell (EuclideanSpace.single j 1) * (∫ x in ball 0 S, ψ x * x j))) =
          ∑ j, ell (EuclideanSpace.single j 1) *
            ((volume.real (ball (0 : Euclidean n) S))⁻¹ * (∫ x in ball 0 S, ψ x * x j)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hsum]
      ring
    exact (mul_left_cancel₀ (inv_ne_zero hvol)) (hp.trans hf.symm)
  have hid : (fun x : Euclidean n => ψ x * (fderiv ℝ w x x - w x - ell x - k)) =
      fun x => ((ψ x * fderiv ℝ w x x - ψ x * w x) - ψ x * ell x) - k * ψ x := by
    funext x
    ring
  have hc₁ := integral_sub ((iD.sub iw).sub il) (iψ.const_mul k)
  have hc₂ := integral_sub (iD.sub iw) il
  have hc₃ := integral_sub iD iw
  simp only [Pi.sub_apply] at hc₁ hc₂ hc₃
  rw [hid, hc₁, hc₂, hc₃, integral_const_mul, hp']
  ring

end RegularPointCoordinates

end

end OAI

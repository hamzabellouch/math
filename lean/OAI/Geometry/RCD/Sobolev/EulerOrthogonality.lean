import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicModel
import OAI.Geometry.RCD.Sobolev.EulerRigidity

namespace OAI

/-! # The Euclidean contradiction for the sharp projection -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- Euler rigidity gives an exact affine identity in the same normalized
L2 space in which orthogonality passes to the limit. -/
theorem EuclideanHarmonicModel.euler_moments {n : ℕ} {S r : ℝ}
    (w : EuclideanHarmonicModel n S) (hS : 0 < S) (hr : r ≤ S)
    (ell : Euclidean n →L[ℝ] ℝ) (k : ℝ)
    (heuler : ∀ x ∈ ball (0 : Euclidean n) S,
      fderiv ℝ w.value x x = w.value x + ell x + k) :
    ∃ (c : ℝ) (b : Fin n → ℝ),
      w.moments hr none = c • w.moments hr (some none) +
        ∑ i, b i • w.moments hr (some (some i)) := by
  have haff := (euler_rigidity_of_contDiffOn hS w.harmonic.contDiffOn heuler).2.2
  let c := w.value 0
  let b : Fin n → ℝ := fun i => fderiv ℝ w.value 0 (EuclideanSpace.single i 1)
  let one : Lp ℝ 2 (volume.restrict (ball (0 : Euclidean n) r)) :=
    restrictedOne volume (ball 0 r) measure_ball_ne_top
  let u := euclideanCoordinateLp n r
  have hone : one =ᵐ[volume.restrict (ball 0 r)] fun _ => (1 : ℝ) := by
    simpa only [one, restrictedOne, indicator_univ] using
      (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := volume.restrict (ball (0 : Euclidean n) r))
        (hs := MeasurableSet.univ) (hμs := by simpa only [Measure.restrict_apply_univ]
          using (measure_ball_ne_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := r)))
        (c := (1 : ℝ)))
  have hraw : w.localLp hr = c • one + ∑ i, b i • u i := by
    apply Lp.ext
    filter_upwards [w.localLp_coe hr, hone,
      ae_restrict_mem measurableSet_ball,
      Lp.coeFn_add (c • one) (∑ i, b i • u i), Lp.coeFn_smul c one,
      Lp.coeFn_finsetSum Finset.univ (fun i => b i • u i),
      (ae_all_iff.2 fun i => Lp.coeFn_smul (b i) (u i)),
      (ae_all_iff.2 (euclideanCoordinateLp_coe n r))]
        with x hw ho hx ha hc hs hb hu
    rw [hw, ha]
    simp only [Pi.add_apply, hc, hs, Pi.smul_apply, smul_eq_mul, ho, mul_one,
      Finset.sum_apply]
    have hsum : (∑ i, (b i • u i) x) = fderiv ℝ w.value 0 x := by
      calc
        _ = ∑ i, b i * x i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hb i]
          simp only [Pi.smul_apply, smul_eq_mul]
          change b i * euclideanCoordinateLp n r i x = _
          rw [hu i]
        _ = _ := euclidean_linear_form_sum (fderiv ℝ w.value 0) x
    rw [hsum]
    exact haff x ((ball_subset_ball hr) hx)
  refine ⟨c, b, ?_⟩
  change normalizeLocalL2 volume (ball 0 r) measure_ball_ne_top (w.localLp hr) =
    c • normalizeLocalL2 volume (ball 0 r) measure_ball_ne_top one +
      ∑ i, b i • normalizeLocalL2 volume (ball 0 r) measure_ball_ne_top (u i)
  rw [hraw]
  simp only [normalizeLocalL2, smul_add, Finset.smul_sum, smul_comm c,
    smul_comm _ (‖one‖⁻¹), one]

/-- An Euler solution orthogonal to the affine span has zero local norm. -/
theorem EuclideanHarmonicModel.euler_orthogonal_norm_zero {n : ℕ} {S r : ℝ}
    (w : EuclideanHarmonicModel n S) (hS : 0 < S) (hr : r ≤ S)
    (ell : Euclidean n →L[ℝ] ℝ) (k : ℝ)
    (heuler : ∀ x ∈ ball (0 : Euclidean n) S,
      fderiv ℝ w.value x x = w.value x + ell x + k)
    (hone : ⟪w.moments hr none, w.moments hr (some none)⟫_ℝ = 0)
    (hcoords : ∀ i, ⟪w.moments hr none, w.moments hr (some (some i))⟫_ℝ = 0) :
    ⟪w.moments hr none, w.moments hr none⟫_ℝ = 0 := by
  obtain ⟨c, b, heq⟩ := w.euler_moments hS hr ell k heuler
  have hi := congrArg (fun g => ⟪w.moments hr none, g⟫_ℝ) heq
  simp only [inner_add_right, inner_smul_right, inner_sum,
    hone, hcoords, mul_zero, Finset.sum_const_zero, add_zero] at hi
  exact hi

/-- The limit of unit residuals cannot simultaneously satisfy the Euler
equation and be orthogonal to the affine coordinate span. -/
theorem EuclideanHarmonicModel.no_unit_euler_residual {n : ℕ} {S r : ℝ}
    (w : EuclideanHarmonicModel n S) (hS : 0 < S) (hr : r ≤ S)
    (ell : Euclidean n →L[ℝ] ℝ) (k : ℝ)
    (heuler : ∀ x ∈ ball (0 : Euclidean n) S,
      fderiv ℝ w.value x x = w.value x + ell x + k)
    (hunit : ⟪w.moments hr none, w.moments hr none⟫_ℝ = 1)
    (hone : ⟪w.moments hr none, w.moments hr (some none)⟫_ℝ = 0)
    (hcoords : ∀ i, ⟪w.moments hr none, w.moments hr (some (some i))⟫_ℝ = 0) : False := by
  have hh := w.euler_orthogonal_norm_zero hS hr ell k heuler hone hcoords
  rw [hunit] at hh
  exact one_ne_zero hh

end RegularPointCoordinates

end

end OAI

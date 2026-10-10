import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicModel
import OAI.Geometry.RCD.Harmonic.AffineScaleChoice

namespace OAI

/-! # The strict Euclidean candidate for harmonic affine improvement -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- The Taylor coefficients give a normalized local L² affine candidate. -/
theorem EuclideanHarmonicModel.affine_candidate {n : ℕ} {S ρ C : ℝ}
    (w : EuclideanHarmonicModel n S) (_hS : 0 < S) (hρ : 0 < ρ)
    (hρS : ρ ≤ S / 2) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ ball (0 : Euclidean n) (S / 2),
      ‖fderiv ℝ (fderiv ℝ w.value) z‖ ≤ C) :
    ∃ (c : ℝ) (v : Euclidean n),
      ‖∑ i, affineErrorCoefficients c (fun j => v j) i •
        w.moments (show ρ ≤ S by linarith) i‖ ≤ C * ρ ^ 2 := by
  let one : Lp ℝ 2 (volume.restrict (ball (0 : Euclidean n) ρ)) :=
    restrictedOne volume (ball 0 ρ) measure_ball_ne_top
  let F := w.localLp (show ρ ≤ S by linarith)
  let u := euclideanCoordinateLp n ρ
  let v : Euclidean n := WithLp.toLp 2 (fun i => fderiv ℝ w.value 0 (EuclideanSpace.single i 1))
  have hone : one =ᵐ[volume.restrict (ball (0 : Euclidean n) ρ)] fun _ => (1 : ℝ) := by
    simpa only [one, restrictedOne, indicator_univ] using
      (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := volume.restrict (ball (0 : Euclidean n) ρ))
        (hs := MeasurableSet.univ) (hμs := by simpa only [Measure.restrict_apply_univ]
          using (measure_ball_ne_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := ρ)))
        (c := (1 : ℝ)))
  have hsmall : ball (0 : Euclidean n) (S / 2) ⊆ ball 0 S :=
    ball_subset_ball (by linarith)
  have hsmooth := w.harmonic.contDiffOn
  have hf (z : Euclidean n) (hz : z ∈ ball (0 : Euclidean n) (S / 2)) :
      HasFDerivAt w.value (fderiv ℝ w.value z) z :=
    ((hsmooth.contDiffAt (isOpen_ball.mem_nhds (hsmall hz))).differentiableAt
      (by norm_num)).hasFDerivAt
  have hdf (z : Euclidean n) (hz : z ∈ ball (0 : Euclidean n) (S / 2)) :
      HasFDerivAt (fderiv ℝ w.value) (fderiv ℝ (fderiv ℝ w.value) z) z := by
    have hh : ContDiffOn ℝ 1 (fderiv ℝ w.value) (ball 0 S) :=
      hsmooth.fderiv_of_isOpen isOpen_ball (by norm_num)
    exact ((hh.contDiffAt (isOpen_ball.mem_nhds (hsmall hz))).differentiableAt
      (by norm_num)).hasFDerivAt
  have ht := l2_coordinate_affine_taylor_bound volume hρ hρS hC hf hdf hbound F one u
    (w.localLp_coe _) hone (euclideanCoordinateLp_coe n ρ)
  refine ⟨w.value 0, v, ?_⟩
  change ‖∑ i, affineErrorCoefficients (w.value 0) (fun j => v j) i •
    affineMomentFamily n (normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top F)
      (normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top one)
      (fun j => normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top (u j)) i‖ ≤ _
  rw [affineMomentFamily_sum]
  have heq : normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top F -
      w.value 0 • normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top one -
      ∑ j, v j • normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top (u j) =
      ‖one‖⁻¹ • (F - w.value 0 • one - ∑ j, v j • u j) := by
    simp only [normalizeLocalL2, smul_sub, Finset.smul_sum, smul_comm _ (‖one‖⁻¹), one]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  have ht' : ‖F - w.value 0 • one - ∑ j, v j • u j‖ ≤ C * ρ ^ 2 * ‖one‖ := ht
  by_cases hzero : ‖one‖ = 0
  · simp only [hzero, inv_zero, zero_mul]
    positivity
  calc
    _ ≤ ‖one‖⁻¹ * (C * ρ ^ 2 * ‖one‖) :=
      mul_le_mul_of_nonneg_left ht' (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := by field_simp

end RegularPointCoordinates

end

end OAI

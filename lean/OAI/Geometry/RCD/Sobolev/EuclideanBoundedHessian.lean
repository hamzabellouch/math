import OAI.Geometry.RCD.Sobolev.EuclideanHarmonicHessianConstruction
import OAI.Geometry.RCD.Coordinates.NormalizedPairing

namespace OAI

/-! # Interior Hessian control for bounded, unnormalized harmonic functions -/

open Set Metric MeasureTheory
open scoped ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_bounded_harmonic_hessian {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Euclidean n → ℝ) (S M : ℝ),
      0 < S → 0 < M → ContDiff ℝ 2 f →
      InnerProductSpace.HarmonicOnNhd f (ball 0 S) →
      (∀ x ∈ ball 0 S, |f x| ≤ M) →
      ∀ z ∈ ball (0 : Euclidean n) (S/2),
        ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C*M/S^2 := by
  obtain ⟨C,hC,hbound⟩ := euclideanHarmonicHessianInput hn
  refine ⟨C,hC,?_⟩
  intro f S M hS hM hf hh hb z hz
  let F : Euclidean n → ℝ := fun x => M⁻¹ • f x
  have hF : ContDiff ℝ 2 F := hf.const_smul _
  let : IsFiniteMeasure (volume.restrict (ball (0 : Euclidean n) S)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := S))⟩
  have hpoint : ∀ᵐ x ∂volume.restrict (ball (0 : Euclidean n) S), |F x| ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    dsimp only [F,smul_eq_mul]
    rw [abs_mul,abs_of_pos (inv_pos.mpr hM)]
    calc
      M⁻¹*|f x| ≤ M⁻¹*M := mul_le_mul_of_nonneg_left (hb x hx) (inv_nonneg.mpr hM.le)
      _ = 1 := inv_mul_cancel₀ hM.ne'
  have hLp : MemLp F 2 (volume.restrict (ball (0 : Euclidean n) S)) := by
    apply MemLp.of_bound hF.continuous.aestronglyMeasurable 1
    simpa only [Real.norm_eq_abs] using hpoint
  have hnormalized : ‖normalizeLocalL2 volume (ball (0 : Euclidean n) S) measure_ball_ne_top
      (hLp.toLp F)‖ ≤ 1 := by
    apply normalized_norm_le_of_bound volume _ _ _ zero_le_one
    filter_upwards [hLp.coeFn_toLp,hpoint] with x hx hb'
    rwa [hx]
  let w : EuclideanHarmonicModel n S := {
    value := F
    harmonic := hh.const_smul
    memLp := hLp
    normalized := hnormalized }
  have he : ‖fderiv ℝ (fderiv ℝ F) z‖ = M⁻¹*‖fderiv ℝ (fderiv ℝ f) z‖ := by
    rw [← norm_iteratedFDeriv_one (f := fderiv ℝ F),norm_iteratedFDeriv_fderiv]
    change ‖iteratedFDeriv ℝ 2 (fun x => M⁻¹ • f x) z‖ = _
    rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hM),← norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_one]
  have hhess := hbound S hS w z hz
  change ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C/S^2 at hhess
  rw [he] at hhess
  have hresult := (div_le_iff₀ hM).mp (by simpa only [div_eq_inv_mul] using hhess)
  calc
    _ ≤ (C/S^2)*M := by simpa only [div_eq_inv_mul] using hresult
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI

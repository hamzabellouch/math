import OAI.MeasureTheory.Falconer.Slicing.GaussianOrthogonal
import OAI.MeasureTheory.Falconer.Angular.AngularTubes
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

/-! # Resolving two Gaussian band constraints into orthogonal coordinates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem perpendicular_normalize_orthogonal {u v : Space d} (hu : ‖u‖ = 1) :
    inner ℝ u (normalize (perpendicularPart u v)) = 0 := by
  simp [NormedSpace.normalize,perpendicularPart,inner_sub_right,inner_smul_right,
    hu]

theorem two_band_perpendicular_coordinate {u v x : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {r : ℝ} (_hr : 0 ≤ r)
    (hux : |inner ℝ u x| ≤ r) (hvx : |inner ℝ v x| ≤ r)
    (hne : perpendicularPart u v ≠ 0) :
    |inner ℝ (normalize (perpendicularPart u v)) x| ≤ 2*r/‖perpendicularPart u v‖ := by
  have huv : |inner ℝ u v| ≤ 1 := by
    simpa only [hu,hv,mul_one] using abs_real_inner_le_norm u v
  have hinner : |inner ℝ (perpendicularPart u v) x| ≤ 2*r := by
    rw [perpendicularPart,inner_sub_left,real_inner_smul_left]
    calc
      _ ≤ |inner ℝ v x|+|inner ℝ u v*inner ℝ u x| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (inner ℝ v x) (inner ℝ u v*inner ℝ u x)
      _ ≤ r+1*r := add_le_add hvx (by rw [abs_mul]; exact mul_le_mul huv hux (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  rw [NormedSpace.normalize,real_inner_smul_left,abs_mul,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne))]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr (norm_nonneg (perpendicularPart u v)))

theorem gaussian_two_band_nondegenerate {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hne : perpendicularPart u v ≠ 0) :
    stdGaussian (Space d) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ≤
      ENNReal.ofReal (2*gaussianBandConstant^2*r^2/‖perpendicularPart u v‖) := by
  have hsub : {x : Space d | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ⊆
      {x : Space d | |inner ℝ u x| ≤ r ∧
        |inner ℝ (normalize (perpendicularPart u v)) x| ≤ 2*r/‖perpendicularPart u v‖} := by
    rintro x ⟨hx,hx'⟩
    exact ⟨hx,two_band_perpendicular_coordinate hu hv hr hx hx' hne⟩
  apply (measure_mono hsub).trans
  have h := gaussian_orthogonal_pair_band hu (norm_normalize hne)
    (perpendicular_normalize_orthogonal hu) hr (by positivity : 0 ≤ 2*r/‖perpendicularPart u v‖)
  convert h using 1
  congr 1
  ring

end Falconer

end OAI

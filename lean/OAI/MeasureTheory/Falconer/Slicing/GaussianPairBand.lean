import OAI.MeasureTheory.Falconer.Slicing.GaussianPairGeometry

namespace OAI

/-! # Regularized two-vector Gaussian band bounds -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def gaussianPairBandConstant : ℝ :=
  2*gaussianBandConstant+4*gaussianBandConstant^2

theorem gaussianPairBandConstant_pos : 0 < gaussianPairBandConstant := by
  unfold gaussianPairBandConstant
  have := gaussianBandConstant_pos
  positivity

theorem gaussian_two_band {u v : Space d} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    stdGaussian (Space d) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ≤
      ENNReal.ofReal (gaussianPairBandConstant*r^2/(‖perpendicularPart u v‖+r)) := by
  let C := gaussianBandConstant
  let q := ‖perpendicularPart u v‖
  have hC : 0 < C := gaussianBandConstant_pos
  have hq₀ : 0 ≤ q := norm_nonneg _
  have hden : 0 < q+r := by positivity
  have hsub : {x : Space d | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ⊆
      {x : Space d | |inner ℝ u x| ≤ r} := fun _ hx => hx.1
  by_cases hqr : q ≤ r
  · apply ((measure_mono hsub).trans (gaussian_unit_inner_band hu hr.le)).trans
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hden).mpr
    calc
      C*r*(q+r) ≤ C*r*(2*r) := by gcongr; linarith
      _ = (2*C)*r^2 := by ring
      _ ≤ gaussianPairBandConstant*r^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        dsimp [gaussianPairBandConstant,C]
        nlinarith [sq_nonneg gaussianBandConstant]
  · have hqp : 0 < q := hr.trans (lt_of_not_ge hqr)
    have hne : perpendicularPart u v ≠ 0 := norm_pos_iff.mp hqp
    apply (gaussian_two_band_nondegenerate hu hv hr.le hne).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_iff₀ hqp hden).mpr
    calc
      (2*C^2*r^2)*(q+r) ≤ (2*C^2*r^2)*(2*q) := by gcongr; linarith
      _ = (4*C^2)*r^2*q := by ring
      _ ≤ gaussianPairBandConstant*r^2*q := by
        gcongr
        dsimp [gaussianPairBandConstant,C]
        linarith [gaussianBandConstant_pos]

theorem gaussian_two_band_projective_chart {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : 0 ≤ inner ℝ u v)
    {r : ℝ} (hr : 0 < r) :
    stdGaussian (Space d) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ≤
      ENNReal.ofReal (2*gaussianPairBandConstant*r^2/(dist u v+r)) := by
  apply (gaussian_two_band hu hv hr).trans
  apply ENNReal.ofReal_le_ofReal
  have hh := unit_close_of_perpendicular hu hv huv
  have hp : 0 < dist u v+r := by positivity
  have hq : 0 < ‖perpendicularPart u v‖+r := by positivity
  apply (div_le_div_iff₀ hq hp).mpr
  have hc : 0 ≤ gaussianPairBandConstant*r^2 :=
    mul_nonneg gaussianPairBandConstant_pos.le (sq_nonneg _)
  calc
    _ ≤ (gaussianPairBandConstant*r^2)*(2*(‖perpendicularPart u v‖+r)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      rw [dist_eq_norm]
      linarith
    _ = _ := by ring

end Falconer

end OAI

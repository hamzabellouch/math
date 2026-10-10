import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCriticalDetector
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPackedProduct

namespace OAI

/-! # The literal critical-line mass controlling the integral alternative -/

namespace Ostmann

open MeasureTheory

noncomputable def densityCriticalMass (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) : ℝ :=
  ∫ v, densityCubicWeight (v - t) * ‖χ.L (densityVerticalPoint (1 / 2) v)‖ *
    ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) v)‖

 theorem densityCriticalMass_nonneg (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) :
    0 ≤ densityCriticalMass χ X t :=
  integral_nonneg (fun _ => mul_nonneg (mul_nonneg (densityCubicWeight_nonneg _) (norm_nonneg _)) (norm_nonneg _))

 theorem densityCriticalMass_eq (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) :
    (∫ u, densityCubicWeight u * ‖densityCriticalProduct χ X t u‖) = densityCriticalMass χ X t := by
  have he := integral_add_right_eq_self (μ := volume)
    (fun v => densityCubicWeight (v - t) * ‖χ.L (densityVerticalPoint (1 / 2) v)‖ *
      ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) v)‖) t
  convert he using 1
  apply integral_congr_ae
  filter_upwards with u
  simp only [add_sub_cancel_right, densityCriticalProduct, norm_mul]
  rw [add_comm u t]
  ring
  rfl

 theorem densityDetector_uniform_mass_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (σ β t : ℝ) (hσ : 1 / 2 < σ) (hβ : σ ≤ β) (hβ1 : β ≤ 1)
    (hz : χ.L (densityVerticalPoint β t) = 0) (Y : ℝ) (hY : 1 ≤ Y) :
    ‖densityDetectorMean χ X (densityVerticalPoint β t) Y‖ ≤
      (16 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)) * densityCriticalMass χ X t := by
  have hm := densityDetectorMean_at_zero_bound χ X β t (hσ.trans_le hβ) hβ1 hz Y hY
  rw [densityCriticalMass_eq] at hm
  apply hm.trans
  apply mul_le_mul_of_nonneg_right _ (densityCriticalMass_nonneg χ X t)
  calc
    _ ≤ (16 * Y ^ (1 / 2 - σ)) / (β - 1 / 2) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by norm_num)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

end Ostmann

end OAI

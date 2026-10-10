import OAI.NumberTheory.TwoPoint.Bounds.WeightedShiftAverage
import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftScale

namespace OAI

/-! The three quantitative terms in the qualitative weighted shift
argument, separated from their eventual scale estimates. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma rough_coefficient_mass_le_one (Z : Finset ℕ) (c : ℕ → ℂ) (D : ℕ)
    (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ z ∧ z < D + D)
    (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1) :
    (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 1 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hcard : Z.card ≤ D := by
    have ht := card_le_card (show Z ⊆ Ico D (D + D) from
      fun z hz => mem_Ico.mpr (hZ z hz))
    simpa using ht
  calc
    _ ≤ ∑ _z ∈ Z, (D : ℝ)⁻¹ := sum_le_sum
      (rough_coefficient_norm_le Z c D hDr
        (fun z hz => by exact_mod_cast (hZ z hz).1) hc)
    _ = Z.card / (D : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hDr).mpr (by exact_mod_cast hcard)

lemma weighted_shift_high_identity (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (q η U V K : ℝ) (hη : 0 < η) :
    (((U * q) * ((2 * (h : ℝ) + 1) * D) *
        (K * Y * D * q) / η ^ 4) * (V / D * q ^ 4)) / ((Y : ℝ) * D) =
      ((2 * (h : ℝ) + 1) * U * V * K) * (q ^ 6 / η ^ 4) := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hYr : (Y : ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  field_simp

/-- The high-frequency cost is controlled by `q^6 ≤ η^5`; all actual
correlation, boundary and short-window terms remain explicit. -/
theorem weighted_rough_shift_parameter_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (c : ℕ → ℂ) (D h Y : ℕ)
    (hD : 0 < D) (hY : 0 < Y) (hZ : ∀ z ∈ Z, z ≤ 2 * D)
    (q η U V K : ℝ) (hq : 0 ≤ q) (hη : 0 < η)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (hmass : (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 1)
    (hendpoint : (D : ℝ) / Y ≤ η) (hgap : q ^ 6 ≤ η ^ 5)
    (hB : ∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U * q)
    (hfourth : (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V / D * q ^ 4)
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤
      K * Y * D * q) :
    ‖weightedRoughShiftAverage f g Z c h Y‖ ≤
      (2 + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K) * η := by
  have he : 2 * (D : ℝ) / Y * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) ≤ 2 * η := by
    calc
      _ = 2 * ((D : ℝ) / Y) * (∑ z ∈ Z, ‖c z / (z : ℂ)‖) := by ring
      _ ≤ 2 * η * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hendpoint (by norm_num)) hmass
        (sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
      _ = _ := mul_one _
  have hraw := weighted_rough_shift_average_bound f g hf hg Z c D h Y hD hY hZ
    η (U * q) (V / D * q ^ 4) (K * Y * D * q) hη (by positivity) (by positivity)
    hB hfourth hF
  have hlow := rough_low_term_bound D h Y hD hY η hη.le
  have hhigh := weighted_shift_high_identity D h Y hD hY q η U V K hη
  have hfrac : q ^ 6 / η ^ 4 ≤ η := by
    apply (div_le_iff₀ (pow_pos hη 4)).mpr
    convert hgap using 1
    ring
  have ht := mul_le_mul_of_nonneg_left hfrac
    (show 0 ≤ (2 * (h : ℝ) + 1) * U * V * K by positivity)
  apply hraw.trans
  rw [add_div, hhigh]
  nlinarith only [he, hlow, ht]

end TwoPointCorrelations

end OAI

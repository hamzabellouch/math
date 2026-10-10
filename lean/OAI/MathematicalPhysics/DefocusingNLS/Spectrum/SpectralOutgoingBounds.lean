import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialTailData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularUnweight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalJet
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalFactor

namespace OAI

/-! Value and first-derivative bounds for the constructed outgoing spectral columns. -/

open Polynomial
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circular_expansion_bound (U : ℂ[X] × ℂ[X]) (j : ℕ)
    (v : CircularTailSpace) (Y : ℝ → E₄)
    (hY : ∀ t, 0 ≤ t → Y t=circularPolynomialJet U t+circularUnweight (2*(j : ℝ)) v t)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖Y t‖ ≤ ‖boundedCircularPolynomialJet U‖+‖v‖ := by
  have he : Real.exp (-(2*(j : ℝ))*t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  rw [hY t ht]
  calc
    _ ≤ ‖circularPolynomialJet U t‖+‖circularUnweight (2*(j : ℝ)) v t‖ := norm_add_le _ _
    _ ≤ ‖boundedCircularPolynomialJet U‖+Real.exp (-(2*(j : ℝ))*t)*‖v‖ := by
      apply add_le_add
      · rw [← boundedCircularPolynomialJet_eq U t ht]
        exact circularTailEvaluation_norm _ _
      · exact circularUnweight_norm _ _ _
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) he)

theorem spectralPhysicalJet_bounds (ν : ℂ) (Y : ℝ → ℂ × ℂ)
    (M r : ℝ) (hr : 0 < r) (hY : ‖Y (Real.log r)‖ ≤ M) :
    ‖(spectralPhysicalJet ν Y r).1‖ ≤ r^ν.re*M ∧
      ‖(spectralPhysicalJet ν Y r).2‖ ≤ r^(ν.re-1)*(‖ν‖+1)*M := by
  have hf := (norm_fst_le (Y (Real.log r))).trans hY
  have hg := (norm_snd_le (Y (Real.log r))).trans hY
  constructor
  · change ‖Complex.exp (ν*(Real.log r : ℂ))*(Y (Real.log r)).1‖ ≤ _
    rw [norm_mul,radialPhysicalFactor_norm ν r hr]
    exact mul_le_mul_of_nonneg_left hf (Real.rpow_pos_of_pos hr _).le
  · change ‖Complex.exp (ν*(Real.log r : ℂ))/(r : ℂ)*
      (ν*(Y (Real.log r)).1+(Y (Real.log r)).2)‖ ≤ _
    rw [norm_mul,norm_div,radialPhysicalFactor_norm ν r hr,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hr,Real.rpow_sub hr,Real.rpow_one]
    calc
      _ ≤ (r^ν.re/r)*(‖ν‖*‖(Y (Real.log r)).1‖+‖(Y (Real.log r)).2‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
        · positivity
      _ ≤ (r^ν.re/r)*(‖ν‖*M+M) := by gcongr
      _ = _ := by ring

end DefocusingNLS

end OAI

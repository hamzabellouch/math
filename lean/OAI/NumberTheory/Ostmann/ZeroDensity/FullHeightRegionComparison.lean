import OAI.NumberTheory.Ostmann.ZeroDensity.FullHeightRealRegion
import OAI.NumberTheory.Ostmann.ZeroDensity.NonquadraticZeroRegion
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCharacterReal

namespace OAI

/-! # Comparing the conductor-height cutoffs with the published Page cutoff -/

namespace Ostmann

theorem conductor_height_log_ge_one (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) :
    1 ≤ Real.log (2 * (Q : ℝ) * T) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  apply (Real.le_log_iff_exp_le (by positivity : 0 < 2 * (Q : ℝ) * T)).mpr
  have hh := mul_le_mul_of_nonneg_right hQr (by linarith : 0 ≤ T)
  exact Real.exp_one_lt_three.le.trans (by nlinarith)

theorem local_height_log_le (q Q : ℕ) (hq : 0 < q) (hqQ : q ≤ Q)
    (T : ℝ) (hT : 2 ≤ T) :
    Real.log q + Real.log (T + 2) + 1 ≤ 2 * Real.log (2 * (Q : ℝ) * T) := by
  have hQr : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ1 : 1 ≤ Q := (Nat.succ_le_iff.mpr hq).trans hqQ
  have hH := conductor_height_log_ge_one Q hQ1 T hT
  have hp : (q : ℝ) * (T + 2) ≤ 2 * (Q : ℝ) * T := by
    have hQpos : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_right hQr (by linarith : 0 ≤ T + 2)
    nlinarith
  have hl := Real.log_le_log (mul_pos hqp (by linarith : 0 < T + 2)) hp
  rw [Real.log_mul hqp.ne' (by linarith : T + 2 ≠ 0)] at hl
  linarith

theorem small_cutoff_fraction (a b U V : ℝ) (ha : 0 ≤ a) (hU : 0 < U) (hV : 0 < V)
    (hab : a ≤ b / 4) (hUV : U ≤ 2 * V) : a / V ≤ b / (2 * U) := by
  apply (div_le_div_iff₀ hV (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hUV (by positivity : 0 ≤ 2 * a)
  have hh' := mul_le_mul_of_nonneg_right hab hV.le
  nlinarith

noncomputable def PrimitiveRealZero.asRealCharacter (e : PrimitiveRealZero) : PrimitiveRealCharacter where
  modulus := e.modulus
  positive := e.positive
  character := e.character
  primitive := e.primitive
  nontrivial := e.nontrivial

@[simp] theorem actualRealZero_asCharacter (χ : PrimitiveRealCharacter) (i : ℕ)
    (hi : ((realCharacterActualZeros χ).zeros i).im = 0) :
    ((actualRealCharacterZeroExpansion χ).realZero i hi).asRealCharacter = χ := rfl

end Ostmann

end OAI

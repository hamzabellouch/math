import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterGlobalZeros
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterStripBound

namespace OAI

/-! An all-height logarithmic derivative bound with explicit polynomial
modulus loss. The stronger high-height result remains available separately. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

theorem mrt_character_logderiv_global_bound : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ t sigma : ℝ, 1 - c / ((q : ℝ) ^ 2 * mrtCharacterHeight q t) ≤ sigma →
      sigma ≤ 2 →
      DirichletCharacter.LFunction χ ((sigma : ℂ) + Complex.I * (t : ℂ)) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((sigma : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
          C * (q : ℝ) ^ 2 * mrtCharacterHeight q t ^ 2 := by
  obtain ⟨c0, hc0, hfree0⟩ := mrt_character_nonprincipal_global_zero_free
  let c := min c0 (1 / 4)
  have hc : 0 < c := lt_min hc0 (by norm_num)
  have hcsmall : c ≤ 1 / 4 := min_le_right _ _
  have hfree : ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ t beta : ℝ, 1 - c / ((q : ℝ) ^ 2 * mrtCharacterHeight q t) ≤ beta →
      DirichletCharacter.LFunction χ ((beta : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    intro q _ χ hχ t beta hb
    apply hfree0 q χ hχ t beta
    have hd := div_le_div_of_nonneg_right (min_le_left c0 (1 / 4))
      (mul_nonneg (sq_nonneg (q : ℝ)) (mrt_character_height_pos q t).le)
    linarith
  let P := 1 / Real.log ((15 / 16 : ℝ) / (7 / 8))
  have hP : 0 < P := by dsimp [P]; exact one_div_pos.mpr (Real.log_pos (by norm_num))
  let A := Real.log (4 * mrtCharacterInverseConstant) / Real.log 2 + 1
  have hA : 0 < A := by
    have hK : 1 ≤ mrtCharacterInverseConstant := by
      unfold mrtCharacterInverseConstant
      exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
    have hlog : 0 ≤ Real.log (4 * mrtCharacterInverseConstant) := Real.log_nonneg (by linarith)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [A]
    positivity
  let C := A * (2 * mrtCharacterLogDerivativeConstant + 6 * P / c)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos hA (add_pos (mul_pos (by norm_num) mrtCharacterLogDerivativeConstant_pos)
      (div_pos (mul_pos (by norm_num) hP) hc))
  refine ⟨c / 4, C, by positivity, hC, ?_⟩
  intro q _ χ hχ t sigma hsigma hsigma2
  let Q : ℝ := (q : ℝ) ^ 2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  let H := mrtCharacterHeight q t
  have hH : 0 < H := mrt_character_height_pos q t
  have hHhalf : 1 / 2 ≤ H := mrt_character_log_height_ge_half q t
  have hsigma' : 1 - c / (4 * Q * H) ≤ sigma := by
    change 1 - (c / 4) / (Q * H) ≤ sigma at hsigma
    convert hsigma using 1; ring
  have hsmall : c / (4 * Q * H) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Q * H)).mpr
    nlinarith
  have hsigmalow : 7 / 8 ≤ sigma := by linarith
  have hne : DirichletCharacter.LFunction χ ((sigma : ℂ) + I * (t : ℂ)) ≠ 0 := by
    apply hfree q χ hχ t sigma
    have hi : c / (4 * Q * H) ≤ c / (Q * H) :=
      div_le_div_of_nonneg_left hc.le (by positivity) (by nlinarith)
    change 1 - c / (Q * H) ≤ sigma
    linarith
  refine ⟨hne, ?_⟩
  let z := mrtCharacterRealDiskPoint sigma
  have hz : ‖z‖ ≤ 3 / 4 := by
    rw [show z = mrtCharacterRealDiskPoint sigma from rfl, mrtCharacterRealDiskPoint,
      Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  have hp : DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z) ≠ 0 := by
    rwa [mrtCharacterPhysicalPoint_real]
  have hn : mrtCharacterNormalizedLFunction χ t z ≠ 0 :=
    div_ne_zero hp (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num))
  have hf : ∀ v beta : ℝ, (-2 : ℝ) ≤ |v| →
      1 - (c / Q) / mrtCharacterHeight q v ≤ beta →
      DirichletCharacter.LFunction χ ((beta : ℂ) + I * (v : ℂ)) ≠ 0 := by
    intro v beta _ hb
    apply hfree q χ hχ v beta
    change 1 - c / (Q * mrtCharacterHeight q v) ≤ beta
    convert hb using 1; ring
  have hd : ∀ rho ∈ mrtCharacterNormalizedZeros χ t,
      c / (6 * Q * H) ≤ ‖z - rho‖ := by
    intro rho hrho
    have hh := mrt_character_zero_distance_of_strip (div_pos hc hQ0) χ hf t sigma
      (by linarith [abs_nonneg t]) (by
        change 1 - (c / Q) / (4 * H) ≤ sigma
        convert hsigma' using 1; ring) hrho
    convert hh using 1; ring
  have he := mrt_character_normalized_logderiv_norm χ hχ t hz hn
    (show 0 < c / (6 * Q * H) by positivity) hd
  have hcoef : 0 ≤ mrtCharacterLogDerivativeConstant + P / (c / (6 * Q * H)) := by
    exact add_nonneg mrtCharacterLogDerivativeConstant_pos.le (div_nonneg hP.le (by positivity))
  have hlog := mul_le_mul_of_nonneg_left (mrt_character_log_disk_growth q t) hcoef
  have htotal := he.trans hlog
  have hrecip : P / (c / (6 * Q * H)) = (6 * P / c) * (Q * H) := by field_simp
  change _ ≤ (mrtCharacterLogDerivativeConstant + P / (c / (6 * Q * H))) * (A * H) at htotal
  rw [hrecip] at htotal
  have hlinear : H ≤ 2 * Q * H ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlinear
    (mul_nonneg hA.le mrtCharacterLogDerivativeConstant_pos.le)
  have htotal' : ‖deriv (mrtCharacterNormalizedLFunction χ t) z /
      mrtCharacterNormalizedLFunction χ t z‖ ≤ C * Q * H ^ 2 := by
    dsimp [C]
    nlinarith only [htotal, hmul]
  rw [mrtCharacterNormalized_logderiv_eq χ hχ t z hp, norm_mul,
    mrtCharacterPhysicalPoint_real] at htotal'
  norm_num at htotal'
  apply (le_mul_of_one_le_left (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans
  simpa only [norm_div] using htotal'

end TwoPointCorrelations

end OAI

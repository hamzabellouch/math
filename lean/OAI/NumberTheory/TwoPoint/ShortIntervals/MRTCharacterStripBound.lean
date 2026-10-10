import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterZeroDistance

namespace OAI

/-! The actual logarithmic derivative is bounded by an absolute constant
times log(q*(abs(t)+2))^2 on a narrower classical high-height strip. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

lemma mrt_character_log_height_ge_half (q : ℕ) [NeZero q] (t : ℝ) :
    1 / 2 ≤ mrtCharacterHeight q t := by
  have hlog : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact hlog.trans ((Real.log_le_log (by norm_num)
    (by linarith [abs_nonneg t])).trans (mrt_character_height_ge q t))

theorem mrt_character_logderiv_strip_bound : ∃ c C T : ℝ,
    0 < c ∧ 0 < C ∧ 2 < T ∧ ∀ (q : ℕ) [NeZero q],
    ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t sigma : ℝ), T ≤ |t| →
      1 - c / mrtCharacterHeight q t ≤ sigma → sigma ≤ 2 →
      DirichletCharacter.LFunction χ ((sigma : ℂ) + Complex.I * (t : ℂ)) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((sigma : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
          C * mrtCharacterHeight q t ^ 2 := by
  obtain ⟨c0, hc0, T0, hT0, hfree0⟩ := mrt_character_nonprincipal_high_zero_free
  let c := min c0 (1 / 4)
  have hc : 0 < c := lt_min hc0 (by norm_num)
  have hcsmall : c ≤ 1 / 4 := min_le_right _ _
  have hfree : ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ t beta : ℝ, T0 ≤ |t| → 1 - c / mrtCharacterHeight q t ≤ beta →
      DirichletCharacter.LFunction χ ((beta : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    intro q _ χ hχ t beta ht hb
    apply hfree0 q χ hχ t beta ht
    have hd := div_le_div_of_nonneg_right (min_le_left c0 (1 / 4))
      (mrt_character_height_pos q t).le
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
  refine ⟨c / 4, C, T0 + 2, by positivity, hC, by linarith, ?_⟩
  intro q _ χ hχ t sigma ht hsigma hsigma2
  let H := mrtCharacterHeight q t
  have hH : 0 < H := mrt_character_height_pos q t
  have hHhalf : 1 / 2 ≤ H := mrt_character_log_height_ge_half q t
  have hsigma' : 1 - c / (4 * H) ≤ sigma := by
    have he : (c / 4) / H = c / (4 * H) := by ring
    change 1 - (c / 4) / H ≤ sigma at hsigma
    rwa [he] at hsigma
  have hsmall : c / (4 * H) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * H)).mpr
    nlinarith
  have hsigmalow : 7 / 8 ≤ sigma := by linarith
  have hne : DirichletCharacter.LFunction χ ((sigma : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    apply hfree q χ hχ t sigma (by linarith)
    have hi : c / (4 * H) ≤ c / H :=
      div_le_div_of_nonneg_left hc.le hH (by linarith)
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
  have hd : ∀ rho ∈ mrtCharacterNormalizedZeros χ t, c / (6 * H) ≤ ‖z - rho‖ := by
    intro rho hrho
    exact mrt_character_zero_distance_of_strip hc χ (hfree q χ hχ) t sigma ht hsigma' hrho
  have he := mrt_character_normalized_logderiv_norm χ hχ t hz hn
    (show 0 < c / (6 * H) by positivity) hd
  have hcoef : 0 ≤ mrtCharacterLogDerivativeConstant + P / (c / (6 * H)) := by
    exact add_nonneg mrtCharacterLogDerivativeConstant_pos.le (div_nonneg hP.le (by positivity))
  have hlog := mul_le_mul_of_nonneg_left (mrt_character_log_disk_growth q t) hcoef
  have htotal := he.trans hlog
  have hrecip : P / (c / (6 * H)) = (6 * P / c) * H := by field_simp
  change _ ≤ (mrtCharacterLogDerivativeConstant + P / (c / (6 * H))) * (A * H) at htotal
  rw [hrecip] at htotal
  have hlinear : H ≤ 2 * H ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlinear
    (mul_nonneg hA.le mrtCharacterLogDerivativeConstant_pos.le)
  have htotal' : ‖deriv (mrtCharacterNormalizedLFunction χ t) z /
      mrtCharacterNormalizedLFunction χ t z‖ ≤ C * H ^ 2 := by
    dsimp [C]
    nlinarith only [htotal, hmul]
  rw [mrtCharacterNormalized_logderiv_eq χ hχ t z hp, norm_mul,
    mrtCharacterPhysicalPoint_real] at htotal'
  norm_num at htotal'
  apply (le_mul_of_one_le_left (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans
  simpa only [norm_div] using htotal'

end TwoPointCorrelations

end OAI

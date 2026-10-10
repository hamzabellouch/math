import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombRawEvaluation

namespace OAI

/-! End-to-end error accounting for the actual Coulomb coefficient. -/

noncomputable section
namespace ContinuumCoulomb.CoulombEvaluation

theorem truncation_error (rho P : ℕ) (hrho : 0 < rho) (d : ℚ) :
    |localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ) -
      localizedCoulombBoxIntegral (GaussianFrequency.frequency rho)
        (1 / (denominator rho P : ℚ) : ℝ) (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)| ≤
      (4 * ((P : ℝ) + 1))⁻¹ := by
  have hf : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have ht := CoulombTruncationSchedule.error hf (truncationPrecision P) ((d : ℝ) • planarAxis 0)
  rw [← epsilon_eq] at ht
  apply ht.trans
  apply inv_anti₀ (by positivity)
  have h : P ≤ truncationPrecision P := by unfold truncationPrecision; omega
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right h 1) (by norm_num)

theorem rawPrecision_one_le (rho P : ℕ) : 1 ≤ (rawPrecision rho P : ℝ) := by
  have hc := (normalizationBound_bounds rho).1
  have hp : 1 ≤ (P : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]
  have hprod : 1 ≤ (normalizationBound rho : ℝ) * ((P : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le hc hp
  simp only [rawPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem rawApproximate_bound (rho P : ℕ) (hrho : 0 < rho) (d : ℚ) :
    |(rawApproximate rho P d : ℝ)| ≤ (rawMassBound rho : ℝ) * denominator rho P := by
  let I := localizedRawCoulombBox (GaussianFrequency.frequency rho)
    (1 / (denominator rho P : ℚ) : ℝ) (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)
  have hf : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have hD : (1 : ℝ) ≤ denominator rho P := by exact_mod_cast denominator_positive rho P
  have hε : (0 : ℝ) < (1 / (denominator rho P : ℚ) : ℝ) := by
    simp only [Rat.cast_natCast]
    positivity
  have hI := localizedRawCoulombBox_bound hf hε (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)
  rw [denominator_inverse] at hI
  have he := raw_approximation_error rho P hrho d
  have hS := rawPrecision_one_le rho P
  have he1 : |(rawApproximate rho P d : ℝ) - I| ≤ 1 := by
    apply he.trans
    rw [← div_eq_mul_inv]
    exact (div_le_one (by positivity : 0 < 4 * (rawPrecision rho P : ℝ))).mpr (by linarith)
  have htriangle : |(rawApproximate rho P d : ℝ)| ≤ |(rawApproximate rho P d : ℝ) - I| + |I| := by
    calc
      _ = |((rawApproximate rho P d : ℝ) - I) + I| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hM := rawMassBound_le rho
  have hMD := mul_le_mul_of_nonneg_right hM (show (0 : ℝ) ≤ denominator rho P by linarith)
  nlinarith

theorem raw_normalization_budget (rho P : ℕ) :
    CoulombNormalization.coefficient (GaussianFrequency.frequency rho) *
      (3 * (4 * (rawPrecision rho P : ℝ))⁻¹) ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
  have hC := (normalizationBound_bounds rho).1
  have hα := (normalizationBound_bounds rho).2
  have hp : (0 : ℝ) < P + 1 := by positivity
  calc
    _ ≤ (normalizationBound rho : ℝ) * (3 * (4 * (rawPrecision rho P : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_right hα (by positivity)
    _ = (3 / 16 : ℝ) * ((P : ℝ) + 1)⁻¹ := by
      simp only [rawPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      have hc0 : (normalizationBound rho : ℝ) ≠ 0 := ne_of_gt (by linarith)
      field_simp [hc0, hp.ne']
      ring
    _ ≤ _ := by rw [mul_inv]; norm_num; nlinarith [inv_pos.mpr hp]

theorem normalization_rounding_budget (rho P : ℕ) :
    (rawMassBound rho : ℝ) * denominator rho P *
      ((normalizationPrecision rho P : ℝ) + 1)⁻¹ ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
  have hM : (0 : ℝ) < rawMassBound rho := by
    have h := rawMassBound_le rho
    nlinarith [sq_nonneg (localizedRawMass (GaussianFrequency.frequency rho))]
  have hD : (0 : ℝ) < denominator rho P := by exact_mod_cast denominator_positive rho P
  have hp : (0 : ℝ) < P + 1 := by positivity
  have hn : (0 : ℝ) < normalizationPrecision rho P := by
    simp only [normalizationPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    positivity
  calc
    _ ≤ (rawMassBound rho : ℝ) * denominator rho P * (normalizationPrecision rho P : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ hn (by linarith)) (by positivity)
    _ = (8 * ((P : ℝ) + 1))⁻¹ := by
      simp only [normalizationPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      field_simp [hM.ne', hD.ne', hp.ne']
    _ ≤ _ := inv_anti₀ (by positivity) (by linarith)

theorem approximation_error (rho P : ℕ) (hrho : 0 < rho) (d : ℚ) :
    |(approximate rho P d : ℝ) - localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ)| ≤
      ((P : ℝ) + 1)⁻¹ := by
  let α := CoulombNormalization.coefficient (GaussianFrequency.frequency rho)
  let α' : ℝ := CoulombNormalization.approximate rho (normalizationPrecision rho P)
  let q : ℝ := rawApproximate rho P d
  let I := localizedRawCoulombBox (GaussianFrequency.frequency rho)
    (1 / (denominator rho P : ℚ) : ℝ) (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)
  have hf : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have hα0 : 0 ≤ α := by unfold α CoulombNormalization.coefficient; positivity
  have heq : α' * q - α * I = (α' - α) * q + α * (q - I) := by ring
  have hfirst : |(α' - α) * q| ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
    rw [abs_mul]
    have h := mul_le_mul (CoulombNormalization.approximation_error rho (normalizationPrecision rho P))
      (rawApproximate_bound rho P hrho d) (abs_nonneg q) (by positivity)
    apply h.trans
    simpa only [mul_comm] using normalization_rounding_budget rho P
  have hsecond : |α * (q - I)| ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
    rw [abs_mul, abs_of_nonneg hα0]
    exact (mul_le_mul_of_nonneg_left (raw_approximation_error rho P hrho d) hα0).trans
      (raw_normalization_budget rho P)
  have hbox := localizedCoulombBox_eq_normalizedRaw hf (1 / (denominator rho P : ℚ) : ℝ)
    (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)
  have ht := truncation_error rho P hrho d
  rw [hbox, abs_sub_comm] at ht
  have hinner := (abs_add_le ((α' - α) * q) (α * (q - I))).trans (add_le_add hfirst hsecond)
  rw [← heq] at hinner
  have hsum := (abs_sub_le (α' * q) (α * I)
    (localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ))).trans
      (add_le_add hinner ht)
  have hfinal : |α' * q - localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ)| ≤
      ((P : ℝ) + 1)⁻¹ := by
    apply hsum.trans
    rw [mul_inv]
    norm_num
    nlinarith [inv_pos.mpr (show (0 : ℝ) < P + 1 by positivity)]
  simpa only [approximate, Rat.cast_mul, α', q] using hfinal

end ContinuumCoulomb.CoulombEvaluation

end

end OAI

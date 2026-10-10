import OAI.NumberTheory.JointDickman.Arithmetic.TiltedSieveDensity

namespace OAI

/-! # Exponential moments of the actual three-coefficient mass -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem tilted_coefficient_triple_le_sieved (B Z j b c : ℕ)
    (Q₁ Q₂ Q₃ : Finset ℕ) {s₁ s₂ s₃ : ℝ}
    (h₁ : Real.exp s₁ ≤ 2) (h₂ : Real.exp s₂ ≤ 2) (h₃ : Real.exp s₃ ≤ 2) :
    tiltedCoefficientWeight B Q₁ s₁ b * tiltedCoefficientWeight B Q₂ s₂ c *
      tiltedCoefficientWeight B Q₃ s₃ (b + j * c) ≤
    coefficientScale B ^ 3 * mixedThreeFormSieveWeight (sievePrimes Z)
      (tiltedSieveTheta (auxiliaryCutoff B) Q₁ s₁)
      (tiltedSieveTheta (auxiliaryCutoff B) Q₂ s₂)
      (tiltedSieveTheta (auxiliaryCutoff B) Q₃ s₃) j b c := by
  have h := mul_le_mul
    (mul_le_mul (tiltedCoefficientWeight_le_sieved B Z Q₁ h₁ b)
      (tiltedCoefficientWeight_le_sieved B Z Q₂ h₂ c)
      (tiltedCoefficientWeight_nonneg B Q₂ s₂ c)
      (mul_nonneg (coefficientScale_nonneg B) (prod_nonneg (fun p _ =>
        residueWeight_nonneg _ _ (tiltedSieveTheta_bounds _ Q₁ h₁ p).1))))
    (tiltedCoefficientWeight_le_sieved B Z Q₃ h₃ (b + j * c))
    (tiltedCoefficientWeight_nonneg B Q₃ s₃ (b + j * c))
    (mul_nonneg
      (mul_nonneg (coefficientScale_nonneg B) (prod_nonneg (fun p _ =>
        residueWeight_nonneg _ _ (tiltedSieveTheta_bounds _ Q₁ h₁ p).1)))
      (mul_nonneg (coefficientScale_nonneg B) (prod_nonneg (fun p _ =>
        residueWeight_nonneg _ _ (tiltedSieveTheta_bounds _ Q₂ h₂ p).1))))
  apply h.trans_eq
  simp only [mixedThreeFormSieveWeight, Nat.cast_add, Nat.cast_mul, prod_mul_distrib]
  ring

theorem tilted_density_normalization
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ B Z : ℕ, 1 < B → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      ∀ (Q₁ Q₂ Q₃ : Finset ℕ) (s₁ s₂ s₃ : ℝ),
      Real.exp s₁ ≤ 2 → Real.exp s₂ ≤ 2 → Real.exp s₃ ≤ 2 →
      coefficientScale B ^ 3 * (tiltedSieveDensity (auxiliaryCutoff B) Z Q₁ s₁ *
        tiltedSieveDensity (auxiliaryCutoff B) Z Q₂ s₂ * tiltedSieveDensity (auxiliaryCutoff B) Z Q₃ s₃) ≤
      M * Real.exp (((Real.exp s₁ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₁ +
        ((Real.exp s₂ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₂ +
        ((Real.exp s₃ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₃) := by
  obtain ⟨M, hM0, hnorm⟩ := coefficient_sieve_density_bound hM hδ
  refine ⟨M ^ 3 * Real.exp 12, by positivity, ?_⟩
  intro B Z hB hPZ hlog Q₁ Q₂ Q₃ s₁ s₂ s₃ h₁ h₂ h₃
  let ρ := roughSieveDensity (auxiliaryCutoff B) Z
  let l₁ := ((Real.exp s₁ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₁
  let l₂ := ((Real.exp s₂ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₂
  let l₃ := ((Real.exp s₃ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₃
  have hd (Q : Finset ℕ) {s : ℝ} (hs : Real.exp s ≤ 2) : 0 ≤ tiltedSieveDensity (auxiliaryCutoff B) Z Q s := by
    unfold tiltedSieveDensity
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    apply sub_nonneg.mpr
    apply (div_le_one hp0).mpr
    linarith [(tiltedSieveTheta_bounds (auxiliaryCutoff B) Q hs p).1]
  have hρ := roughSieveDensity_nonneg (auxiliaryCutoff B) Z
  have hb₁ := tilted_sieve_density_bound (auxiliaryCutoff B) Z Q₁ h₁
  have hb₂ := tilted_sieve_density_bound (auxiliaryCutoff B) Z Q₂ h₂
  have hb₃ := tilted_sieve_density_bound (auxiliaryCutoff B) Z Q₃ h₃
  have hprod : tiltedSieveDensity (auxiliaryCutoff B) Z Q₁ s₁ *
      tiltedSieveDensity (auxiliaryCutoff B) Z Q₂ s₂ * tiltedSieveDensity (auxiliaryCutoff B) Z Q₃ s₃ ≤
      (ρ * Real.exp (l₁ + 4)) * (ρ * Real.exp (l₂ + 4)) * (ρ * Real.exp (l₃ + 4)) :=
    mul_le_mul (mul_le_mul hb₁ hb₂ (hd Q₂ h₂) (mul_nonneg hρ (Real.exp_pos _).le)) hb₃
      (hd Q₃ h₃) (mul_nonneg (mul_nonneg hρ (Real.exp_pos _).le) (mul_nonneg hρ (Real.exp_pos _).le))
  have hn := pow_le_pow_left₀ (mul_nonneg (coefficientScale_nonneg B) hρ) (hnorm B Z hB hPZ hlog) 3
  calc
    _ ≤ coefficientScale B ^ 3 * ((ρ * Real.exp (l₁ + 4)) * (ρ * Real.exp (l₂ + 4)) * (ρ * Real.exp (l₃ + 4))) :=
      mul_le_mul_of_nonneg_left hprod (pow_nonneg (coefficientScale_nonneg B) _)
    _ = (coefficientScale B * ρ) ^ 3 * Real.exp (l₁ + l₂ + l₃ + 12) := by
      have h12 : Real.exp (12 : ℝ) = Real.exp (4 : ℝ) ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      simp only [Real.exp_add, h12]
      ring
    _ ≤ M ^ 3 * Real.exp (l₁ + l₂ + l₃ + 12) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

theorem tilted_coefficient_three_form_with_remainder
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (Q₁ Q₂ Q₃ : Finset ℕ) (s₁ s₂ s₃ : ℝ),
      Real.exp s₁ ≤ 2 → Real.exp s₂ ≤ 2 → Real.exp s₃ ≤ 2 →
      (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂,
        tiltedCoefficientWeight B Q₁ s₁ b * tiltedCoefficientWeight B Q₂ s₂ c *
          tiltedCoefficientWeight B Q₃ s₃ (b + j * c)) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        Real.exp (((Real.exp s₁ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₁ +
          ((Real.exp s₂ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₂ +
          ((Real.exp s₃ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₃) +
        coefficientScale B ^ 3 *
          (2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) := by
  obtain ⟨C, hC, hsieve⟩ := mixed_three_form_rectangle_sieve hFord hM
  obtain ⟨M, hM0, hnorm⟩ := tilted_density_normalization hM hδ
  refine ⟨C * M, by positivity, ?_⟩
  intro B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ Q₁ Q₂ Q₃ s₁ s₂ s₃ h₁ h₂ h₃
  have hP (p : ℕ) (hp : p ∈ sievePrimes Z) : p.Prime ∧ p ≤ Z ∧ 6 ≤ p := by
    obtain ⟨hpZ, hp6⟩ := mem_filter.mp hp
    obtain ⟨hpZ, hpp⟩ := Nat.mem_primesLE.mp hpZ
    exact ⟨hpp, hpZ, hp6⟩
  have hs := hsieve (sievePrimes Z) (tiltedSieveTheta (auxiliaryCutoff B) Q₁ s₁)
    (tiltedSieveTheta (auxiliaryCutoff B) Q₂ s₂) (tiltedSieveTheta (auxiliaryCutoff B) Q₃ s₃)
    j l₁ r₁ l₂ r₂ Z hj hI hJ hZ hP (fun p _ => tiltedSieveTheta_bounds _ Q₁ h₁ p)
      (fun p _ => tiltedSieveTheta_bounds _ Q₂ h₂ p) (fun p _ => tiltedSieveTheta_bounds _ Q₃ h₃ p)
  have hn := hnorm B Z hB hPZ hlog Q₁ Q₂ Q₃ s₁ s₂ s₃ h₁ h₂ h₃
  have ha : 0 ≤ C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le (sub_nonneg.mpr (by exact_mod_cast hI)))
      (sub_nonneg.mpr (by exact_mod_cast hJ)))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) j))
  calc
    _ ≤ ∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂, coefficientScale B ^ 3 *
        mixedThreeFormSieveWeight (sievePrimes Z) (tiltedSieveTheta (auxiliaryCutoff B) Q₁ s₁)
          (tiltedSieveTheta (auxiliaryCutoff B) Q₂ s₂) (tiltedSieveTheta (auxiliaryCutoff B) Q₃ s₃) j b c :=
      sum_le_sum (fun b _ => sum_le_sum (fun c _ => tilted_coefficient_triple_le_sieved B Z j b c Q₁ Q₂ Q₃ h₁ h₂ h₃))
    _ = coefficientScale B ^ 3 * (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂,
        mixedThreeFormSieveWeight (sievePrimes Z) (tiltedSieveTheta (auxiliaryCutoff B) Q₁ s₁)
          (tiltedSieveTheta (auxiliaryCutoff B) Q₂ s₂) (tiltedSieveTheta (auxiliaryCutoff B) Q₃ s₃) j b c) := by
      simp_rw [mul_sum]
    _ ≤ coefficientScale B ^ 3 * _ := mul_le_mul_of_nonneg_left hs (pow_nonneg (coefficientScale_nonneg B) _)
    _ ≤ _ := by
      rw [mul_add]
      apply add_le_add (b := C * M * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j * _) ?_ le_rfl
      have h := mul_le_mul_of_nonneg_left hn ha
      convert h using 1 <;> unfold tiltedSieveDensity at * <;> ring

end JointDickman

end OAI

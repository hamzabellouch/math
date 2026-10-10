import OAI.NumberTheory.JointDickman.Arithmetic.CoefficientSieveMajorant

namespace OAI

/-! # The coefficient three-form bound with an explicit remainder -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficient_three_form_with_remainder
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z j u v w x : ℕ, 1 < B → 2 ≤ Z →
      auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z → j ≠ 0 → u ≤ v → w ≤ x →
      (∑ b ∈ Ico u v, ∑ c ∈ Ico w x,
        coefficientWeight B b * coefficientWeight B c * coefficientWeight B (b + j * c)) ≤
      C * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j +
        coefficientScale B ^ 3 *
          (2 * (((v : ℝ) - u) + ((x : ℝ) - w) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) := by
  obtain ⟨C, hC, hsieve⟩ := three_form_rectangle_sieve hFord hM
  obtain ⟨M, hM0, hnorm⟩ := coefficient_sieve_density_bound hM hδ
  refine ⟨C * M ^ 3, by positivity, ?_⟩
  intro B Z j u v w x hB hZ hPZ hlog hj huv hwx
  have hnormal := hnorm B Z hB hPZ hlog
  have hpow := pow_le_pow_left₀
    (mul_nonneg (coefficientScale_nonneg B) (roughSieveDensity_nonneg _ _)) hnormal 3
  have hP (p : ℕ) (hp : p ∈ sievePrimes Z) : p.Prime ∧ p ≤ Z ∧ 6 ≤ p := by
    obtain ⟨hpZ, hp6⟩ := mem_filter.mp hp
    obtain ⟨hpZ, hpp⟩ := Nat.mem_primesLE.mp hpZ
    exact ⟨hpp, hpZ, hp6⟩
  have hs := hsieve (sievePrimes Z) (roughSieveTheta (auxiliaryCutoff B)) j u v w x Z hj
    huv hwx hZ hP (fun p _ => roughSieveTheta_bounds _ p)
  have hprod : (∏ p ∈ sievePrimes Z, (1 - (1 - roughSieveTheta (auxiliaryCutoff B) p) / p)) =
      roughSieveDensity (auxiliaryCutoff B) Z := rfl
  rw [hprod] at hs
  have harea : 0 ≤ ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast huv))
      (sub_nonneg.mpr (by exact_mod_cast hwx)))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) j))
  calc
    _ ≤ ∑ b ∈ Ico u v, ∑ c ∈ Ico w x,
        coefficientScale B ^ 3 *
          threeFormSieveWeight (sievePrimes Z) (roughSieveTheta (auxiliaryCutoff B)) j b c :=
      sum_le_sum (fun b _ => sum_le_sum (fun c _ => coefficient_triple_le_sieved B Z j b c))
    _ = coefficientScale B ^ 3 *
        (∑ b ∈ Ico u v, ∑ c ∈ Ico w x,
          threeFormSieveWeight (sievePrimes Z) (roughSieveTheta (auxiliaryCutoff B)) j b c) := by
      simp_rw [mul_sum]
    _ ≤ coefficientScale B ^ 3 *
        (C * ((v : ℝ) - u) * ((x : ℝ) - w) *
          roughSieveDensity (auxiliaryCutoff B) Z ^ 3 * singularFactor 24 j +
          2 * (((v : ℝ) - u) + ((x : ℝ) - w) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hs (pow_nonneg (coefficientScale_nonneg B) _)
    _ ≤ _ := by
      rw [mul_add]
      apply add_le_add (b := C * M ^ 3 * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j) ?_ le_rfl
      calc
        _ = C * (coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z) ^ 3 *
            (((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j) := by ring
        _ ≤ C * M ^ 3 * (((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) harea
        _ = _ := by ring

end JointDickman

end OAI

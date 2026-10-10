import OAI.NumberTheory.DirichletL.CubicSieve.Mobius

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum DivisorBlockCauchy
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma descendedCoefficient_norm_le {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (d : O) (j : n) :
    ‖descendedCoefficient D cols a d j‖ ≤ ‖if D ∣ cols j then a j else 0‖ := by
  unfold descendedCoefficient
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right
    (elementCharacter_norm_le_one _ (totalQuotient_cubic_admissible D _ (hc j)).2 d)
    (norm_nonneg _)).trans_eq (one_mul _)

theorem descended_energy_small_power {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
      ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) ≤
        (divisorConstant ε hε * N^ε)^2 * ∑ j, ‖a j‖^2 := by
  have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
  let B := divisorConstant ε hε * N^ε
  have hB : 0 ≤ B := mul_nonneg (divisorConstant_pos ε hε).le (Real.rpow_nonneg hN0 _)
  have hcard (D : Ideal O) (hD : D ∈ columnDivisorPool cols) :
      ((idealDivisors D).card : ℝ) ≤ B := by
    have hd := columnDivisorPool_norm_bounds cols hc0 N hN D hD
    have hd0 : D ≠ 0 := by
      intro he
      have hh := hd.1
      norm_num [he] at hh
    exact ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 D hd0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hd.2 hε.le)
        (divisorConstant_pos ε hε).le)
  calc
    _ ≤ ∑ D ∈ columnDivisorPool cols, B * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      calc
        _ ≤ ∑ E ∈ idealDivisors D, ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          apply Finset.sum_le_sum
          intro E hE
          exact Finset.sum_le_sum (fun j hj => pow_le_pow_left₀ (norm_nonneg _)
            (descendedCoefficient_norm_le D cols hc a (idealGenerator E) j) 2)
        _ = ((idealDivisors D).card : ℝ) * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD) (by positivity)
    _ = B * (∑ D ∈ columnDivisorPool cols, ∑ j, ‖if D ∣ cols j then a j else 0‖^2) := by
      rw [Finset.mul_sum]
    _ ≤ B * (B * ∑ j, ‖a j‖^2) := mul_le_mul_of_nonneg_left
      (divisor_mask_energy_small_power ε hε _ cols hc0 N hN a) hB
    _ = _ := by dsimp [B]; ring

end
end SevenEighths.CubicSieve

end OAI

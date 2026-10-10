import OAI.MeasureTheory.Falconer.Geometry.ProjectionPowerBudget

namespace OAI

/-! One choice of a weak exponent absorbs every polynomial packet loss,
including the fortieth power arising in projection sampling. -/
namespace Falconer

theorem packet_polynomial_loss {θ C : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let E := Real.exp (ε*(N:ℝ)*Real.log 2)
      let D := Real.exp (θ*(N:ℝ)*Real.log 2)
      1 ≤ E ∧ 100 ≤ D ∧ 16*E^5 ≤ D ∧ C*((N:ℝ)+1)^2*E^48 ≤ D := by
  let A := 100+16+C
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨N0,hN0,hpoly⟩ := dyadic_quadratic_loss (by positivity : 0 < θ/2) hA
  refine ⟨θ/96,N0,by positivity,hN0,?_⟩
  intro N hN
  dsimp only
  let E := Real.exp ((θ/96)*(N:ℝ)*Real.log 2)
  let D := Real.exp (θ*(N:ℝ)*Real.log 2)
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hpoly1 : (1:ℝ) ≤ ((N:ℝ)+1)^2 := by
    have hh : (1:ℝ) ≤ (N:ℝ)+1 := by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith
    exact one_le_pow₀ hh
  have hE48 : E^48 = Real.exp ((θ/2)*(N:ℝ)*Real.log 2) := by
    dsimp [E]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hcost : A*((N:ℝ)+1)^2*E^48 ≤ D := by
    calc
      _ ≤ Real.exp ((θ/2)*(N:ℝ)*Real.log 2)*E^48 :=
        mul_le_mul_of_nonneg_right (hpoly N hN) (pow_nonneg hE0 _)
      _ = D := by rw [hE48,← Real.exp_add]; congr 1; ring
  have h48 : (1:ℝ) ≤ E^48 := one_le_pow₀ hE
  have h5 : E^5 ≤ E^48 := pow_le_pow_right₀ hE (by norm_num)
  refine ⟨hE,?_,?_,?_⟩
  · apply le_trans _ hcost
    calc
      (100:ℝ) ≤ A := by dsimp [A]; linarith only [hC]
      _ ≤ A*((N:ℝ)+1)^2 := le_mul_of_one_le_right hA hpoly1
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hA (sq_nonneg _)) h48
  · apply le_trans _ hcost
    calc
      16*E^5 ≤ 16*E^48 := mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ ≤ A*E^48 := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith only [hC]) (pow_nonneg hE0 _)
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right hA hpoly1
        exact mul_le_mul_of_nonneg_right hh (pow_nonneg hE0 _)
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith : C ≤ A) (sq_nonneg _))
      (pow_nonneg hE0 _)).trans hcost

end Falconer

end OAI

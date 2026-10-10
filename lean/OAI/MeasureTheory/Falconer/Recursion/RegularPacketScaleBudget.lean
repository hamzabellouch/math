import OAI.MeasureTheory.Falconer.Geometry.ProjectionPowerBudget

namespace OAI

/-! Reserve one fixed weak power for all regular-packet preparation losses:
the logarithmic selections, fixed grid constants and the exponent gap. -/
namespace Falconer

theorem regular_packet_scale_budget {κ θ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let N := n+2
      let K := Real.exp (ε*(N:ℝ)*Real.log 2)
      let D := K^2
      3 ≤ n ∧ 80 ≤ D ∧ projectionGapConstant κ ≤ D ∧
        13*K ≤ D ∧ 8*K ≤ D ∧ 10*(N:ℝ) ≤ D ∧
        D^40 ≤ Real.exp (θ*(N:ℝ)*Real.log 2) := by
  let ε := min (θ/80) 1
  let C := 80+projectionGapConstant κ
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  have hH := projectionGapConstant_pos hκ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N1,hN1,hpoly⟩ := dyadic_quadratic_loss hε hC
  refine ⟨ε,max N1 5,hε,min_le_right _ _,by omega,?_⟩
  intro n hn
  dsimp only
  let N := n+2
  let K := Real.exp (ε*(N:ℝ)*Real.log 2)
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hpoly' : C*((N:ℝ)+1)^2 ≤ K := hpoly N ((le_max_left _ _).trans hn)
  have hpoly1 : (1:ℝ) ≤ ((N:ℝ)+1)^2 := one_le_pow₀ (by linarith only [hN])
  have hCK : C ≤ K := (le_mul_of_one_le_right hC hpoly1).trans hpoly'
  have hK80 : 80 ≤ K := (show 80 ≤ C by dsimp [C]; linarith only [hH]).trans hCK
  have hK1 : 1 ≤ K := by linarith only [hK80]
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hKD : K ≤ K^2 := by nlinarith only [mul_le_mul_of_nonneg_left hK1 hK0]
  have h80poly : 80*((N:ℝ)+1)^2 ≤ K :=
    (mul_le_mul_of_nonneg_right (show 80 ≤ C by dsimp [C]; linarith only [hH]) (sq_nonneg _)).trans hpoly'
  have h13 : 13*K ≤ K^2 := by nlinarith only [mul_le_mul_of_nonneg_right hK80 hK0]
  have h8 : 8*K ≤ K^2 := by nlinarith only [mul_le_mul_of_nonneg_right hK80 hK0]
  refine ⟨by omega,hK80.trans hKD,?_,h13,h8,?_,?_⟩
  · exact (show projectionGapConstant κ ≤ C by dsimp [C]; linarith).trans (hCK.trans hKD)
  · have hh : 10*(N:ℝ) ≤ K := by nlinarith only [h80poly,hN,sq_nonneg (N:ℝ)]
    exact hh.trans hKD
  · change (K^2)^40 ≤ _
    rw [← pow_mul]
    change (Real.exp (ε*(N:ℝ)*Real.log 2))^(2*40) ≤ _
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have he : 80*ε ≤ θ := by
      have hh := min_le_left (θ/80) (1:ℝ)
      dsimp [ε]
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right he (mul_nonneg hN (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))
    convert hh using 1 <;> dsimp [N] <;> push_cast <;> ring

end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Geometry.ProjectionPowerBudget

namespace OAI

/-! Choose one even block width so that all block-label and fixed per-block
losses fit the prescribed weak exponent, uniformly in the total depth. -/
namespace Falconer

theorem exists_even_profile_block_budget {ε : ℝ} (hε : 0 < ε) (c : ℕ) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∀ m : ℕ, 0 < m →
      (((2*B+1:ℕ):ℝ)^(m+1))*(2:ℝ)^(c*(m+1)) ≤
        (2:ℝ)^(ε*((B*m:ℕ):ℝ)) := by
  obtain ⟨B0,hB0,hbudget⟩ := dyadic_quadratic_loss (half_pos hε)
    (show 0 ≤ 3*(2:ℝ)^c by positivity)
  let B := 2*B0
  have hB : 0 < B := by dsimp [B]; omega
  have hBge : B0 ≤ B := by dsimp [B]; omega
  have hbase : ((2*B+1:ℕ):ℝ)*(2:ℝ)^c ≤ (2:ℝ)^((ε/2)*(B:ℝ)) := by
    have hh := hbudget B hBge
    have hdom : ((2*B+1:ℕ):ℝ) ≤ 3*((B:ℝ)+1)^2 := by
      push_cast
      nlinarith only [sq_nonneg (B:ℝ),Nat.cast_nonneg (α := ℝ) B]
    calc
      _ ≤ (3*((B:ℝ)+1)^2)*(2:ℝ)^c := mul_le_mul_of_nonneg_right hdom (by positivity)
      _ = (3*(2:ℝ)^c)*((B:ℝ)+1)^2 := by ring
      _ ≤ Real.exp ((ε/2)*(B:ℝ)*Real.log 2) := hh
      _ = _ := by rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; congr 1; ring
  refine ⟨B,hB,⟨B0,by dsimp [B]; omega⟩,?_⟩
  intro m hm
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hlength : (ε/2)*(B:ℝ)*(m+1:ℕ) ≤ ε*((B*m:ℕ):ℝ) := by
    push_cast
    have hh := mul_le_mul_of_nonneg_left (show (m:ℝ)+1 ≤ 2*(m:ℝ) by linarith only [hmR])
      (show 0 ≤ (ε/2)*(B:ℝ) by positivity)
    nlinarith only [hh]
  calc
    _ = (((2*B+1:ℕ):ℝ)*(2:ℝ)^c)^(m+1) := by rw [mul_pow,pow_mul]
    _ ≤ ((2:ℝ)^((ε/2)*(B:ℝ)))^(m+1) := pow_le_pow_left₀ (by positivity) hbase _
    _ = (2:ℝ)^((ε/2)*(B:ℝ)*(m+1:ℕ)) :=
      (Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlength

end Falconer

end OAI

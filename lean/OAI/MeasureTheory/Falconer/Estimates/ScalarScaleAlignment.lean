import OAI.MeasureTheory.Falconer.Estimates.ScalarResolution

namespace OAI

/-! Align any fine dyadic resolution with a fixed block width. The
 difference is at most one block and all covering losses stay fixed. -/
namespace Falconer

 theorem scalar_block_ceiling_bounds (N B : ℕ) (hB : 0 < B) :
    N < B*(N/B+1) ∧ B*(N/B+1) ≤ N+B := by
  have hm := Nat.mod_lt N hB
  have he := Nat.mod_add_div N B
  rw [Nat.mul_add,Nat.mul_one]
  constructor <;> omega

 theorem scalar_block_scale_comparison (N B : ℕ) (hB : 0 < B) :
    (1/2:ℝ)^(B*(N/B+1)) ≤ (1/2:ℝ)^N ∧
    (1/2:ℝ)^N ≤ ((2:ℝ)^B)*(1/2:ℝ)^(B*(N/B+1)) := by
  obtain ⟨hlo,hhi⟩ := scalar_block_ceiling_bounds N B hB
  refine ⟨pow_le_pow_of_le_one (by norm_num) (by norm_num) hlo.le,?_⟩
  have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) hhi
  rw [pow_add] at hh
  have hc : (2:ℝ)^B*(1/2:ℝ)^B = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((2:ℝ)^B*(1/2:ℝ)^B)*(1/2:ℝ)^N := by rw [hc,one_mul]
    _ = (2:ℝ)^B*((1/2:ℝ)^N*(1/2:ℝ)^B) := by ring
    _ ≤ (2:ℝ)^B*(1/2:ℝ)^(B*(N/B+1)) := mul_le_mul_of_nonneg_left hh (by positivity)

 theorem scalar_fixed_losses {η C D : ℝ} (hη : 0 < η) (hC : 0 < C) (hD : 0 < D) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*Real.exp ((η/4)*(N:ℝ)*Real.log 2) ≤ Real.exp (η*(N:ℝ)*Real.log 2) ∧
      D*Real.exp ((η/4)*(N:ℝ)*Real.log 2) ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1
    (max (Real.log C) (Real.log D)/((3*η/4)*Real.log 2)))
  have hNpos : 0 < N0 := by
    have hh := (le_max_left _ _).trans_lt hN0
    exact_mod_cast (show (0:ℝ) < N0 by linarith)
  have hbase : max (Real.log C) (Real.log D) ≤ (3*η/4)*(N0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (by positivity : 0 < (3*η/4)*Real.log 2)).1
      ((le_max_right _ _).trans_lt hN0)
    nlinarith
  refine ⟨N0,hNpos,?_⟩
  intro N hN
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hN)
    (show 0 ≤ (3*η/4)*Real.log 2 by positivity)
  have hmax : max (Real.log C) (Real.log D) ≤ (3*η/4)*(N:ℝ)*Real.log 2 := by nlinarith
  constructor
  · calc
      _ = Real.exp (Real.log C+(η/4)*(N:ℝ)*Real.log 2) := by rw [Real.exp_add,Real.exp_log hC]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [le_max_left (Real.log C) (Real.log D)])
  · calc
      _ = Real.exp (Real.log D+(η/4)*(N:ℝ)*Real.log 2) := by rw [Real.exp_add,Real.exp_log hD]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [le_max_right (Real.log C) (Real.log D)])

end Falconer

end OAI

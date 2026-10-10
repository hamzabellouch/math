import OAI.MeasureTheory.Falconer.Estimates.RegularizationScales
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

namespace PlanarFalconer

theorem exists_bounded_regularization_control {lam : ℝ} (hlam : 0 < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
      ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧
      (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam := by
  let H := Nat.floor (1/lam)+1
  have hH : 0 < H := Nat.succ_pos _
  have hHlo : 1/lam < (H:ℝ) := by simpa only [H,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (1/lam)
  have hHhi : (H:ℝ) ≤ 1/lam+2 := by
    have hh := Nat.floor_le (by positivity : 0 ≤ 1/lam)
    dsimp [H]
    push_cast
    linarith
  have hHl : 1 ≤ lam*(H:ℝ) := by
    simpa only [mul_comm] using ((div_lt_iff₀ hlam).mp hHlo).le
  obtain ⟨M,hM⟩ := exists_nat_gt (((2*H+1:ℕ):ℝ)/lam)
  refine ⟨H,max H M,hH,hHhi,?_⟩
  intro N hN
  have hHN : H ≤ N := (le_max_left _ _).trans hN
  have hMN : M ≤ N := (le_max_right _ _).trans hN
  have hc := division_blocks_control hH hHN
  refine ⟨lt_of_lt_of_le hH hHN,hc.1,hc.2,division_block_width hlam.le hHl,?_⟩
  have hreal : ((2*H+1:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hm := (div_lt_iff₀ hlam).mp hM
    have hn : (M:ℝ) ≤ N := by exact_mod_cast hMN
    exact hm.le.trans (mul_le_mul_of_nonneg_right hn hlam.le)
  have hcount : ((N/(N/H)+2:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hh : N/(N/H)+2 ≤ 2*H+1 := by omega
    have hhR : ((N/(N/H)+2:ℕ):ℝ) ≤ ((2*H+1:ℕ):ℝ) := by exact_mod_cast hh
    exact hhR.trans hreal
  rw [← Real.rpow_natCast (2:ℝ) (N/(N/H)+2),← Real.rpow_natCast (2:ℝ) N,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcount

end PlanarFalconer

end OAI

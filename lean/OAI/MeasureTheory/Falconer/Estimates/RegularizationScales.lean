import OAI.MeasureTheory.Falconer.Recursion.BlockRegularization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

namespace PlanarFalconer

theorem division_blocks_control {H N : ℕ} (hH : 0 < H) (hN : H ≤ N) :
    0 < N/H ∧ N/(N/H)+1 ≤ 2*H := by
  have hB : 0 < N/H := Nat.div_pos hN hH
  have hrem : N < (N/H+1)*H := by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N hH
  have hmul : (N/H+1)*H ≤ (2*(N/H))*H := Nat.mul_le_mul_right H (by omega)
  have hlt : N < (2*H)*(N/H) := by
    calc
      N < (N/H+1)*H := hrem
      _ ≤ (2*(N/H))*H := hmul
      _ = (2*H)*(N/H) := by ac_rfl
  have hdiv : N/(N/H) < 2*H := (Nat.div_lt_iff_lt_mul hB).mpr hlt
  exact ⟨hB,by omega⟩

theorem division_block_width {H N : ℕ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hH : 1 ≤ lam*(H:ℝ)) : ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) := by
  have hn : (((N/H)*H:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.div_mul_le_self N H
  have h0 : 0 ≤ ((N/H:ℕ):ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hH h0
  have hl := mul_le_mul_of_nonneg_left hn hlam
  simp only [Nat.cast_mul, mul_one] at hh hl
  nlinarith

theorem exists_regularization_block_control {lam : ℝ} (hlam : 0 < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧ ∀ N ≥ N₀,
      0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
      ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧
      (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam := by
  obtain ⟨H,hH⟩ := exists_nat_gt (1/lam)
  have hHp : 0 < H := by
    have hp : 0 < (H:ℝ) := (one_div_pos.mpr hlam).trans hH
    exact_mod_cast hp
  have hHl : 1 ≤ lam*(H:ℝ) := by
    have := (div_lt_iff₀ hlam).mp hH
    nlinarith
  obtain ⟨M,hM⟩ := exists_nat_gt (((2*H+1:ℕ):ℝ)/lam)
  refine ⟨H,max H M,hHp,?_⟩
  intro N hN
  have hHN : H ≤ N := (le_max_left _ _).trans hN
  have hMN : M ≤ N := (le_max_right _ _).trans hN
  have hc := division_blocks_control hHp hHN
  refine ⟨lt_of_lt_of_le hHp hHN,hc.1,hc.2,division_block_width hlam.le hHl,?_⟩
  have hreal : ((2*H+1:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hm := (div_lt_iff₀ hlam).mp hM
    have hn : (M:ℝ) ≤ N := by exact_mod_cast hMN
    nlinarith
  have hcount : ((N/(N/H)+2:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hh : N/(N/H)+2 ≤ 2*H+1 := by omega
    have hhR : ((N/(N/H)+2:ℕ):ℝ) ≤ ((2*H+1:ℕ):ℝ) := by exact_mod_cast hh
    exact hhR.trans hreal
  rw [← Real.rpow_natCast (2:ℝ) (N/(N/H)+2), ← Real.rpow_natCast (2:ℝ) N,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcount

theorem blockDepth_brackets {N n B : ℕ} (hn : n ≤ N) (hB : 0 < B) :
    let i := (N-n)/B
    i < N/B+1 ∧ blockDepth N B (i+1) ≤ n ∧ n ≤ blockDepth N B i ∧
      blockDepth N B i-n ≤ B ∧ n-blockDepth N B (i+1) ≤ B := by
  dsimp only
  have hlo := Nat.div_mul_le_self (N-n) B
  have hhi := Nat.lt_mul_div_succ (N-n) hB
  have hi : (N-n)/B ≤ N/B := Nat.div_le_div_right (Nat.sub_le _ _)
  simp only [blockDepth]
  rw [Nat.mul_comm B] at hhi
  have hgap := blockDepth_gap N B ((N-n)/B)
  dsimp only [blockDepth] at hgap
  omega

end PlanarFalconer

end OAI

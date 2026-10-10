import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailAngularMiddle
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailRange
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeHeightBlock
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeHeightRanges

namespace OAI

/-! The original angular semiprime windows above the local Hecke height
have arbitrary logarithmic cancellation, uniformly in the angular index. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem semiprimeGaussTail_angular_high_piece
    (hHuxley : HuxleyAdditiveLargeSieve) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (ℓ : ℤ) (H U : ℝ) (i j : ℕ),
      1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) → U < 2*Real.pi*H →
      (min (semiprimePartitionScale i) (semiprimePartitionScale j))^(7/20:ℝ) < U →
      ‖semiprimeGaussTailPiece ℓ H U X i j‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨K,B₀,hK,hmiddle⟩ := semiprimeGaussTail_angular_middle_window hHuxley hMV hC k
  refine ⟨K*3^(5/6:ℝ)/(39/100:ℝ)^k,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (3:ℝ),
    eventually_semiprimeGaussTail_admissible (by norm_num : (0:ℝ) < 1) 0 B₀,
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 2/5) 2,
    eventually_tailPrime_small_group_length (D:=8) (K:=4^(27/25:ℝ))
      (by norm_num) (by positivity),
    eventually_tailPrime_middle_upper,
    eventually_tailPrime_middle_height (C:=4) (by norm_num),
    eventually_tailPrime_large_height_cap (by norm_num : (1/3000:ℝ) ≤ 1/1500)]
    with X hX hadm hlower hsmall hupper hheight hcap
  intro ℓ H U i j hH hHX hUH hU
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hlogX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX1]
  have hordered (i j : ℕ) (hji : semiprimePartitionScale j ≤ semiprimePartitionScale i)
      (hU : (semiprimePartitionScale j)^(7/20:ℝ) < U)
      (hne : semiprimeGaussTailPiece ℓ H U X i j ≠ 0) :
      ‖semiprimeGaussTailPiece ℓ H U X i j‖ ≤
        (K*3^(5/6:ℝ)/(39/100:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
    let A := semiprimePartitionScale i
    let B := semiprimePartitionScale j
    have hAp : 0 < A := semiprimePartitionScale_pos i
    have hBp : 0 < B := semiprimePartitionScale_pos j
    obtain ⟨hB₀,_,_,_⟩ := hadm ℓ H U i j hji hne
    obtain ⟨hABlo,hAB,_,hBL⟩ := semiprimeGaussTailPiece_nonzero_lengths ℓ H U hXp hne
    have hBX : X^(39/100:ℝ) ≤ B := by dsimp [B]; linarith
    have hBs : B ≤ X^(12/25:ℝ) := by
      apply le_of_not_ge
      intro hb
      have hc := (mul_le_mul_of_nonneg_left hHX (by positivity : 0 ≤ 2*Real.pi)).trans
        (hcap B hb)
      exact (not_le_of_gt hU) (hUH.le.trans hc)
    have hAl : (4*B)^(27/25:ℝ) ≤ A := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hBp.le]
      exact hsmall A B hBp hABlo hBs
    have hAU : A ≤ B^(19/10:ℝ) := hupper A B hBp hAB hBX
    have hUU : (4*B)^(1/50:ℝ) ≤ U := by
      apply (hheight B hBp hBs).trans
      apply (Real.rpow_le_rpow_of_exponent_le hX1
        (by norm_num : (1/100:ℝ) ≤ 13/100)).trans
      exact (semiprime_height_power hX1 hBX).trans hU.le
    have hHB : H ≤ B^3 := by
      apply hHX.trans
      apply tailPrime_height_cube hX1 (by norm_num : (1/3000:ℝ) ≤ 1/1500)
      exact (Real.rpow_le_rpow_of_exponent_le hX1
        (by norm_num : (1/4:ℝ) ≤ 39/100)).trans hBX
    exact (hmiddle ℓ H U X i j hB₀ hAl hAU hUU hH hHB hXp hUH).trans
      (semiprime_bilinear_scale hX1 hAp.le hBX hK.le hAB k)
  by_cases hne : semiprimeGaussTailPiece ℓ H U X i j = 0
  · rw [hne,norm_zero]
    positivity
  by_cases hji : semiprimePartitionScale j ≤ semiprimePartitionScale i
  · exact hordered i j hji (by simpa only [min_eq_right hji] using hU) hne
  · have hij := le_of_not_ge hji
    have hh := hordered j i hij (by simpa only [min_eq_left hij] using hU)
      (by rwa [semiprimeGaussTailPiece_symm ℓ H U X j i])
    simpa only [semiprimeGaussTailPiece_symm ℓ H U X j i] using hh

end CubicFirstMoment

end

end OAI

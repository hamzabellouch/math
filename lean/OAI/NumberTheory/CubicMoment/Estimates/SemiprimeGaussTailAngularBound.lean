import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailAngularHecke
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailAngularMiddle
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeHeightBlock
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeHeightRanges

namespace OAI

/-! Every actual radial semiprime window is controlled, including the heights
above the published Hecke range. The latter use the enlarged all-height
prime-product dispersion estimate. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem semiprimeGaussTail_angular_piece_log_saving
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (k : ℕ) :
    ∃ (K : ℝ) (m : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H U : ℝ) (i j : ℕ), 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      (1+Real.log X)^m ≤ U → U < 2*Real.pi*H →
      ‖semiprimeGaussTailPiece ℓ H U X i j‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨η,G,K₁,B₁,m,hη,hK₁,hhecke⟩ :=
    semiprimeGaussTail_angular_hecke_window ℓ hpub hHuxley hperiod hMV hC hGI hGQ k
  obtain ⟨K₂,B₂,hK₂,hmiddle⟩ := semiprimeGaussTail_angular_middle_window hHuxley hMV hC k
  let K₀ := K₁+K₂
  have hK₀ : 0 < K₀ := add_pos hK₁ hK₂
  refine ⟨K₀*3^(5/6:ℝ)/(39/100:ℝ)^k,m,by dsimp [K₀]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (3:ℝ),
    eventually_semiprimeGaussTail_admissible hη G (max B₁ B₂),
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 2/5) 2,
    eventually_tailPrime_small_group_length (D:=8) (K:=4^(27/25:ℝ))
      (by norm_num) (by positivity),
    eventually_tailPrime_middle_upper,
    eventually_tailPrime_middle_height (C:=4) (by norm_num),
    eventually_tailPrime_large_height_cap (by norm_num : (1/3000:ℝ) ≤ 1/1500)]
    with X hX hadm hlower hsmall hupper hheight hcap
  intro H U i j hH hHX hU hUH
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hlogX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX1]
  have hordered (i j : ℕ) (hji : semiprimePartitionScale j ≤ semiprimePartitionScale i)
      (hne : semiprimeGaussTailPiece ℓ H U X i j ≠ 0) :
      ‖semiprimeGaussTailPiece ℓ H U X i j‖ ≤
        (K₀*3^(5/6:ℝ)/(39/100:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
    let A := semiprimePartitionScale i
    let B := semiprimePartitionScale j
    have hAp : 0 < A := semiprimePartitionScale_pos i
    have hBp : 0 < B := semiprimePartitionScale_pos j
    obtain ⟨hB₀,hrough,hAlo,hAhi⟩ := hadm ℓ H U i j hji hne
    obtain ⟨hABlo,hAB,_,hBL⟩ := semiprimeGaussTailPiece_nonzero_lengths ℓ H U hXp hne
    have hBX : X^(39/100:ℝ) ≤ B := by dsimp [B]; linarith
    have hB1 : 1 ≤ B := (Real.one_le_rpow hX1 (by norm_num : (0:ℝ) ≤ 39/100)).trans hBX
    have hA1 : 1 ≤ A := hB1.trans hji
    have hBXhi : B ≤ X := by
      have hBB : B*B ≤ 3*X := (mul_le_mul_of_nonneg_right hji hBp.le).trans hAB
      nlinarith
    have hlog : 1+Real.log B ≤ 1+Real.log X := by linarith [Real.log_le_log hBp hBXhi]
    have hden : 0 ≤ (1+Real.log B)^k :=
      pow_nonneg (by linarith [Real.log_nonneg hB1]) k
    have hUl : (1+Real.log B)^m ≤ U :=
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hB1]) hlog m).trans hU
    have hraw : ‖semiprimeGaussTailPiece ℓ H U X i j‖ ≤
        K₀*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
      by_cases hUs : U ≤ B^(7/20:ℝ)
      · rw [semiprimeGaussTailPiece_eq_angularUnitWindow ℓ H U hXp i j]
        have hh := hhecke (A/X^(2/5:ℝ)) (B/X^(2/5:ℝ)) A B H U X
          (by positivity) (by positivity) hA1 hB1 ((le_max_left B₁ B₂).trans hB₀)
          hrough ((Real.rpow_le_rpow_of_exponent_le hB1
            (by linarith : 1-η/4 ≤ 1-η/16)).trans hAlo) hAhi hUl hUs
          (zero_lt_one.trans_le hH) hXp
        apply hh.trans
        apply div_le_div_of_nonneg_right ?_ hden
        apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hBp.le _)
        exact mul_le_mul_of_nonneg_right (by dsimp [K₀]; linarith) (Real.rpow_nonneg hAp.le _)
      · have hBs : B ≤ X^(12/25:ℝ) := by
          apply le_of_not_ge
          intro hb
          have hc := (mul_le_mul_of_nonneg_left hHX (by positivity : 0 ≤ 2*Real.pi)).trans
            (hcap B hb)
          exact hUs (hUH.le.trans hc)
        have hAl : (4*B)^(27/25:ℝ) ≤ A := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hBp.le]
          exact hsmall A B hBp hABlo hBs
        have hAU : A ≤ B^(19/10:ℝ) := hupper A B hBp hAB hBX
        have hUU : (4*B)^(1/50:ℝ) ≤ U := by
          apply (hheight B hBp hBs).trans
          apply (Real.rpow_le_rpow_of_exponent_le hX1
            (by norm_num : (1/100:ℝ) ≤ 13/100)).trans
          exact (semiprime_height_power hX1 hBX).trans (le_of_not_ge hUs)
        have hHB : H ≤ B^3 := by
          apply hHX.trans
          apply tailPrime_height_cube hX1 (by norm_num : (1/3000:ℝ) ≤ 1/1500)
          exact (Real.rpow_le_rpow_of_exponent_le hX1
            (by norm_num : (1/4:ℝ) ≤ 39/100)).trans hBX
        have hh := hmiddle ℓ H U X i j ((le_max_right B₁ B₂).trans hB₀)
          hAl hAU hUU hH hHB hXp hUH
        apply hh.trans
        apply div_le_div_of_nonneg_right ?_ hden
        apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hBp.le _)
        exact mul_le_mul_of_nonneg_right (by dsimp [K₀]; linarith) (Real.rpow_nonneg hAp.le _)
    exact hraw.trans (semiprime_bilinear_scale hX1 hAp.le hBX (by dsimp [K₀]; positivity) hAB k)
  by_cases hne : semiprimeGaussTailPiece ℓ H U X i j = 0
  · rw [hne,norm_zero]
    positivity
  by_cases hji : semiprimePartitionScale j ≤ semiprimePartitionScale i
  · exact hordered i j hji hne
  · have hh := hordered j i (le_of_not_ge hji)
      (by rwa [semiprimeGaussTailPiece_symm ℓ H U X j i])
    simpa only [semiprimeGaussTailPiece_symm ℓ H U X j i] using hh

end CubicFirstMoment

end

end OAI

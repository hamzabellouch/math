import OAI.NumberTheory.CubicMoment.Estimates.SmallBHeightPowers

namespace OAI

/-! A genuine absolute power saving for the noncube height mass of an
arbitrary squarefree coefficient sequence in the small-frequency range. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_noncube_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := smallB_noncube_height_blocks hMV hC hHuxley
    (by norm_num : (0:ℝ) < 1/10000)
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨CL,hCL,hlog⟩ := smallB_log_square_bound
  refine ⟨K*(11664+2*CI*CL),by positivity,?_⟩
  intro S H β Z B T u ℓ hZ hB hT hS hsize hH
  let V := 5832*(Z:ℝ)^(1/1000:ℝ)
  have hZp : 0 < (Z:ℝ) := zero_lt_one.trans_le hZ
  have hTp : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  have hB2 : B ≤ (Z:ℝ)^2 := by
    calc
      B ≤ 8*B := by linarith
      _ ≤ (Z:ℝ)^(3/4:ℝ) := hsize
      _ ≤ _ := by
        rw [← Real.rpow_natCast (Z:ℝ) 2]
        exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  have hb := hbound S H β Z B V T u ℓ hZ (zero_le_one.trans hB)
    (by dsimp [V]; positivity) hTp hS hsize hH
  have hs := smallB_height_bracket_power hZ hT hCI.le hCL
    (hcount V B Z hB hZ hB2) (hlog Z hZ)
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ K*B^(1/3:ℝ)*(∑ b ∈ S, ‖β b‖^2) by positivity)
  convert hm using 1
  ring

end CubicFirstMoment

end

end OAI

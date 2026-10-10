import OAI.NumberTheory.CubicMoment.Estimates.SmallBAllFrequency
import OAI.NumberTheory.CubicMoment.Estimates.UniformHeightMellin

namespace OAI

/-! The actual arbitrary-coefficient small-B mass over the entire Mellin
line. The height bound is uniform in translation, so no tail is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma finite_character_mass_bound (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ b ∈ S, primary b) (ℓ : ℤ) (t : ℝ) :
    ‖∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase t (norm b)‖^2‖ ≤
      (H.card:ℝ)*S.card*∑ b ∈ S, ‖β b‖^2 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  have hrow (h : Eisenstein) :
      ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase t (norm b)‖^2 ≤
      (S.card:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    apply (norm_sum_sq_le_card_mul S _).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro b hb
    apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
    simp only [norm_mul,norm_theta (primary_ne_zero (hS b hb)),mellinPhase_norm,mul_one]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS b hb) h)
  apply (Finset.sum_le_sum (fun h _ => hrow h)).trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

theorem smallB_arithmeticMellin_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u ρ ε : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 ≤ ρ → (ε = 1 ∨ ε = -1) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖arithmeticMellinCoefficient M hM V hV hV' ρ (ε*s)‖*
          ∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*
            mellinPhase (t+u+s) (norm b)‖^2) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hpower⟩ := smallB_all_frequency_height_power hMV hC hHuxley
  obtain ⟨D,hD,hmellin⟩ := arithmeticMellin_signed_height_uniform M hM V hV hV' q
  refine ⟨D*K,mul_pos hD hK,?_⟩
  intro S H β Z B T u ρ ε ℓ hZ hB hT hρ hε hS hsize hH
  let G := fun t => ∑ h ∈ H, ‖∑ b ∈ S,
    β b*cubicSymbol b h*theta ℓ b*mellinPhase t (norm b)‖^2
  let E := (H.card:ℝ)*S.card*∑ b ∈ S, ‖β b‖^2
  let A := K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2
  have hgc : Continuous G := by
    apply continuous_finsetSum
    intro h hh
    convert (continuous_finite_character_height S β h ℓ 0).norm.pow 2 using 1
    ext t
    simp only [Pi.pow_apply,add_zero]
  have hgb : ∀ t, ‖G t‖ ≤ E := fun t => finite_character_mass_bound S H β
    (fun b hb => (hS b hb).1) ℓ t
  have hTp : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hT
  have havg : ∀ v, dyadicHeightMean (fun t => G (t+v)) T ≤ A := fun v =>
    hpower S H β Z B T v ℓ hZ hB hT hS hsize hH
  have hm := hmellin ρ hρ G hgc E A T u ε hε (by dsimp [A]; positivity) hTp hgb havg
  convert hm using 1
  dsimp [A]
  ring

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Estimates.NormMellinMoments
import OAI.NumberTheory.CubicMoment.Estimates.ArithmeticMellinMoments

namespace OAI

/-! A bounded finite mass is integrated using its local bound and a
polynomial kernel moment. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem integral_bounded_mellin_window {f g : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ t, 0 ≤ f t) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {B C T : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hT : 0 < T) (k : ℕ)
    (hfk : Integrable (fun t : ℝ => ‖t‖^k*f t))
    (hgC : ∀ t, g t ≤ C) (hsmall : ∀ t, ‖t‖ ≤ T → g t ≤ B) :
    (∫ t : ℝ, f t*g t) ≤ B*(∫ t : ℝ, f t)+C/T^k*(∫ t : ℝ, ‖t‖^k*f t) := by
  have hi : Integrable (fun t : ℝ => f t*g t) := hf.mul_bdd hg.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hg0 t)]
      exact hgC t))
  have hm := (hf.const_mul B).add (hfk.const_mul (C/T^k))
  calc
    _ ≤ ∫ t : ℝ, B*f t+(C/T^k)*(‖t‖^k*f t) := by
      apply integral_mono hi hm
      intro t
      calc
        _ ≤ f t*(B+C/T^k*‖t‖^k) :=
          mul_le_mul_of_nonneg_left (mellin_window_majorant hB hC hT k hgC hsmall t) (hf0 t)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = _ := by rw [integral_add (hf.const_mul B) (hfk.const_mul (C/T^k)),
      integral_const_mul,integral_const_mul]

theorem arithmeticMellin_bounded_window (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q k : ℕ) :
    ∃ D₀ Dk : ℝ, 0 < D₀ ∧ 0 < Dk ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ (g : ℝ → ℝ), Continuous g → (∀ t, 0 ≤ g t) →
      ∀ B C T : ℝ, 0 ≤ B → 0 ≤ C → 0 < T →
      (∀ t, g t ≤ C) → (∀ t, ‖t‖ ≤ T → g t ≤ B) →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*g t) ≤
        B*D₀+C/T^k*Dk := by
  obtain ⟨D₀,hD₀,hzero⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q 0
  obtain ⟨Dk,hDk,hk⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q k
  refine ⟨D₀,Dk,hD₀,hDk,?_⟩
  intro ρ hρ g hg hg0 B C T hB hC hT hgC hsmall
  let F := arithmeticMellinCoefficient M hM V hV hV' ρ
  have hi := integral_bounded_mellin_window
    (arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm
    (fun t => _root_.norm_nonneg (F t)) hg hg0 hB hC hT k
    (arithmeticMellinCoefficient_moment_integrable M hM V hV hV' ρ k) hgC hsmall
  have hz : (1+ρ)^q*(∫ t : ℝ, ‖F t‖) ≤ D₀ := by
    simpa only [pow_zero,one_mul] using hzero ρ hρ
  calc
    _ ≤ (1+ρ)^q*(B*(∫ t : ℝ, ‖F t‖)+C/T^k*(∫ t : ℝ, ‖t‖^k*‖F t‖)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = B*((1+ρ)^q*(∫ t : ℝ, ‖F t‖))+
        C/T^k*((1+ρ)^q*(∫ t : ℝ, ‖t‖^k*‖F t‖)) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hz hB)
      (mul_le_mul_of_nonneg_left (hk ρ hρ) (by positivity))

lemma polynomial_mellin_tail_absorb {L z E : ℝ} (hL : 0 < L) (hz : 0 < z)
    (b k : ℕ) (hlog : E*z^(b+k) ≤ L) :
    (E*L^4*z^b)/(L^(1/4:ℝ))^12 ≤ L^2/z^k := by
  have he : (L^(1/4:ℝ))^12 = L^3 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
    norm_num
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hL 3) (pow_pos hz k)).mpr
  have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt (pow_pos hL 4))
  rw [pow_add] at hm
  nlinarith only [hm]

end CubicFirstMoment

end

end OAI

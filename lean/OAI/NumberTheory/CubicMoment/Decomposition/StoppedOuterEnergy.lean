import OAI.NumberTheory.CubicMoment.Estimates.SmallBStoppedBilinear

namespace OAI

/-! The actual stopped outer coefficient has logarithmic energy in the
same X-normalization as the stopped corrected-dispersion theorem. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem stopped_outer_log_energy (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (E U P : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w b A X : ℝ) (remaining : Eisenstein → Prop),
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      Real.exp 1 ≤ X → 2 ≤ b → b ≤ X → b^(3/2:ℝ) ≤ A → A ≤ b^2 →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
      (∑ a ∈ P, ‖stoppedAlpha E U ψ w remaining a‖^2) ≤
        K*A*(Real.log X)^d := by
  obtain ⟨K,d,hK,henergy⟩ := smallB_stopped_alpha_energy hpnt
  let M := 2*K*(3+Real.log 2)^d
  refine ⟨M*2^d,d,by dsimp [M]; positivity,?_⟩
  intro E U P ψ w b A X remaining hE hψ hX hb hbX hAlo hAhi hP
  have hb1 : 1 ≤ b := by linarith
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hAlo
  have hbpow : b ≤ b^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num : (1:ℝ) ≤ 3/2)
  have hA2 : 2 ≤ A := hb.trans (hbpow.trans hAlo)
  have hbig : Real.exp 1 ≤ 2*A := by linarith [Real.exp_one_lt_d9]
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hLb : 1+Real.log b ≤ 2*Real.log X := by
    have hh := Real.log_le_log (by linarith : 0 < b) hbX
    linarith
  have he := henergy E U P ψ w (2*A) remaining hE hψ hbig
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2⟩)
  apply (he.trans (outer_log_energy_conversion hA1 hb1 hAhi hK.le d)).trans
  change M*A*(1+Real.log b)^d ≤ (M*2^d)*A*(Real.log X)^d
  calc
    _ ≤ M*A*(2*Real.log X)^d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hb1]) hLb d)
      (by dsimp [M]; positivity)
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI

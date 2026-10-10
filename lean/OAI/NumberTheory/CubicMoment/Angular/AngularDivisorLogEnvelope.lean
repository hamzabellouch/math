import OAI.NumberTheory.CubicMoment.Angular.AngularHeightCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.DivisorFrequencyDyads
import OAI.NumberTheory.CubicMoment.Estimates.LogPoissonEnvelope

namespace OAI

/-! The full prime coefficient envelope on actual effective-frequency
dyads. Both square-divisor powers in the scalar are retained. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_logarithmic_divisor_poisson_dyad {R : ℝ} (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ (K : ℝ) (a : ℕ), 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (A : ℝ) (d e : Eisenstein) (u : ℝ) (j : ℕ) (H : Finset Eisenstein)
      (hd : d ≠ 0), 0 < A → H ⊆ divisorFrequencyDyad d hd j →
      ‖finiteDivisorPoissonContribution d (fullSquarefreePrimeSupport R (W r) X e) H
        (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*(A/(norm d)^2)*L r*(1+Real.log (L r))^a*(2:ℝ)^j /
          (1+A*(2:ℝ)^j/(27*(norm d)^3*(R^Fintype.card ι*L r)^2))^m := by
  obtain ⟨C,hC,hbound⟩ := finiteDivisorPoissonContribution_absolute V hV hV' m
  obtain ⟨E,a,hE,hl1⟩ := logarithmic_full_l1_square hR hW hlo hhi
  refine ⟨4*C*E,a,by positivity,?_⟩
  intro r X hL hX hprod A d e u j H hd hA hH
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hRpow : 1 ≤ R^Fintype.card ι := one_le_pow₀ hR
  have hS : ∀ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      primary b ∧ L r ≤ norm b ∧ norm b ≤ R^Fintype.card ι*L r := by
    intro b hb
    have hn := fullPrimeProduct_norm_bounds R (W r) X
      (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) (Finset.mem_filter.mp hb).1
    rw [hprod] at hn
    exact ⟨(fullSquarefreePrimeSupport_primary R (W r) X e hb).1,hn⟩
  have hm := hbound A (L r) (R^Fintype.card ι*L r) ((2:ℝ)^j/norm d) hA hLp
    (le_mul_of_one_le_left hLp.le hRpow) (by positivity) d hd _ H hS
    (fun h hh => (divisorFrequencyDyad_norm (hH hh)).1) (angularHeightPrimeCoefficient ℓ R (W r) X) u
  have heq : (A/(norm d)^2)*((2:ℝ)^j/norm d)/(27*(R^Fintype.card ι*L r)^2) =
      A*(2:ℝ)^j/(27*(norm d)^3*(R^Fintype.card ι*L r)^2) := by ring
  rw [heq] at hm
  have hc₀ : (H.card:ℝ) ≤ ((frequencyDyad j).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hH).trans (divisorFrequencyDyad_card_le d hd j)
  have hc : (H.card:ℝ) ≤ 36*(2:ℝ)^j := hc₀.trans (frequencyDyad_card_le j)
  apply hm.trans
  calc
    _ ≤ C*((A/(norm d)^2)/(9*L r))*(36*(2:ℝ)^j)*
        (E*(L r)^2*(1+Real.log (L r))^a) /
        (1+A*(2:ℝ)^j/(27*(norm d)^3*(R^Fintype.card ι*L r)^2))^m := by
      gcongr
      rw [angularHeightPrimeCoefficient_l1]
      exact hl1 r X hL hX hprod e
    _ = _ := by field_simp; ring

end CubicFirstMoment

end

end OAI

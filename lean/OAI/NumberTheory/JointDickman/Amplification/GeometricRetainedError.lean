import OAI.NumberTheory.JointDickman.Probability.HistogramLossBound
import OAI.NumberTheory.JointDickman.Amplification.RetainedErrorSum

namespace OAI

/-! # Vanishing retained-arc histogram error, uniformly in endpoint tests -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap

noncomputable def geometricDenominatorError (m B j : ℕ) [NeZero j] (q : ℕ+)
    (a b t β : ℝ) (S : Finset ℤ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  ∑ k ∈ S, manuscriptSampledIntegralError m B (j*(q : ℕ))
    (geometricHistogramWindow m B t (Real.log a) (Real.log b) k) g h
    (fun ξ => logOscillatoryTest w₁ B (Real.exp ((k : ℝ)*t)) (β*ξ))
    (fun ξ => logOscillatoryTest w₂ B (Real.exp ((k : ℝ)*t)) (-β*ξ))
    (fun r => r.val.Coprime (q : ℕ)) w

theorem geometric_retained_error_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ D₁ D₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 ≤ T → η*T ≤ j → ∀ S : Finset ℤ,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*‖retainedErrorSum B j Q
        (fun q => geometricDenominatorError m B j q a b t (T/j) S g h w₁ w₂ w)‖ ≤ ε B := by
  obtain ⟨C,hC,hgeo⟩ := geometric_sampled_integral_error_sum hSD hSW hM hMP
  obtain ⟨ε,hε,hden⟩ := retainedErrorSum_vanishing hMP hη
  let R := 1/η
  let K := 2*(b*Real.exp 1)*((D₁+2*Real.pi*R*M₁)*M₂+M₁*(D₂+2*Real.pi*R*M₂))+2*M₁*M₂
  let W := ∫ ξ : ℝ, ‖testFourierTransform w ξ‖*(1+|ξ|)
  let C₀ := (Real.log b-Real.log a+2)*C*((1+Real.log b-Real.log a)/t+1)*K*W
  have hb : 0 < b := ha.trans_le hab
  have hlog : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have hK : 0 ≤ K := by dsimp [K,R]; positivity
  have hW : 0 ≤ W := integral_nonneg (fun ξ => by positivity)
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    have : 0 ≤ Real.log b-Real.log a+2 := by linarith
    have : 0 ≤ 1+Real.log b-Real.log a := by linarith
    positivity
  refine ⟨fun B => C₀*ε B,by simpa using hε.const_mul C₀,?_⟩
  intro m hm
  filter_upwards [hgeo m hm,hden m hm,eventually_ge_atTop 1] with B hgeoB hdenB hB
  intro j _ Q hQ hscale T hT hlag S g h hg hh
  have hj : 0 < j := NeZero.pos j
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hβ : |T/(j : ℝ)| ≤ R := by
    rw [abs_of_nonneg (div_nonneg hT hj0.le)]
    apply (div_le_div_iff₀ hj0 hη).mpr
    simpa only [one_mul,mul_one,mul_comm] using hlag
  have hBpow : B ≤ B^15 := Nat.le_pow (by omega)
  apply hdenB j Q hj hQ (hscale.trans hBpow) T C₀ hT hC₀ hlag
  intro q hq
  have hjq : j*(q : ℕ) ≤ B := (Nat.mul_le_mul_left j ((mem_positiveDenominators Q q).mp hq)).trans hscale
  have he := hgeoB (j*(q : ℕ)) hjq a b t ha hab ht S g h hg hh
    w₁ w₂ w₁' w₂' M₁ M₂ D₁ D₂ (T/j) hM₁ hM₂ hD₁ hD₂
    hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ (fun r => r.val.Coprime (q : ℕ)) w
  have hloss := histogram_frequency_loss_bound (m := m) hB hM₁ hM₂ hD₁ hD₂ hb.le
    (show 0 ≤ R by dsimp [R]; positivity) hβ
  let P := ((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*
    ((Real.log b-Real.log a+2)/B)*C*((1+Real.log b-Real.log a)/t+1)
  have hP : 0 ≤ P := by
    dsimp [P]
    have : 0 ≤ Real.log b-Real.log a+2 := by linarith
    have : 0 ≤ 1+Real.log b-Real.log a := by linarith
    positivity
  have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hloss hP) hW
  exact ((norm_sum_le _ _).trans (he.trans hs)).trans_eq (by dsimp [P,C₀,K,W,R]; ring)

end JointDickman

end OAI

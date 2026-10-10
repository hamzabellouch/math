import OAI.NumberTheory.JointDickman.Amplification.WeightedGeometricError
import OAI.NumberTheory.JointDickman.Counting.CoefficientDensityRegularity

namespace OAI

/-! # The actual frozen coefficient density preserves the summed error estimate -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem frozen_histogram_error_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2)) (H : ℕ)
    {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ D₁ D₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 ≤ T → η*T ≤ j → ∀ S : Finset ℤ,
      ∀ X : ℤ → ℝ, (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (X k)) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*‖retainedErrorSum B j Q (fun q => weightedGeometricDenominatorError m B j q
        a b t (T/j) S (fun k => (coefficientDensity c H B (Real.log (X k)/B) : ℂ))
        g h w₁ w₂ w)‖ ≤ ε B := by
  obtain ⟨D,L,hD,_,hbound⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨ε,hε,he⟩ := weighted_geometric_retained_error_vanishing hSD hSW hM hMP
    ha hab ht hη w₁ w₂ w₁' w₂' w hM₁ hM₂ hD₁ hD₂ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hD
  refine ⟨ε,hε,?_⟩
  intro m hm
  filter_upwards [he m hm,hbound,eventually_ge_atTop 1] with B heB hb hB
  intro j _ Q hQ hscale T hT hlag S X hX g h hg hh
  apply heB j Q hQ hscale T hT hlag S
    (fun k => (coefficientDensity c H B (Real.log (X k)/B) : ℂ)) ?_ g h hg hh
  intro k hk
  rw [Complex.norm_real,Real.norm_eq_abs]
  apply hb.1
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  apply (le_div_iff₀ hB0).mpr
  nlinarith [hX k hk]

end JointDickman

end OAI

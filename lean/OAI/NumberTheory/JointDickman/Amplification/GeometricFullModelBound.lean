import OAI.NumberTheory.JointDickman.Amplification.GeometricFullModel
import OAI.NumberTheory.JointDickman.Probability.FrozenHistogramError

namespace OAI

/-! # The full retained-arc model is uniformly approximated by the sampled log kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem geometric_full_model_error_vanishing
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
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*‖geometricFullModelDifference m B j Q a b T t S
        (fun k => (coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B) : ℂ))
        g h w₁ w₂ w‖ ≤ ε B := by
  obtain ⟨ε,hε,he⟩ := frozen_histogram_error_vanishing hSD hSW hM hMP c hc H
    ha hab ht hη w₁ w₂ w₁' w₂' w hM₁ hM₂ hD₁ hD₂ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂
  refine ⟨ε,hε,?_⟩
  intro m hm
  filter_upwards [he m hm,endpoint_support_log_bounds ha hab,eventually_ge_atTop 1]
    with B heB hsupport hB
  intro j _ Q hQ hscale T hT hlag S hbox hcoeff g h hg hh
  have hBpos : 0 < B := by omega
  have hQbound : Q ≤ B^12 :=
    ((Nat.le_mul_of_pos_left Q (NeZero.pos j)).trans hscale).trans (Nat.le_pow (by norm_num))
  have hpow : B ≤ B^1000 := le_self_pow₀ hB (by decide : (1000 : ℕ) ≠ 0)
  have hcut : j*Q ≤ auxiliaryCutoff B := by
    change j*Q ≤ B^1000
    exact Nat.le_trans hscale hpow
  have hlocal (v : ℝ → ℝ) (hs : ∀ x, x ≤ a ∨ b < x → v x = 0)
      (k : ℤ) (hk : k ∈ S) (n : ℕ) (_hn : n ∈ primeSplitProductSupport (auxiliaryPrimes B))
      (hw : v (n/Real.exp ((k : ℝ)*t)) ≠ 0) : Real.log n/B ∈ Set.Ioc (1/2 : ℝ) 3 := by
    have hinside : a < (n : ℝ)/Real.exp ((k : ℝ)*t) ∧
        (n : ℝ)/Real.exp ((k : ℝ)*t) ≤ b := by
      constructor
      · by_contra h
        exact hw (hs _ (Or.inl (le_of_not_gt h)))
      · by_contra h
        exact hw (hs _ (Or.inr (lt_of_not_ge h)))
    apply hsupport _ (Real.exp_pos _) (by simpa only [Real.log_exp] using hbox k hk) n
      hinside.1 hinside.2
  rw [geometric_full_model_replacement hm hBpos hQbound hcut ha hab hT S _ g h hg hh
    w₁ w₂ hM₁ hM₂ hwb₁ hwb₂ hs₁ hs₂ (hlocal w₁ hs₁) (hlocal w₂ hs₂) w]
  exact heB j Q hQ hscale T hT.le hlag S (fun k => Real.exp ((k : ℝ)*t)/T) hcoeff g h hg hh

end JointDickman

end OAI

import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionExponential

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling Guided Comparison
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]

noncomputable def recoveryRepeat (D F S : Finset V) (hD : D.Nonempty)
    (hSF : S ⊆ F) (hS : S.Nonempty) (Δ P : ℝ) (hΔ : 0 ≤ Δ)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) (m n : ℕ)
    (seed : Fin n → IntegralBits D Δ m × (Fin (localTapeBound F m) → Bool)) : Finset V :=
  bestWithFallback (realCost D) S
    (recoveryTrial D F S hD hSF hS Δ P hΔ hbound m) n seed

lemma recoveryRepeat_feasible (D F S : Finset V) (hD : D.Nonempty)
    (hSF : S ⊆ F) (hS : S.Nonempty) (Δ P : ℝ) (hΔ : 0 ≤ Δ)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) (m n : ℕ)
    (seed : Fin n → IntegralBits D Δ m × (Fin (localTapeBound F m) → Bool)) :
    recoveryRepeat D F S hD hSF hS Δ P hΔ hbound m n seed ⊆ F ∧
    (recoveryRepeat D F S hD hSF hS Δ P hΔ hbound m n seed).card ≤ S.card ∧
    (recoveryRepeat D F S hD hSF hS Δ P hΔ hbound m n seed).Nonempty ∧
    realCost D (recoveryRepeat D F S hD hSF hS Δ P hΔ hbound m n seed) ≤ realCost D S := by
  unfold recoveryRepeat
  rcases bestWithFallback_mem (realCost D) S
    (recoveryTrial D F S hD hSF hS Δ P hΔ hbound m) n seed with h | ⟨i,h⟩
  · rw [h]
    exact ⟨hSF,le_rfl,hS,le_rfl⟩
  · have ht := recoveryTrial_feasible D F S hD hSF hS Δ P hΔ hbound m (seed i)
    rw [h]
    exact ht

namespace Comparison
variable {D S O : Finset V}

theorem recoveryRepeat_guarantees : ∃ c : ℝ, 0 < c ∧
    ∀ {D S O : Finset V} (C : Comparison D S O) (hD : D.Nonempty)
      (F : Finset V) (hSF : S ⊆ F), O ⊆ F → ∀ (hS : S.Nonempty)
      (Δ : ℝ) (hΔ : 1 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ),
      (∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) →
      0 < comparisonCost D C.assign → 0 < C.bad.card →
      ∀ ζ : ℝ, 0 < ζ → ∀ n : ℕ,
      Real.log (1/ζ)/Real.exp (-c*C.bad.card) ≤ (n:ℝ) →
      probability (fun seed : Fin n → IntegralBits D Δ C.bad.card × (Fin (localTapeBound F C.bad.card) → Bool) =>
        realCost D (recoveryRepeat D F S hD hSF hS Δ (comparisonCost D C.assign)
          (by linarith) hbound C.bad.card n seed) ≤ (197/100:ℝ)*comparisonCost D C.assign) ≥ 1-ζ ∧
      average (fun seed : Fin n → IntegralBits D Δ C.bad.card × (Fin (localTapeBound F C.bad.card) → Bool) =>
        realCost D (recoveryRepeat D F S hD hSF hS Δ (comparisonCost D C.assign)
          (by linarith) hbound C.bad.card n seed)) ≤
        (197/100:ℝ)*comparisonCost D C.assign + realCost D S*ζ := by
  obtain ⟨c,hc,hsuccess⟩ := recoveryTrial_exponential (V := V)
  refine ⟨c,hc,?_⟩
  intro D S O C hD F hSF hOF hS Δ hΔ hbound hsep hP hm ζ hζ n hn
  have hs := hsuccess C hD F hSF hOF hS Δ hΔ hbound hsep hP hm
  exact (amplified_output (realCost D) S
    (recoveryTrial D F S hD hSF hS Δ (comparisonCost D C.assign)
      (by linarith) hbound C.bad.card)
    (by positivity : (0:ℝ) ≤ (197/100:ℝ)*comparisonCost D C.assign)
    (by
      simp only [realCost,dite_eq_left hS]
      exact Finset.sum_nonneg (fun _ _ => distanceTo_nonneg _ _ _)) le_rfl (Real.exp_pos _) hs hζ n hn).2

end Comparison
end MetricKMedianRecovery.Sampling

end OAI

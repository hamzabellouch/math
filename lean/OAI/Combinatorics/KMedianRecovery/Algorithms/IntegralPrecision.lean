import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.OneStepLower

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling Precision
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable local instance (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _

noncomputable def integralPrecision (D : Finset V) (Δ : ℝ) (m : ℕ) : ℕ :=
  precisionBits D.card (Nat.ceil Δ) (firstSize mainKappa)
    (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m)

lemma integralPrecision_spec (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
    (Δ P : ℝ) (hΔ : 1 ≤ Δ) (m : ℕ)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) :
    Precise (blindUpdate D F S hD Δ P m) (mainActual D S Δ m)
      (integralPrecision D Δ m) (2*m) (some State.initial) := by
  exact precise_every_history D F S hD hSF Δ P mainKappa hΔ m _ _ _
    (by unfold firstSize; omega) (by unfold thirdSize; omega) hsep (2*m) _ good_initial

noncomputable abbrev IntegralBits (D : Finset V) (Δ : ℝ) (m : ℕ) :=
  Fin (2*m) → Fin (integralPrecision D Δ m) → Bool

noncomputable def integralActions (D F S : Finset V) (hD : D.Nonempty)
    (Δ P : ℝ) (m : ℕ) (bits : IntegralBits D Δ m) : Fin (2*m) → MainAction D m :=
  actions (blindUpdate D F S hD Δ P m) (mainActual D S Δ m)
    (integralPrecision D Δ m) (Sum.inl ()) (2*m) (some State.initial) bits

theorem integral_records_success {D S O : Finset V}
    (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (hSF : S ⊆ F) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (1/2:ℝ)^(2*C.bad.card) * samplingBound C.bad.card ≤
      probability (fun bits => Hits
        (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
        (C.stop hD Δ) (2*C.bad.card) (some State.initial)
        (integralActions D F S hD Δ (comparisonCost D C.assign) C.bad.card bits)) := by
  have hh := event_lower
    (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
    (mainActual D S Δ C.bad.card) (integralPrecision D Δ C.bad.card)
    (Sum.inl ()) (2*C.bad.card) (some State.initial)
    (integralPrecision_spec D F S hD hSF Δ (comparisonCost D C.assign) hΔ C.bad.card hsep)
    (Hits (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
      (C.stop hD Δ) (2*C.bad.card) (some State.initial))
  exact (mul_le_mul_of_nonneg_left (C.actual_records_success hD F hOF Δ (by linarith) hP hm)
    (by positivity)).trans hh

theorem integral_prefix_exponential : ∃ c : ℝ, 0 < c ∧
    ∀ {D S O : Finset V} (C : Comparison D S O) (hD : D.Nonempty)
      (F : Finset V), O ⊆ F → S ⊆ F → ∀ Δ : ℝ, 1 ≤ Δ →
      (∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) →
      0 < comparisonCost D C.assign → 0 < C.bad.card →
      Real.exp (-c*C.bad.card) ≤ probability (fun bits => Hits
        (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
        (C.stop hD Δ) (2*C.bad.card) (some State.initial)
        (integralActions D F S hD Δ (comparisonCost D C.assign) C.bad.card bits)) := by
  obtain ⟨c,hc,h⟩ := sampling_exponential
  exact ⟨c,hc,fun C hD F hOF hSF Δ hΔ hsep hP hm =>
    (h C.bad.card).trans (C.integral_records_success hD F hOF hSF Δ hΔ hsep hP hm)⟩

end MetricKMedianRecovery.Sampling.Comparison

end OAI

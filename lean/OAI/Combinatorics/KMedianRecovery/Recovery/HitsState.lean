import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralPrecision

namespace OAI

namespace MetricKMedianRecovery.Guided
variable {S A : Type*}
lemma hits_iff_exists_state (f : S → A → S) (stop : S → Prop)
    (n : ℕ) (s : S) (seed : Fin n → A) :
    Hits f stop n s seed ↔ ∃ i : Fin (n+1), stop (states f n s seed i) := by
  induction n generalizing s with
  | zero =>
    change stop s ↔ ∃ _ : Fin 1, stop s
    exact ⟨fun h => ⟨0,h⟩,fun ⟨_,h⟩ => h⟩
  | succ n ih =>
    rw [Hits,ih]
    constructor
    · rintro (h | ⟨i,hi⟩)
      · exact ⟨0,by simpa only [states,Fin.cases_zero] using h⟩
      · exact ⟨i.succ,by simpa only [states,Fin.cases_succ] using hi⟩
    · rintro ⟨i,hi⟩
      revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi
        exact Or.inl (by simpa only [states,Fin.cases_zero] using hi)
      · intro hi
        exact Or.inr ⟨j,by simpa only [states,Fin.cases_succ] using hi⟩
end MetricKMedianRecovery.Guided

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling Guided Comparison
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]

noncomputable def completeOption (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (m : ℕ) (tape : Fin (localTapeBound F m) → Bool) : Option (State V) → Finset V
  | none => S
  | some s => completeState D F S hSF hS Δ hΔ hbound s m tape

lemma completeOption_feasible (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (m : ℕ) (tape : Fin (localTapeBound F m) → Bool) (s : Option (State V)) :
    let out := completeOption D F S hSF hS Δ hΔ hbound m tape s
    out ⊆ F ∧ out.card ≤ S.card ∧ out.Nonempty ∧ realCost D out ≤ realCost D S := by
  cases s with
  | none => exact ⟨hSF,le_refl _,hS,le_refl _⟩
  | some s => exact completeState_feasible D F S hSF hS Δ hΔ hbound s m tape

noncomputable def recoveryTrial (D F S : Finset V) (hD : D.Nonempty)
    (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ P : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) (m : ℕ)
    (seed : IntegralBits D Δ m × (Fin (localTapeBound F m) → Bool)) : Finset V :=
  enumeratedBest (realCost D) S (fun i : Fin (2*m+1) =>
    completeOption D F S hSF hS Δ hΔ hbound m seed.2
      (states (blindUpdate D F S hD Δ P m) (2*m) (some State.initial)
        (integralActions D F S hD Δ P m seed.1) i))

lemma recoveryTrial_feasible (D F S : Finset V) (hD : D.Nonempty)
    (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ P : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) (m : ℕ)
    (seed : IntegralBits D Δ m × (Fin (localTapeBound F m) → Bool)) :
    let out := recoveryTrial D F S hD hSF hS Δ P hΔ hbound m seed
    out ⊆ F ∧ out.card ≤ S.card ∧ out.Nonempty ∧ realCost D out ≤ realCost D S := by
  unfold recoveryTrial
  have hcost := (enumeratedBest_le (realCost D) S (fun i : Fin (2*m+1) =>
    completeOption D F S hSF hS Δ hΔ hbound m seed.2
      (states (blindUpdate D F S hD Δ P m) (2*m) (some State.initial)
        (integralActions D F S hD Δ P m seed.1) i))).1
  rcases enumeratedBest_mem (realCost D) S (fun i : Fin (2*m+1) =>
    completeOption D F S hSF hS Δ hΔ hbound m seed.2
      (states (blindUpdate D F S hD Δ P m) (2*m) (some State.initial)
        (integralActions D F S hD Δ P m seed.1) i)) with h | ⟨i,h⟩
  · simpa only [h] using And.intro hSF (And.intro (le_refl S.card) (And.intro hS (le_refl (realCost D S))))
  · have hh := completeOption_feasible D F S hSF hS Δ hΔ hbound m seed.2
      (states (blindUpdate D F S hD Δ P m) (2*m) (some State.initial)
        (integralActions D F S hD Δ P m seed.1) i)
    exact ⟨h ▸ hh.1,h ▸ hh.2.1,h ▸ hh.2.2.1,hcost⟩

lemma recoveryTrial_le (D F S : Finset V) (hD : D.Nonempty)
    (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ P : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) (m : ℕ)
    (seed : IntegralBits D Δ m × (Fin (localTapeBound F m) → Bool)) (i : Fin (2*m+1)) :
    realCost D (recoveryTrial D F S hD hSF hS Δ P hΔ hbound m seed) ≤
      realCost D (completeOption D F S hSF hS Δ hΔ hbound m seed.2
        (states (blindUpdate D F S hD Δ P m) (2*m) (some State.initial)
          (integralActions D F S hD Δ P m seed.1) i)) :=
  (enumeratedBest_le _ _ _).2 i
end MetricKMedianRecovery.Sampling

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling Guided
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

theorem recoveryTrial_success
    (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hSF : S ⊆ F) (hOF : O ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 1 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    ((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card) *
        ((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)) ≤
      probability (fun seed : IntegralBits D Δ C.bad.card × (Fin (localTapeBound F C.bad.card) → Bool) =>
        realCost D (recoveryTrial D F S hD hSF hS Δ (comparisonCost D C.assign)
          (by linarith) hbound C.bad.card seed) ≤ (197/100:ℝ)*comparisonCost D C.assign) := by
  have hΔ0 : 0 ≤ Δ := le_trans (by norm_num) hΔ
  let E := fun bits : IntegralBits D Δ C.bad.card => Hits
    (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
    (C.stop hD Δ) (2*C.bad.card) (some State.initial)
    (integralActions D F S hD Δ (comparisonCost D C.assign) C.bad.card bits)
  have hsample : (1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card ≤ probability E :=
    C.integral_records_success hD F hOF hSF Δ hΔ hsep hP hm
  apply (mul_le_mul_of_nonneg_right hsample (by positivity :
    0 ≤ (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ))).trans
  refine probability_prod_lower E (fun sample tape =>
    realCost D (recoveryTrial D F S hD hSF hS Δ (comparisonCost D C.assign)
      hΔ0 hbound C.bad.card (sample,tape)) ≤ (197/100:ℝ)*comparisonCost D C.assign) ?_
  intro sample hsample
  obtain ⟨i,hi⟩ := (hits_iff_exists_state _ _ _ _ _).mp hsample
  generalize hst : states (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
    (2*C.bad.card) (some State.initial)
    (integralActions D F S hD Δ (comparisonCost D C.assign) C.bad.card sample) i = st at hi
  cases st with
  | none => exact False.elim hi
  | some s =>
    change C.Correct hD mainKappa s ∧ C.Terminal mainKappa Δ s at hi
    have hc := C.completeState_success hD Δ s hi.1 hΔ0 hP hm hi.2.2 hi.2.1 F hSF hOF hS hbound
    apply hc.trans
    apply probability_mono
    intro tape ht
    have hl := recoveryTrial_le D F S hD hSF hS Δ (comparisonCost D C.assign)
      hΔ0 hbound C.bad.card (sample,tape) i
    rw [hst] at hl
    exact hl.trans ht
end MetricKMedianRecovery.Sampling.Comparison

end OAI

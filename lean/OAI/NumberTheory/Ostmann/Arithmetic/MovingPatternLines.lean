import OAI.NumberTheory.Ostmann.Construction.SamplePatternCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceRelabel
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampledIndexedProbability

namespace OAI

/-! # Actual equality-pattern rows in the fixed coordinates of the line comparison -/

namespace Ostmann
open scoped Classical

/-- The uniqueness and tier conditions of the fixed row system are consequences
of the exact equality-pattern coordinates. They are not additional arithmetic
assumptions about the original samples. -/
theorem movingPatternLineProbability {I A : Type*} [Fintype I]
    (s : Setoid I) {N n : ℕ} (hcard : Fintype.card (Quotient s) = N + 1)
    (z : Quotient s → A) (hz : Function.Injective z)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (T : Bool → MovingSlotData I n) (tier : I → ℕ)
    (htier : ∀ i j, s i j → tier i = tier j) (hlevels : ∀ side, (T side).Levels tier)
    (c : Fin (N + 1))
    (base : MovingPairRepresentativeOccurrences
      (fun side => (T side).map (samplePatternLabels s hcard)) c)
    (hf : ∀ side, (T side).Frequencies (fun a =>
      (a : ZMod (prime (samplePatternValues s hcard z c))) ≠ 0)) :
    let v := fun i => prime (z (Quotient.mk'' i))
    let p := prime (samplePatternValues s hcard z c)
    letI : Fact p.Prime := ⟨hprime _⟩
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction p v (movingPrimeOccurrenceLine v T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p v (movingPrimeOccurrenceLine v T p j).b) =
    movingSlotLineProbability (fun a => (prime a : ℤ)) prime hprime
      (fun o => (movingIndexedOccurrence
        (fun side => (T side).map (samplePatternLabels s hcard)) c base o).path)
      (fun o => (movingIndexedOccurrence
        (fun side => (T side).map (samplePatternLabels s hcard)) c base o).current)
      true (samplePatternValues s hcard z) (samplePatternValues s hcard z c) := by
  let x := samplePatternValues s hcard z
  let labels := samplePatternLabels s hcard
  let TT := fun side => (T side).map labels
  let tt := samplePatternTier s hcard tier
  let p := prime (x c)
  let : Fact p.Prime := ⟨hprime _⟩
  have hx : Function.Injective (fun i => prime (x i)) :=
    hpInj.comp (samplePatternValues_injective s hcard z hz)
  have hd (i j : Fin (N + 1)) (h : tt i ≠ tt j) : prime (x i) ≠ prime (x j) := by
    intro he
    exact h (congrArg tt (hx he))
  have hl (side : Bool) : (TT side).Levels tt :=
    (T side).levels_samplePattern s hcard tier htier (hlevels side)
  have hff (side : Bool) : (TT side).Frequencies (fun a => (a : ZMod p) ≠ 0) :=
    ((T side).frequencies_map labels _).mpr (hf side)
  have he := movingSampledIndexedProbability prime hprime x TT tt hd hl c base
    (fun i h => hx h) hff
  have hm := movingInternalBaseProbability_map labels (fun i => prime (x i)) T p
  have hv : (fun i => prime (x i)) ∘ labels = (fun i => prime (z (Quotient.mk'' i))) := by
    funext i
    exact congrArg prime (samplePatternValues_labels s hcard z i)
  rw [hv] at hm
  exact hm.symm.trans he

end Ostmann

end OAI

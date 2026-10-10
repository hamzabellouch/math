import OAI.Combinatorics.ProgressionColoring.OuterPatternColoring
import OAI.Combinatorics.ProgressionColoring.EligiblePatternTests
import OAI.Combinatorics.ProgressionColoring.OuterBalanced

namespace OAI

/-!
# Outer coloring of the actual eligible geometric patterns

The event indices contain exactly a period and a literal `(step, word)` pair.
Existential real realizations of one word do not increase its event count.
-/

namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem recordedWord_coloredPositions_eq {D h : ℕ}
    (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (R : AnchoredPatterns.Realization D) (lambda : ℕ) (t : Fin D → Fin h)
    (color : FullLabel D (Fin n) A.Label → Bool) (b : Bool) :
    RecordedSupport.coloredPositions
        (AnchoredPatterns.recordedWord n hn A eta R lambda t) color b =
      (AnchoredPatterns.regularPositions eta R lambda t).filter
        (fun z => color (AnchoredPatterns.fullLabel n hn A R lambda t z) = b) := by
  classical
  ext z
  simp only [RecordedSupport.mem_coloredPositions,
    AnchoredPatterns.recordedWord_eq_some_iff, Finset.mem_filter,
    AnchoredPatterns.regularPositions, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨beta, ⟨hz, hbeta⟩, hb⟩
    exact ⟨hz, by simpa only [hbeta] using hb⟩
  · rintro ⟨hz, hb⟩
    exact ⟨_, ⟨hz, rfl⟩, hb⟩

theorem exists_outer_coloring_of_eligible_counts
    {D k : ℕ} (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ) (lambda : ℕ)
    (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → FullLabel D (Fin n) A.Label))
    (periods : Finset ℕ) (countBound : ℕ → ℕ)
    (hrow : (100 : ℝ) ≤ (M : ℝ) / 10 - 1)
    (hperiodLower : ∀ h ∈ periods, 200 ≤ h)
    (hthrough : ∀ h ∈ periods, ∀ beta : FullLabel D (Fin n) A.Label,
      (AnchoredPatterns.through (h := h) n hn A eta lambda beta).card ≤ countBound h)
    (hbudget : ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) +
      (∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500) :
    ∃ color : FullLabel D (Fin n) A.Label → Bool,
      (∀ word ∈ words, k ≤ 10 * (OuterWordTests.lightPositions M word).card → ∀ b,
        (OuterWordTests.lightPositions M word).card ≤
          4 * ((OuterWordTests.lightPositions M word).filter
            fun j => color (word j) = b).card) ∧
      (∀ h ∈ periods, ∀ t : Fin D → Fin h, ∀ R : AnchoredPatterns.Realization D,
        AnchoredPatterns.EligibleRealization n hn A eta lambda t R → ∀ b,
          (AnchoredPatterns.regularPositions eta R lambda t).card ≤
            4 * ((AnchoredPatterns.regularPositions eta R lambda t).filter
              fun z => color (AnchoredPatterns.fullLabel n hn A R lambda t z) = b).card) := by
  classical
  let I := EligiblePatternTests.TestIndex (D := D) n hn A eta lambda periods
  let period : I → ℕ := EligiblePatternTests.period
  let pattern : ∀ i : I, Fin (period i) → Option (FullLabel D (Fin n) A.Label) :=
    EligiblePatternTests.word
  have hcount : ∀ beta h,
      (Finset.univ.filter (fun i : I =>
        (∃ j, pattern i j = some beta) ∧ period i = h)).card ≤ countBound h := by
    intro beta h
    simpa only [EligiblePatternTests.mem_support] using
      EligiblePatternTests.incident_card_le_of_through countBound hthrough beta h
  obtain ⟨color, hglobal, hlocal⟩ := exists_outer_word_pattern_coloring M hM hMk words
    period pattern periods countBound hrow EligiblePatternTests.period_mem
    (fun i => hperiodLower (period i) (EligiblePatternTests.period_mem i))
    EligiblePatternTests.word_labelsInjective EligiblePatternTests.word_regular_many
    hcount hbudget
  refine ⟨color, hglobal, ?_⟩
  intro h hh t R hR b
  let p := AnchoredPatterns.recordedWord n hn A eta R lambda t
  have hp : (t, p) ∈ AnchoredPatterns.eligiblePairs n hn A eta lambda := by
    exact (AnchoredPatterns.mem_eligiblePairs n hn A eta lambda (t, p)).mpr ⟨R, hR, rfl⟩
  let i : I := ⟨⟨h, hh⟩, ⟨(t, p), hp⟩⟩
  have hi := hlocal i b
  change (RecordedSupport.regularPositions p).card ≤
    4 * (RecordedSupport.coloredPositions p color b).card at hi
  simpa only [p, AnchoredPatterns.recordedWord_regularPositions_eq,
    recordedWord_coloredPositions_eq] using hi

/-- Actual eligible patterns obey the anchored count theorem, so outer
selection requires only its explicit numerical incident-weight budget. -/
theorem exists_outer_balanced {D k : ℕ} (n : ℕ) (hn : 0 < n)
    (A : AdaptiveMesh) (lambda M : ℕ) (hD : 0 < D) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → FullLabel D (Fin n) A.Label)) (periods : Finset ℕ)
    (hrow : (100 : ℝ) ≤ (M : ℝ) / 10 - 1)
    (hperiodLower : ∀ h ∈ periods, 200 ≤ h)
    (hbudget : ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) +
      (∑ h ∈ periods, (((16005 * D * h) ^ (14 * D) : ℕ) : ℝ) *
        Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500) :
    ∃ color : FullLabel D (Fin n) A.Label → Bool,
      OuterBalanced n hn A (1 / (1000 * (D : ℝ))) lambda M words periods color := by
  classical
  have hthrough : ∀ h ∈ periods, ∀ beta : FullLabel D (Fin n) A.Label,
      (AnchoredPatterns.through (h := h) n hn A (1 / (1000 * (D : ℝ))) lambda beta).card ≤
        (16005 * D * h) ^ (14 * D) := by
    intro h hh beta
    exact AnchoredPatterns.card_through_le n hn A lambda beta hD
      (lt_of_lt_of_le (by decide : 0 < 200) (hperiodLower h hh))
  obtain ⟨color, hglobal, hlocal⟩ := exists_outer_coloring_of_eligible_counts
    n hn A (1 / (1000 * (D : ℝ))) lambda M hM hMk words periods
    (fun h => (16005 * D * h) ^ (14 * D)) hrow hperiodLower hthrough hbudget
  exact ⟨color, ⟨hglobal, hlocal⟩⟩

end QuantitativeVanDerWaerden

end OAI

import OAI.Combinatorics.ProgressionColoring.OuterFamilies
import OAI.Combinatorics.ProgressionColoring.OuterWordTests
import OAI.Combinatorics.ProgressionColoring.RecordedSupport

namespace OAI

/-!
# Simultaneous balancing of words and recorded local patterns

The global tests are constructed from the actual light-position fibers. The
local tests retain precisely the labels recorded by their Option-valued words.
The only counting inputs are the finite word and anchored-pattern bounds;
all probability, row partitioning and support-to-position conversions are proved.
-/

universe uLabel uI

namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem exists_outer_word_pattern_coloring
    {Label : Type uLabel} {I : Type uI} [Fintype Label] [DecidableEq Label] [Fintype I] [DecidableEq I]
    {k : ℕ} (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label))
    (period : I → ℕ) (pattern : ∀ i, Fin (period i) → Option Label)
    (periods : Finset ℕ) (countBound : ℕ → ℕ)
    (hrow : (100 : ℝ) ≤ (M : ℝ) / 10 - 1)
    (hperiod : ∀ i, period i ∈ periods)
    (hperiodLower : ∀ i, 200 ≤ period i)
    (hinj : ∀ i, RecordedSupport.LabelsInjective (pattern i))
    (hregular : ∀ i, period i ≤ 2 * (RecordedSupport.regularPositions (pattern i)).card)
    (hcount : ∀ b h,
      (Finset.univ.filter (fun i => (∃ j, pattern i j = some b) ∧ period i = h)).card ≤
        countBound h)
    (hbudget : ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) +
      (∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500) :
    ∃ color : Label → Bool,
      (∀ word ∈ words, k ≤ 10 * (OuterWordTests.lightPositions M word).card → ∀ b,
        (OuterWordTests.lightPositions M word).card ≤
          4 * ((OuterWordTests.lightPositions M word).filter
            fun j => color (word j) = b).card) ∧
      (∀ i b, (RecordedSupport.regularPositions (pattern i)).card ≤
        4 * (RecordedSupport.coloredPositions (pattern i) color b).card) := by
  classical
  let gsupport := OuterWordTests.support M hM hMk words
  let lsupport : I → Finset Label := fun i => RecordedSupport.support (pattern i)
  have hlsize : ∀ i, (100 : ℝ) ≤ (lsupport i).card := by
    intro i
    have heq := RecordedSupport.support_card_eq (pattern i) (hinj i)
    have hn : 100 ≤ (lsupport i).card := by
      dsimp only [lsupport]
      rw [heq]
      have hl := hperiodLower i
      have hr := hregular i
      omega
    exact_mod_cast hn
  have hhalf : ∀ i, period i ≤ 2 * (lsupport i).card := by
    intro i
    dsimp only [lsupport]
    rw [RecordedSupport.support_card_eq (pattern i) (hinj i)]
    exact hregular i
  have hlocalcount : ∀ b h,
      (Finset.univ.filter (fun i => b ∈ lsupport i ∧ period i = h)).card ≤ countBound h := by
    intro b h
    simpa only [lsupport, RecordedSupport.mem_support] using hcount b h
  have hbudget' : (Fintype.card (OuterWordTests.TestIndex M words) : ℝ) *
      Real.exp (-((M : ℝ) / 10 - 1) / 32) +
      (∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500 := by
    have hc : (Fintype.card (OuterWordTests.TestIndex M words) : ℝ) ≤
        ((k * words.card : ℕ) : ℝ) := by
      exact_mod_cast OuterWordTests.testIndex_card_le M words
    exact (add_le_add_left
      (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) _).trans hbudget
  obtain ⟨color, hg, hl⟩ := exists_outer_coloring_of_family_counts gsupport lsupport
    period periods countBound ((M : ℝ) / 10 - 1) hrow
    (OuterWordTests.support_card_real_lower M hM hMk words) hlsize hperiod hhalf
    hlocalcount hbudget'
  refine ⟨color, OuterWordTests.supports_balance_words M hM hMk words color hg, ?_⟩
  intro i b
  exact RecordedSupport.regular_card_le_four_colored (pattern i) (hinj i) color b (hl i b)

/-- The light-position alternative already gives the required whole-word
frequency bound, with slack from one fortieth to one hundredth. -/
theorem rich_of_light_balanced {Label : Type uLabel} [DecidableEq Label] {k M : ℕ}
    (word : Fin k → Label) (color : Label → Bool)
    (hlight : k ≤ 10 * (OuterWordTests.lightPositions M word).card)
    (hbalance : ∀ b, (OuterWordTests.lightPositions M word).card ≤
      4 * ((OuterWordTests.lightPositions M word).filter fun j => color (word j) = b).card) :
    ∀ b, k ≤ 100 * (Finset.univ.filter fun j => color (word j) = b).card := by
  classical
  intro b
  have hsub : (OuterWordTests.lightPositions M word).filter (fun j => color (word j) = b) ⊆
      Finset.univ.filter (fun j => color (word j) = b) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩
  have hc := Finset.card_le_card hsub
  have hb := hbalance b
  omega

end QuantitativeVanDerWaerden

end OAI

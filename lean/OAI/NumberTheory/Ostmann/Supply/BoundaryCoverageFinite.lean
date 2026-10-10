import OAI.NumberTheory.Ostmann.Preliminaries.Sizes
import OAI.NumberTheory.Ostmann.Supply.FiniteCoverage
import OAI.NumberTheory.Ostmann.Supply.NaturalWeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Ostmann.Preliminaries
open scoped BigOperators

def boundaryPairCount (d : Decomposition) (X : ℕ) : ℕ :=
  countUpTo d.A (initialWindowCutoff X) * countUpTo d.B X +
    countUpTo d.A X * countUpTo d.B (initialWindowCutoff X)

theorem largeElements_subset_upperWindow (A : Set ℕ) (X : ℕ) :
    largeElements (elementsUpTo A X) (initialWindowCutoff X) ⊆ upperWindow A X := by
  intro a ha
  obtain ⟨ha, hlarge⟩ := mem_largeElements.mp ha
  obtain ⟨hA,hX⟩ := mem_elementsUpTo.mp ha
  apply mem_upperWindow.mpr
  refine ⟨hA,hX,?_⟩
  exact le_of_lt ((Nat.floor_lt (Real.rpow_nonneg (by positivity) _)).mp hlarge)

theorem smallElements_card_le_initial (A : Set ℕ) (X : ℕ) :
    (smallElements (elementsUpTo A X) (initialWindowCutoff X)).card ≤
      countUpTo A (initialWindowCutoff X) := by
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ha,hr⟩ := mem_smallElements.mp ha
  exact mem_elementsUpTo.mpr ⟨(mem_elementsUpTo.mp ha).1,hr⟩

theorem actual_weighted_coverage_boundary (d : Decomposition) (X : ℕ)
    (hcut : d.cutoff ≤ X / 2) (W : ℕ → ℝ) (M : ℝ)
    (hW : ∀ n, 0 ≤ W n) (hM : 0 ≤ M) (hWM : ∀ n, W n ≤ M) :
    ∑ q ∈ primesInInterval (X/2) X, W q ≤
      (∑ a ∈ upperWindow d.A X, ∑ b ∈ upperWindow d.B X, W (a+b)) +
        (boundaryPairCount d X : ℝ) * M := by
  classical
  have hcover : ∀ q ∈ primesInInterval (X/2) X,
      ∃ a ∈ elementsUpTo d.A X, ∃ b ∈ elementsUpTo d.B X, a+b=q := by
    intro q hq
    obtain ⟨hqlo,hqhi,hqprime⟩ := mem_primesInInterval.mp hq
    obtain ⟨a,ha,b,hb,hab⟩ := d.prime_covered hqprime (hcut.trans hqlo)
    exact ⟨a,mem_elementsUpTo.mpr ⟨ha,by omega⟩,
      b,mem_elementsUpTo.mpr ⟨hb,by omega⟩,hab⟩
  have hcov := weighted_coverage_with_boundary_loss
    (elementsUpTo d.A X) (elementsUpTo d.B X) (primesInInterval (X/2) X)
    (initialWindowCutoff X) W M hW hM (fun q _ => hWM q) hcover
  have hsum :
      (∑ a ∈ largeElements (elementsUpTo d.A X) (initialWindowCutoff X),
        ∑ b ∈ largeElements (elementsUpTo d.B X) (initialWindowCutoff X), W (a+b)) ≤
      ∑ a ∈ upperWindow d.A X, ∑ b ∈ upperWindow d.B X, W (a+b) := by
    calc
      _ ≤ ∑ a ∈ largeElements (elementsUpTo d.A X) (initialWindowCutoff X),
          ∑ b ∈ upperWindow d.B X, W (a+b) := by
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.sum_le_sum_of_subset_of_nonneg (largeElements_subset_upperWindow d.B X)
          (fun b _ _ => hW _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (largeElements_subset_upperWindow d.A X) (fun a _ _ => Finset.sum_nonneg (fun b _ => hW _))
  have hcounts :
      (smallElements (elementsUpTo d.A X) (initialWindowCutoff X)).card *
        (elementsUpTo d.B X).card + (elementsUpTo d.A X).card *
          (smallElements (elementsUpTo d.B X) (initialWindowCutoff X)).card ≤
      boundaryPairCount d X := by
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (smallElements_card_le_initial d.A X))
      (Nat.mul_le_mul_left _ (smallElements_card_le_initial d.B X))
  have hc : ((smallElements (elementsUpTo d.A X) (initialWindowCutoff X)).card *
        (elementsUpTo d.B X).card + (elementsUpTo d.A X).card *
          (smallElements (elementsUpTo d.B X) (initialWindowCutoff X)).card : ℕ) ≤
      (boundaryPairCount d X : ℝ) := by exact_mod_cast hcounts
  exact hcov.trans (add_le_add hsum (mul_le_mul_of_nonneg_right hc hM))

end Ostmann.Supply

end

end OAI

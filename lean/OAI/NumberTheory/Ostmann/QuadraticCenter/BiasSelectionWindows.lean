import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionQuadratic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries
open scoped BigOperators

def positiveIntegerEmbedding : ℕ ↪ ℤ :=
  ⟨fun n => (n : ℤ), fun a b h => by
    change (a : ℤ) = (b : ℤ) at h
    exact_mod_cast h⟩

def negativeIntegerEmbedding : ℕ ↪ ℤ :=
  ⟨fun n => -(n : ℤ), fun a b h => by
    have he := neg_injective h
    exact_mod_cast he⟩

def positiveIntegerWindow (S : Set ℕ) (X : ℕ) : Finset ℤ :=
  (upperWindow S X).map positiveIntegerEmbedding

def negativeIntegerWindow (S : Set ℕ) (X : ℕ) : Finset ℤ :=
  (upperWindow S X).map negativeIntegerEmbedding

def integerQuadraticMean (U : Finset ℤ) (p : ℕ) (t : ℤ) : ℝ :=
  (∑ a ∈ U, (jacobiSym (a - t) p : ℝ)) / U.card

lemma oriented_integerQuadraticMean (U : Finset ℤ) (p : ℕ) (ε t : ℤ) :
    (∑ a ∈ U, ((ε * jacobiSym (a - t) p : ℤ) : ℝ)) / U.card =
      (ε : ℝ) * integerQuadraticMean U p t := by
  simp only [Int.cast_mul, ← Finset.mul_sum, integerQuadraticMean]
  ring

variable {p : ℕ} [Fact p.Prime]

lemma quadraticCharacter_nat_translate (n : ℕ) (t : ZMod p) :
    quadraticCharacter p ((n : ZMod p) - t) =
      (jacobiSym ((n : ℤ) - (t.val : ℤ)) p : ℂ) := by
  have he : ((n : ZMod p) - t) = (((n : ℤ) - (t.val : ℤ) : ℤ) : ZMod p) := by simp
  rw [he, quadraticCharacter_intCast, jacobiSym.legendreSym.to_jacobiSym]

lemma quadraticCharacter_neg_nat_translate (n : ℕ) (t : ZMod p) :
    quadraticCharacter p (-(n : ZMod p) - t) =
      (jacobiSym (-(n : ℤ) - (t.val : ℤ)) p : ℂ) := by
  have he : (-(n : ZMod p) - t) = ((-(n : ℤ) - (t.val : ℤ) : ℤ) : ZMod p) := by simp
  rw [he, quadraticCharacter_intCast, jacobiSym.legendreSym.to_jacobiSym]

lemma positive_window_complex_mean (S : Set ℕ) (X : ℕ) (t : ZMod p) :
    (∑ n ∈ upperWindow S X, quadraticCharacter p ((n : ZMod p) - t)) /
        ((upperWindow S X).card : ℂ) =
      (integerQuadraticMean (positiveIntegerWindow S X) p (t.val : ℤ) : ℂ) := by
  unfold integerQuadraticMean positiveIntegerWindow
  rw [Finset.card_map, Finset.sum_map]
  push_cast
  apply congrArg (fun z : ℂ => z / ((upperWindow S X).card : ℂ))
  apply Finset.sum_congr rfl
  intro n hn
  exact quadraticCharacter_nat_translate n t

lemma negative_window_complex_mean (S : Set ℕ) (X : ℕ) (t : ZMod p) :
    (∑ n ∈ upperWindow S X, quadraticCharacter p (-(n : ZMod p) - t)) /
        ((upperWindow S X).card : ℂ) =
      (integerQuadraticMean (negativeIntegerWindow S X) p (t.val : ℤ) : ℂ) := by
  unfold integerQuadraticMean negativeIntegerWindow
  rw [Finset.card_map, Finset.sum_map]
  push_cast
  apply congrArg (fun z : ℂ => z / ((upperWindow S X).card : ℂ))
  apply Finset.sum_congr rfl
  intro n hn
  exact quadraticCharacter_neg_nat_translate n t

lemma quadratic_complement_density_relation (d : Decomposition) (hp : p ≠ 2)
    (t : ZMod p) :
    d.residueDensity p * quadraticResidueMean (d.residueSupport p) t +
      (1 - d.residueDensity p) * quadraticResidueMean (d.residueSupport p)ᶜ t = 0 := by
  have hc := quadraticResidueMean_compl (d.residueSupport p)
    (d.residueSupport_nonempty p) (d.residueSupport_compl_nonempty p (Fact.out)) hp t
  have hcard : ((d.residueSupport p).card : ℝ) + ((d.residueSupport p)ᶜ.card : ℝ) = p := by
    have hn : (d.residueSupport p).card + (d.residueSupport p)ᶜ.card = p := by
      simpa only [ZMod.card p] using Finset.card_add_card_compl (d.residueSupport p)
    exact_mod_cast hn
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have htcard : ((d.residueSupport p)ᶜ.card : ℝ) = p - (d.residueSupport p).card := by linarith
  rw [htcard] at hc
  unfold Decomposition.residueDensity
  field_simp [hp0]
  nlinarith only [hc]

end Ostmann.QuadraticCenter

end

end OAI

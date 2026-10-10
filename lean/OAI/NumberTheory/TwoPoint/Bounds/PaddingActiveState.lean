import OAI.NumberTheory.TwoPoint.Bounds.ActiveStateExpansion
import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingResidues

namespace OAI

/-! Exact finite-index active states for the literal padding primes.
The same state determines the vertex normalization and every retained
squarefree padding-divisor test. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingActiveState {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q)
    (n : ℤ) : Finset (Fin m) :=
  activeState (fun i => decide (((e i).val : ℤ) ∣ n))

lemma paddingActiveState_image {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q) (n : ℤ) :
    (paddingActiveState Q e n).image (fun i => (e i).val) =
      Q.filter (fun p : ℕ => (p : ℤ) ∣ n) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact mem_filter.mpr ⟨(e i).property, by simpa [paddingActiveState, activeState] using hi⟩
  · intro hp
    obtain ⟨hpQ, hd⟩ := mem_filter.mp hp
    obtain ⟨i, hi⟩ := e.surjective ⟨p, hpQ⟩
    apply mem_image.mpr
    refine ⟨i, ?_, congrArg Subtype.val hi⟩
    simp only [paddingActiveState, activeState, mem_filter, mem_univ, true_and,
      decide_eq_true_eq]
    simpa only [hi] using hd

lemma paddingActiveState_card {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q) (n : ℤ) :
    (paddingActiveState Q e n).card = actualPaddingDegree Q n := by
  have hi : Function.Injective (fun i => (e i).val) :=
    Subtype.val_injective.comp e.injective
  have hh := congrArg Finset.card (paddingActiveState_image Q e n)
  rw [card_image_of_injective _ hi] at hh
  exact hh

lemma actualPaddingVertex_sq_activeState {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q) (n : ℤ) :
    (actualPaddingVertex Q n) ^ 2 = (5 : ℝ) ^ (paddingActiveState Q e n).card := by
  rw [actualPaddingVertex_sq, actualPaddingWeight, paddingActiveState_card]

lemma retainedPadding_dvd_iff_activeState {m : ℕ} (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (e : Fin m ≃ Q) (q : ℕ)
    (hq : q ∈ retainedPrimeDivisors Q) (n : ℤ) :
    (q : ℤ) ∣ n ↔ q.primeFactors ⊆
      (paddingActiveState Q e n).image (fun i => (e i).val) := by
  rw [paddingActiveState_image, ← paddingAvailablePrimes_integer]
  exact (padding_literal_support_iff_dvd Q hQ n q hq).symm

lemma paddingActiveState_residue {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q)
    (z : ∀ i, ZMod (e i).val) (n : ℤ)
    (hn : ∀ i, (n : ZMod (e i).val) = z i) :
    paddingActiveState Q e n = activeState (fun i => decide (z i = 0)) := by
  ext i
  simp only [paddingActiveState, activeState, mem_filter, mem_univ, true_and,
    decide_eq_true_eq]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hn i]

lemma actualPaddingVertex_sq_residue_state {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q)
    (z : ∀ i, ZMod (e i).val) (n : ℤ)
    (hn : ∀ i, (n : ZMod (e i).val) = z i) :
    (actualPaddingVertex Q n) ^ 2 =
      (5 : ℝ) ^ (activeState (fun i => decide (z i = 0))).card := by
  rw [actualPaddingVertex_sq_activeState Q e n, paddingActiveState_residue Q e z n hn]

lemma retainedPadding_dvd_iff_residue_state {m : ℕ} (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (e : Fin m ≃ Q) (q : ℕ)
    (hq : q ∈ retainedPrimeDivisors Q) (z : ∀ i, ZMod (e i).val) (n : ℤ)
    (hn : ∀ i, (n : ZMod (e i).val) = z i) :
    (q : ℤ) ∣ n ↔ q.primeFactors ⊆
      (activeState (fun i => decide (z i = 0))).image (fun i => (e i).val) := by
  rw [← paddingActiveState_residue Q e z n hn]
  exact retainedPadding_dvd_iff_activeState Q hQ e q hq n

end TwoPointCorrelations

end OAI

import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries

def withinAtomPrimeSupport (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (x : T.Constituent width → PrimeUpTo Q) : Prop :=
  ∀ i : T.Slot, Pairwise (fun a b : Fin (width (T.role i)) =>
    (x ⟨i,a⟩).val.Coprime (x ⟨i,b⟩).val)

def copiedWithinAtomPrimeSupport (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (x : CopiedConstituent T j width → PrimeUpTo Q) : Prop :=
  ∀ i : {i : T.Slot // T.IsCopied j i}, Pairwise
    (fun a b : Fin (width (T.role i.val)) => (x ⟨i,a⟩).val.Coprime (x ⟨i,b⟩).val)

def outsideWithinAtomPrimeSupport (T : Layout) (j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (x : OutsideConstituent T j width → PrimeUpTo Q) : Prop :=
  ∀ i : {i : T.Slot // T.IsOutside j i}, Pairwise
    (fun a b : Fin (width (T.role i.val)) => (x ⟨i,a⟩).val.Coprime (x ⟨i,b⟩).val)

theorem pairwise_coprime_sigma_iff {ι : Type*} {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (n : (i : ι) × κ i → ℕ) :
    Pairwise (fun u v => (n u).Coprime (n v)) ↔
      Pairwise (fun i j => (∏ a, n ⟨i,a⟩).Coprime (∏ b, n ⟨j,b⟩)) ∧
      ∀ i, Pairwise (fun a b : κ i => (n ⟨i,a⟩).Coprime (n ⟨i,b⟩)) := by
  constructor
  · intro h
    constructor
    · intro i j hij
      apply Nat.coprime_prod_left_iff.mpr
      intro a ha
      apply Nat.coprime_prod_right_iff.mpr
      intro b hb
      apply h
      intro he
      exact hij (congrArg Sigma.fst he)
    · intro i a b hab
      apply h
      intro he
      exact hab (by simpa using he)
  · rintro ⟨hcross,hwithin⟩ ⟨i,a⟩ ⟨j,b⟩ huv
    by_cases hij : i=j
    · subst j
      apply hwithin i
      intro hab
      subst b
      exact huv rfl
    · have h := Nat.coprime_prod_left_iff.mp (hcross hij) a (Finset.mem_univ _)
      exact Nat.coprime_prod_right_iff.mp h b (Finset.mem_univ _)

theorem constituent_prime_support_iff (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (x : T.Constituent width → PrimeUpTo Q) :
    Pairwise (fun i h => (x i).val.Coprime (x h).val) ↔
      Pairwise (fun i h => IsCoprime
        (constituentSampleState T width x i) (constituentSampleState T width x h)) ∧
      withinAtomPrimeSupport T width x := by
  have h := pairwise_coprime_sigma_iff (fun i : T.Constituent width => (x i).val)
  simpa only [Pairwise, constituentSampleState, ← Nat.cast_prod,
    Nat.isCoprime_iff_coprime, withinAtomPrimeSupport] using h

end Ostmann.Characters.Template

end

end OAI

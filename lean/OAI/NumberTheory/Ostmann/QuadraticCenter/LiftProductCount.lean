import OAI.NumberTheory.Ostmann.QuadraticCenter.LiftCountingBound
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductSampling

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem primeProductSamples_primeFactors {P : Finset ℕ}
    (hP : ∀ p ∈ P,Nat.Prime p) {q k : ℕ} (hq : q ∈ primeProductSamples P k) :
    Squarefree q ∧ q.primeFactors ∈ P.powersetCard k := by
  classical
  obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hq
  exact ⟨primeSubsetProduct_squarefree hP U,
    Finset.mem_powersetCard.mpr ⟨primeSubsetProduct_primeFactors_subset hP U,
      (primeSubsetProduct_primeFactors_card hP U).trans (Finset.mem_powersetCard.mp hU).2⟩⟩

theorem lifted_products_le_matching_moments {P E : Finset ℕ}
    (hP : ∀ p ∈ P,Nat.Prime p) {k : ℕ} (hE : E ⊆ primeProductSamples P k)
    (a : ℤ) (t : ℕ → ℤ) (H : ℕ)
    (hlift : ∀ q ∈ E,(boundedSubsetLifts q.primeFactors a t H).Nonempty) :
    k.factorial * E.card ≤
      ∑ n ∈ Finset.Icc (-(H:ℤ)) H,(matchingPrimes P a n t).card.descFactorial k := by
  classical
  have hcard : (E.image Nat.primeFactors).card = E.card := by
    apply Finset.card_image_of_injOn
    intro q hq r hr he
    have hqsf := (primeProductSamples_primeFactors hP (hE hq)).1
    have hrsf := (primeProductSamples_primeFactors hP (hE hr)).1
    calc
      q = ∏ p ∈ q.primeFactors,p := (Nat.prod_primeFactors_of_squarefree hqsf).symm
      _ = ∏ p ∈ r.primeFactors,p := by rw [he]
      _ = r := Nat.prod_primeFactors_of_squarefree hrsf
  rw [←hcard]
  apply lifted_subsets_le_matching_moments
  · intro U hU
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hU
    exact (primeProductSamples_primeFactors hP (hE hq)).2
  · intro U hU
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hU
    exact hlift q hq

theorem exists_fixed_multiplier_lift_moment {P E : Finset ℕ}
    (hP : ∀ p ∈ P,Nat.Prime p) {k : ℕ} (hE : E ⊆ primeProductSamples P k)
    (A H : ℕ) (hA : 0 < A) (t : ℕ → ℤ)
    (hlift : ∀ q ∈ E,∃ a : ℕ,1 ≤ a ∧ a ≤ A ∧
      (boundedSubsetLifts q.primeFactors a t H).Nonempty) :
    ∃ a : ℕ,1 ≤ a ∧ a ≤ A ∧
      k.factorial * E.card ≤ A *
        ∑ n ∈ Finset.Icc (-(H:ℤ)) H,(matchingPrimes P a n t).card.descFactorial k := by
  classical
  let Ea (a : ℕ) : Finset ℕ := E.filter
    (fun q => (boundedSubsetLifts q.primeFactors a t H).Nonempty)
  have hcover : E ⊆ (Finset.Icc 1 A).biUnion Ea := by
    intro q hq
    obtain ⟨a,ha1,haA,haq⟩ := hlift q hq
    exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_Icc.mpr ⟨ha1,haA⟩,
      Finset.mem_filter.mpr ⟨hq,haq⟩⟩
  have hne : (Finset.Icc 1 A).Nonempty := Finset.nonempty_Icc.mpr hA
  obtain ⟨a,ha,hamax⟩ := (Finset.Icc 1 A).exists_mem_eq_sup' hne (fun a => (Ea a).card)
  have hmax : ∀ b ∈ Finset.Icc 1 A,(Ea b).card ≤ (Ea a).card := by
    intro b hb
    rw [←hamax]
    exact Finset.le_sup' (fun b => (Ea b).card) hb
  have hcnt : E.card ≤ A*(Ea a).card := by
    calc
      _ ≤ ((Finset.Icc 1 A).biUnion Ea).card := Finset.card_le_card hcover
      _ ≤ ∑ b ∈ Finset.Icc 1 A,(Ea b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ Finset.Icc 1 A,(Ea a).card := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hm := lifted_products_le_matching_moments hP
    (show Ea a ⊆ primeProductSamples P k from fun q hq => hE (Finset.mem_filter.mp hq).1)
    (a:ℤ) t H (fun q hq => (Finset.mem_filter.mp hq).2)
  refine ⟨a,(Finset.mem_Icc.mp ha).1,(Finset.mem_Icc.mp ha).2,?_⟩
  calc
    _ ≤ k.factorial*(A*(Ea a).card) := Nat.mul_le_mul_left _ hcnt
    _ = A*(k.factorial*(Ea a).card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left A hm

end Ostmann.QuadraticCenter

end

end OAI

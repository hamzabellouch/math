import OAI.NumberTheory.Ostmann.Statement

namespace OAI

namespace Ostmann
open scoped Pointwise symmDiff

theorem finite_symmDiff_iff_eventuallyEqual (S T : Set ℕ) :
    (S ∆ T).Finite ↔ EventuallyEqual S T := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := h.bddAbove
    refine ⟨N+1, ?_⟩
    intro n hn
    by_contra hne
    have hmem : n ∈ S ∆ T := by
      simp only [Set.mem_symmDiff]
      tauto
    have := hN hmem
    omega
  · rintro ⟨N, hN⟩
    apply (Set.finite_Iio N).subset
    intro n hn
    change n < N
    by_contra hlt
    have he := hN n (by omega)
    simp only [Set.mem_symmDiff] at hn
    tauto

theorem infinite_symmDiff_iff_not_eventuallyEqual (S T : Set ℕ) :
    (S ∆ T).Infinite ↔ ¬ EventuallyEqual S T :=
  not_congr (finite_symmDiff_iff_eventuallyEqual S T)

theorem EventuallyEqual.refl (S : Set ℕ) : EventuallyEqual S S :=
  ⟨0, fun _ _ => Iff.rfl⟩

theorem EventuallyEqual.symm {S T : Set ℕ} (h : EventuallyEqual S T) :
    EventuallyEqual T S := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => (hN n hn).symm⟩

theorem EventuallyEqual.trans {S T U : Set ℕ}
    (hST : EventuallyEqual S T) (hTU : EventuallyEqual T U) : EventuallyEqual S U := by
  obtain ⟨N, hN⟩ := hST
  obtain ⟨M, hM⟩ := hTU
  exact ⟨max N M, fun n hn =>
    (hN n ((le_max_left N M).trans hn)).trans (hM n ((le_max_right N M).trans hn))⟩

theorem eventual_sumset_iff (A B : Set ℕ) :
    EventuallyEqual (A+B) primes ↔ ∃ N : ℕ,
      (∀ a ∈ A, ∀ b ∈ B, N ≤ a+b → Nat.Prime (a+b)) ∧
      (∀ p : ℕ, N ≤ p → Nat.Prime p → ∃ a ∈ A, ∃ b ∈ B, a+b=p) := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_, ?_⟩
    · intro a ha b hb hab
      exact (hN (a+b) hab).mp (Set.add_mem_add ha hb)
    · intro p hp hprime
      exact Set.mem_add.mp ((hN p hp).mpr hprime)
  · rintro ⟨N, hexclude, hcover⟩
    refine ⟨N, fun n hn => ⟨?_, ?_⟩⟩
    · intro hs
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hs
      exact hexclude a ha b hb hn
    · intro hp
      exact Set.mem_add.mpr (hcover n hn hp)

theorem indecomposable_iff_no_eventual_decomposition :
    AsymptoticallyIndecomposable ↔
      ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial → ¬ EventuallyEqual (A+B) primes := by
  constructor
  · intro h A B hA hB
    exact (infinite_symmDiff_iff_not_eventuallyEqual _ _).mp (h A B hA hB)
  · intro h A B hA hB
    exact (infinite_symmDiff_iff_not_eventuallyEqual _ _).mpr (h A B hA hB)

theorem indecomposable_iff_finite_modifications :
    AsymptoticallyIndecomposable ↔ FiniteModificationIndecomposable := by
  constructor
  · intro h S hS A B hA hB heq
    have hi := h A B hA hB
    change ¬ ((A+B) ∆ primes).Finite at hi
    exact hi (heq.symm ▸ hS)
  · intro h A B hA hB hfinite
    exact h (A+B) hfinite A B hA hB rfl

theorem finite_set_infinite_prime_disagreement {S : Set ℕ} (hS : S.Finite) :
    (S ∆ primes).Infinite := by
  apply (Nat.infinite_setOfPred_prime.sdiff hS).mono
  intro n hn
  exact Or.inr hn

theorem finite_finite_disagreement {A B : Set ℕ} (hA : A.Finite) (hB : B.Finite) :
    ((A+B) ∆ primes).Infinite := finite_set_infinite_prime_disagreement (hA.add hB)

theorem eventual_decomposition_infinite_or {A B : Set ℕ}
    (h : EventuallyEqual (A+B) primes) : A.Infinite ∨ B.Infinite := by
  classical
  by_cases hA : A.Finite
  · right
    intro hB
    exact (infinite_symmDiff_iff_not_eventuallyEqual _ _).mp
      (finite_finite_disagreement hA hB) h
  · exact Or.inl hA

theorem nontrivial_iff_exists_lt (A : Set ℕ) :
    A.Nontrivial ↔ ∃ a ∈ A, ∃ b ∈ A, a < b := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact ⟨a, ha, b, hb, hab⟩
    · exact ⟨b, hb, a, ha, hba⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨a, ha, b, hb, ne_of_lt hab⟩

theorem assemble_indecomposability
    (finite_left : ∀ A B : Set ℕ, A.Finite → A.Nontrivial → B.Nontrivial →
      ¬ EventuallyEqual (A+B) primes)
    (infinite_factors : ∀ A B : Set ℕ, A.Infinite → B.Infinite →
      ¬ EventuallyEqual (A+B) primes) : AsymptoticallyIndecomposable := by
  classical
  apply indecomposable_iff_no_eventual_decomposition.mpr
  intro A B hA hB h
  by_cases hAf : A.Finite
  · exact finite_left A B hAf hA hB h
  by_cases hBf : B.Finite
  · exact finite_left B A hBf hB hA (by simpa only [add_comm] using h)
  · exact infinite_factors A B hAf hBf h

theorem countUpTo_mono_set {A B : Set ℕ} (h : A ⊆ B) (x : ℕ) :
    countUpTo A x ≤ countUpTo B x := by
  apply Finset.card_le_card
  intro n hn
  obtain ⟨ha, hx⟩ := mem_elementsUpTo.mp hn
  exact mem_elementsUpTo.mpr ⟨h ha, hx⟩

theorem countUpTo_sumset_le (A B : Set ℕ) (x : ℕ) :
    countUpTo (A+B) x ≤ countUpTo A x * countUpTo B x := by
  classical
  have hsub : elementsUpTo (A+B) x ⊆
      ((elementsUpTo A x) ×ˢ (elementsUpTo B x)).image (fun z => z.1+z.2) := by
    intro n hn
    obtain ⟨hs, hx⟩ := mem_elementsUpTo.mp hn
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hs
    apply Finset.mem_image.mpr
    exact ⟨(a,b), Finset.mem_product.mpr
      ⟨mem_elementsUpTo.mpr ⟨ha, by omega⟩, mem_elementsUpTo.mpr ⟨hb, by omega⟩⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le).trans_eq (Finset.card_product _ _))

theorem countUpTo_le_of_eventual_cutoff {S T : Set ℕ} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → (n ∈ S ↔ n ∈ T)) (x : ℕ) :
    countUpTo S x ≤ countUpTo T x + N := by
  classical
  have hs : elementsUpTo S x ⊆ elementsUpTo T x ∪ Finset.range N := by
    intro n hn
    obtain ⟨hnS, hnx⟩ := mem_elementsUpTo.mp hn
    by_cases hnN : n < N
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_range.mpr hnN))
    · exact Finset.mem_union.mpr (Or.inl
        (mem_elementsUpTo.mpr ⟨(h n (by omega)).mp hnS, hnx⟩))
  exact (Finset.card_le_card hs).trans (by
    simpa only [Finset.card_range, countUpTo] using Finset.card_union_le (elementsUpTo T x) (Finset.range N))

theorem EventuallyEqual.counting_bounds {S T : Set ℕ} (h : EventuallyEqual S T) :
    ∃ N : ℕ, ∀ x : ℕ,
      countUpTo S x ≤ countUpTo T x + N ∧ countUpTo T x ≤ countUpTo S x + N := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun x => ⟨countUpTo_le_of_eventual_cutoff hN x,
    countUpTo_le_of_eventual_cutoff (fun n hn => (hN n hn).symm) x⟩⟩

@[simp] theorem countUpTo_primes (x : ℕ) : countUpTo primes x = Nat.primeCounting x := by
  classical
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range, countUpTo]
  apply congrArg Finset.card
  ext number
  simp [mem_elementsUpTo, primes, and_comm]

theorem EventuallyEqual.primeCounting_le {A B : Set ℕ}
    (h : EventuallyEqual (A+B) primes) :
    ∃ N : ℕ, ∀ x : ℕ, Nat.primeCounting x ≤ countUpTo A x * countUpTo B x + N := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun x => ?_⟩
  rw [← countUpTo_primes]
  exact (countUpTo_le_of_eventual_cutoff (fun n hn => (hN n hn).symm) x).trans
    (Nat.add_le_add_right (countUpTo_sumset_le A B x) N)

end Ostmann

end OAI

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.UnorderedPairSums

variable {V : Type*} [DecidableEq V]

theorem ordered_fiber (s : Finset V) (i j : V)
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    s.offDiag.filter (fun p => ({p.1,p.2} : Finset V) = {i,j}) =
      {(i,j),(j,i)} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hp,he⟩
    have hs : ({p.1,p.2} : Set V) = {i,j} := by
      simpa only [Finset.coe_pair] using congrArg (fun t : Finset V => (t : Set V)) he
    rcases Set.pair_eq_pair_iff.mp hs with hp | hp
    · exact Or.inl (Prod.ext hp.1 hp.2)
    · exact Or.inr (Prod.ext hp.1 hp.2)
  · rintro (rfl | rfl) <;> simp [hi,hj,hij,hij.symm, Finset.pair_comm]

theorem sum_offDiag_eq_two_mul (s : Finset V) (f : Finset V → ℝ) :
    (∑ p ∈ s.offDiag, f {p.1,p.2}) = 2 * ∑ a ∈ s.powersetCard 2, f a := by
  have hmap (p : V × V) (hp : p ∈ s.offDiag) :
      ({p.1,p.2} : Finset V) ∈ s.powersetCard 2 := by
    obtain ⟨hi,hj,hij⟩ := Finset.mem_offDiag.mp hp
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj
    · simp [hij]
  rw [← Finset.sum_fiberwise_of_maps_to' hmap f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨has, hac⟩ := Finset.mem_powersetCard.mp ha
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hac
  have hi := has (Finset.mem_insert_self i {j})
  have hj := has (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
  rw [ordered_fiber s i j hi hj hij]
  have hp : (i,j) ≠ (j,i) := fun h => hij (congrArg Prod.fst h)
  simp [hp, two_mul]

theorem sum_ordered_eq_two_mul [Fintype V] (f : Finset V → ℝ) :
    (∑ i : V, ∑ j : V, if i ≠ j then f {i,j} else 0) =
      2 * ∑ a ∈ (Finset.univ : Finset V).powersetCard 2, f a := by
  have he : (Finset.univ : Finset V).offDiag =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => p.1 ≠ p.2) := by
    ext p
    simp [Finset.mem_offDiag]
  have h := sum_offDiag_eq_two_mul (Finset.univ : Finset V) f
  rw [he, Finset.sum_filter, Finset.sum_product] at h
  exact h

end Problem315.UnorderedPairSums

end

end OAI

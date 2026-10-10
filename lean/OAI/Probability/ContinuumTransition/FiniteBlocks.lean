import OAI.Probability.ContinuumTransition.FiniteProduct

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem familyTerm_gibbs_empty_ne_zero (U : Space → Space → ℝ) (β h : ℝ) {n : ℕ} (hn : n ≠ 0) :
    familyTerm (gibbsFamily U β h) ∅ n = 0 := by
  have hp : 0 < n := Nat.pos_of_ne_zero hn
  have he : {x : Fin n → Space | ∀ i, x i ∈ (∅ : Set Space)} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨⟨0, hp⟩, not_false⟩
  simp only [familyTerm, familyIntegral, he, setIntegral_empty, zero_div]

theorem grandFinite_gibbs_blocks {κ : Type u_1} {U : Space → Space → ℝ}
    (hU : ∀ x y, U x y = U y x) {β h : ℝ} (hβ : 0 ≤ β)
    (A : κ → Set Space) (s : Finset κ)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : (s : Set κ).Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, 0 ≤ U x y)
    (hFi : ∀ (ι : Type) [Fintype ι], IntegrableOn (gibbsFamily U β h ι)
      {x | ∀ i, x i ∈ ⋃ j ∈ s, A j})
    (hFA : ∀ i ∈ s, GrandFinite (gibbsFamily U β h) (A i)) :
    GrandFinite (gibbsFamily U β h) (⋃ i ∈ s, A i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty] at hFi ⊢
    refine ⟨hFi, ?_⟩
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    exact familyTerm_gibbs_empty_ne_zero U β h (by simpa only [Finset.mem_singleton] using hn)
  | @insert i s hi ih =>
    let B := ⋃ j ∈ s, A j
    have hB : MeasurableSet B := MeasurableSet.biUnion s.finite_toSet.countable
      (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    have hAi := hA i (Finset.mem_insert_self _ _)
    have hAB : Disjoint (A i) B := by
      apply Set.disjoint_iUnion₂_right.mpr
      intro j hj
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) (fun hh => hi (hh ▸ hj))
    have hieq : (⋃ j ∈ insert i s, A j) = A i ∪ B := by simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]; rfl
    have hFiB (ι : Type) [Fintype ι] : IntegrableOn (gibbsFamily U β h ι)
        {x | ∀ a, x a ∈ B} := by
      apply (hFi ι).mono_set
      intro x hx a
      rw [hieq]
      exact Or.inr (hx a)
    have hFB := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (hd.mono (Finset.subset_insert _ _))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      hFiB (fun j hj => hFA j (Finset.mem_insert_of_mem hj))
    rw [hieq] at hFi ⊢
    apply GrandFinite.union_product (gibbsFamily_relabel U β h) (gibbsFamily_relabel U β h)
      hAi hB hAB (hFA i (Finset.mem_insert_self _ _)) hFB hFi (gibbsFamily_nonneg U β h)
    intro n r x hx
    apply gibbsFamily_binary_le hU hβ ?_ r hx
    intro a ha b hb
    obtain ⟨j, hj, hjb⟩ := mem_iUnion₂.mp hb
    exact hcross i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
      (fun hh => hi (hh ▸ hj)) a ha b hjb

end ContinuumTemperature
end

end OAI

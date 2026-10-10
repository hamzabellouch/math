import OAI.NumberTheory.TwoPoint.Circuits.CircuitCanonicalTree
import OAI.NumberTheory.TwoPoint.Circuits.CircuitQueryWalk

namespace OAI

/-! A longest branch of the concrete canonical tree supplies a query walk
with at least that many queried variables. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace BooleanDecisionTree

lemma queryVariables_depth_state {n : ℕ} (is : List (Fin n))
    (k : PartialAssignment n → BooleanDecisionTree n) (ρ : PartialAssignment n) :
    ∃ τ : PartialAssignment n,
      (queryVariables is k ρ).depth = is.length + (k τ).depth ∧
      (∀ j ∉ is.toFinset, τ j = ρ j) ∧
      (∀ j ∈ is.toFinset, ∃ b, τ j = some b) := by
  induction is generalizing ρ with
  | nil => exact ⟨ρ, by simp [queryVariables], fun _ _ => rfl, by simp⟩
  | cons i is ih =>
    obtain ⟨b, hb⟩ : ∃ b : Bool,
        max (queryVariables is k (Function.update ρ i (some false))).depth
            (queryVariables is k (Function.update ρ i (some true))).depth =
          (queryVariables is k (Function.update ρ i (some b))).depth := by
      by_cases h : (queryVariables is k (Function.update ρ i (some false))).depth ≤
          (queryVariables is k (Function.update ρ i (some true))).depth
      · exact ⟨true, max_eq_right h⟩
      · exact ⟨false, max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h))⟩
    obtain ⟨τ, ht, hout, hin⟩ := ih (Function.update ρ i (some b))
    refine ⟨τ, ?_, ?_, ?_⟩
    · simp only [queryVariables, depth, hb, ht, List.length_cons]
      omega
    · intro j hj
      have hj' : j ∉ is.toFinset := fun h => hj (by simp [h])
      have hji : j ≠ i := fun h => hj (by simp [h])
      rw [hout j hj']
      simp [hji]
    · intro j hj
      by_cases hj' : j ∈ is.toFinset
      · exact hin j hj'
      · have hji : j = i := by simpa [hj'] using hj
        subst j
        exact ⟨b, by simpa using hout i hj'⟩

lemma queryVariables_depth_witness {n : ℕ} (is : List (Fin n))
    (k : PartialAssignment n → BooleanDecisionTree n) (ρ : PartialAssignment n) :
    ∃ x : BooleanCube n, (queryVariables is k ρ).depth =
      is.length + (k (ρ.assign is.toFinset x)).depth := by
  obtain ⟨τ, ht, hout, hin⟩ := queryVariables_depth_state is k ρ
  let x : BooleanCube n := fun i => (τ i).getD false
  have he : τ = ρ.assign is.toFinset x := by
    funext i
    by_cases hi : i ∈ is.toFinset
    · obtain ⟨b, hb⟩ := hin i hi
      simp [PartialAssignment.assign, hi, x, hb]
    · simp [PartialAssignment.assign, hi, hout i hi]
  exact ⟨x, by simpa only [he] using ht⟩

end BooleanDecisionTree

lemma CubeTerm.satisfied_of_live_empty {n : ℕ} (C : CubeTerm n)
    (ρ : PartialAssignment n) (hC : C.Compatible ρ) (h : C.live ρ = ∅) :
    C.Satisfied ρ := by
  intro i hi
  rcases hC i hi with hn | hv
  · have hm : i ∈ C.live ρ := mem_filter.mpr ⟨hi, hn⟩
    rw [h] at hm
    exact False.elim (notMem_empty i hm)
  · exact hv

theorem canonicalDNFTree_depth_walk {n : ℕ} (F : List (CubeTerm n))
    (ρ : PartialAssignment n) : ∃ bs : List (DNFQueryBlock n),
      CanonicalDNFWalk F ρ bs ∧ (canonicalDNFTree F ρ).depth ≤ DNFQueryBlock.length bs := by
  induction F generalizing ρ with
  | nil => exact ⟨[], .nil _ _, le_refl _⟩
  | cons C F ih =>
    by_cases hC : C.Compatible ρ
    · by_cases he : C.live ρ = ∅
      · refine ⟨[], .nil _ _, ?_⟩
        have hs := C.satisfied_of_live_empty ρ hC he
        simp [canonicalDNFTree, hC, he, BooleanDecisionTree.queryVariables, hs,
          BooleanDecisionTree.depth, DNFQueryBlock.length]
      · have hne := Finset.nonempty_iff_ne_empty.mpr he
        let k := fun τ => if C.Satisfied τ then BooleanDecisionTree.leaf true
          else canonicalDNFTree F τ
        obtain ⟨x, hx⟩ := BooleanDecisionTree.queryVariables_depth_witness
          ((C.live ρ).sort (· ≤ ·)) k ρ
        simp only [Finset.sort_toFinset, Finset.length_sort] at hx
        have hdepth : (canonicalDNFTree (C :: F) ρ).depth =
            (C.live ρ).card + (k (ρ.assign (C.live ρ) x)).depth := by
          simpa only [canonicalDNFTree, hC, ite_true] using hx
        by_cases hs : C.Satisfied (ρ.assign (C.live ρ) x)
        · refine ⟨[⟨C, C.live ρ, x⟩], .step x hC hne (.nil _ _), ?_⟩
          simp [hdepth, k, hs, BooleanDecisionTree.depth, DNFQueryBlock.length]
        · obtain ⟨bs, hbs, hb⟩ := ih (ρ.assign (C.live ρ) x)
          refine ⟨⟨C, C.live ρ, x⟩ :: bs, .step x hC hne hbs, ?_⟩
          simpa only [hdepth, k, hs, ite_false, DNFQueryBlock.length] using
            Nat.add_le_add_left hb (C.live ρ).card
    · obtain ⟨bs, hbs, hb⟩ := ih ρ
      refine ⟨bs, .skip hC hbs, ?_⟩
      simpa only [canonicalDNFTree, hC, ite_false] using hb

end TwoPointCorrelations

end OAI

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import OAI.Computability.BinPacking.Hardness.LiteralSlotGraph

namespace OAI

namespace BinPackingGap.LiteralSlotGraph

open BinPackingGames.Foundations.Target
open scoped BigOperators

def satisfiedClauses (F : Formula) (A : Fin F.variables → Bool) :
    Finset (Fin F.clauses.length) :=
  Finset.univ.filter (fun c => (F.clauses[c]).eval A = true)

def failedClauses (F : Formula) (A : Fin F.variables → Bool) :
    Finset (Fin F.clauses.length) :=
  Finset.univ.filter (fun c => (F.clauses[c]).eval A ≠ true)

theorem clause_true_of_slot_true {n : ℕ} (c : Clause n) (A : Fin n → Bool)
    (j : Fin 3) (hj : c[j].eval A = true) : c.eval A = true := by
  fin_cases j <;> simp_all [Clause.eval]

theorem clause_counts (F : Formula) (A : Fin F.variables → Bool) :
    (satisfiedClauses F A).card + (failedClauses F A).card = F.clauses.length := by
  simpa only [satisfiedClauses, failedClauses, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin F.clauses.length)))
      (fun c => (F.clauses[c]).eval A = true))

theorem failedClauses_card_sum (F : Formula) (A : Fin F.variables → Bool) :
    (failedClauses F A).card =
      ∑ c : Fin F.clauses.length, if (F.clauses[c]).eval A then 0 else 1 := by
  unfold failedClauses
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  cases (F.clauses[c]).eval A <;> simp

theorem independent_card_le_satisfied (F : Formula) (S : Finset (Vertex F))
    (hS : Independent F S) (A : Fin F.variables → Bool)
    (hA : ∀ u ∈ S, (literal F u).eval A = true) :
    S.card ≤ (satisfiedClauses F A).card := by
  have himage : (S.image (occurrence F)).card = S.card :=
    Finset.card_image_iff.mpr (occurrence_injective_on_independent F S hS)
  rw [← himage]
  apply Finset.card_le_card
  intro c hc
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact clause_true_of_slot_true _ A (slot F u) (hA u hu)

theorem assignment_count_of_cover (F : Formula) (C : Finset (Vertex F))
    (hC : (graph F).IsCover C) :
    ∃ A : Fin F.variables → Bool,
      2 * F.clauses.length + (failedClauses F A).card ≤ C.card := by
  let S : Finset (Vertex F) := Finset.univ \ C
  have hS : Independent F S := independent_complement_of_cover F C hC
  obtain ⟨A, hA⟩ := assignment_of_independent F S hS
  have hle := independent_card_le_satisfied F S hS A hA
  have hsum := clause_counts F A
  have hcard : S.card + C.card = 3 * F.clauses.length := by
    simpa only [S, Finset.card_univ, Fintype.card_fin, vertexCount] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C))
  exact ⟨A, by omega⟩

theorem cover_count_of_clause_gap (F : Formula) (D : ℕ)
    (hgap : ∀ A : Fin F.variables → Bool,
      F.clauses.length ≤ D * (failedClauses F A).card)
    (C : Finset (Vertex F)) (hC : (graph F).IsCover C) :
    D * (2 * F.clauses.length) + F.clauses.length ≤ D * C.card := by
  obtain ⟨A, hA⟩ := assignment_count_of_cover F C hC
  calc
    D * (2 * F.clauses.length) + F.clauses.length ≤
        D * (2 * F.clauses.length) + D * (failedClauses F A).card :=
      Nat.add_le_add_left (hgap A) _
    _ = D * (2 * F.clauses.length + (failedClauses F A).card) := (Nat.mul_add _ _ _).symm
    _ ≤ D * C.card := Nat.mul_le_mul_left D hA

end BinPackingGap.LiteralSlotGraph

end OAI

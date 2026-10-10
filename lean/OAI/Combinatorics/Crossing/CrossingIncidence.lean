import OAI.Combinatorics.Crossing.DrawingDefinition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

theorem crossingCount_attainment (D₀ : AdmissibleDrawing m n) :
    ∃ D : AdmissibleDrawing m n, crossingCount D = ordinaryCrossingNumber m n := by
  exact csInf_mem (show (Set.range (@crossingCount m n)).Nonempty from
    ⟨crossingCount D₀, D₀, rfl⟩)

theorem ordinaryCrossingNumber_le_count (D : AdmissibleDrawing m n) :
    ordinaryCrossingNumber m n ≤ crossingCount D :=
  csInf_le' ⟨D, rfl⟩

theorem crossing_incident_iff (D : AdmissibleDrawing m n) (x : Plane)
    (e f : BipartiteEdge m n) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) (g : BipartiteEdge m n) :
    x ∈ edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  constructor
  · intro hg
    by_contra hh
    have hge : e ≠ g := by tauto
    have hgf : f ≠ g := by tauto
    have hmem : x ∈ edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f ∩
        edgeInterior D.toContinuousDrawing g := ⟨⟨he,hf⟩,hg⟩
    rw [D.no_triples e f g hef hge hgf] at hmem
    exact hmem
  · rintro (rfl | rfl) <;> assumption

theorem crossing_two_edges (D : AdmissibleDrawing m n) (x : Plane)
    (hx : x ∈ crossingPoints D.toContinuousDrawing) :
    ∃ e f : BipartiteEdge m n, e ≠ f ∧
      ∀ g, x ∈ edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  obtain ⟨e,f,hef,he,hf⟩ := hx
  exact ⟨e,f,hef,crossing_incident_iff D x e f hef he hf⟩

def pairCrossings (D : AdmissibleDrawing m n) (e f : BipartiteEdge m n) : Finset Plane :=
  D.crossings_finite.toFinset.filter (fun x => e ≠ f ∧
    x ∈ edgeInterior D.toContinuousDrawing e ∧ x ∈ edgeInterior D.toContinuousDrawing f)

theorem pairCrossings_self (D : AdmissibleDrawing m n) (e : BipartiteEdge m n) :
    pairCrossings D e e = ∅ := by
  simp [pairCrossings]

theorem pairCrossings_comm (D : AdmissibleDrawing m n) (e f : BipartiteEdge m n) :
    pairCrossings D e f = pairCrossings D f e := by
  ext x
  simp only [pairCrossings, Finset.mem_filter]
  tauto

theorem crossing_ordered_incidence (D : AdmissibleDrawing m n) (x : Plane)
    (hx : x ∈ crossingPoints D.toContinuousDrawing) :
    (∑ e : BipartiteEdge m n, ∑ f : BipartiteEdge m n,
      if e ≠ f ∧ x ∈ edgeInterior D.toContinuousDrawing e ∧
        x ∈ edgeInterior D.toContinuousDrawing f then (1 : ℕ) else 0) = 2 := by
  classical
  obtain ⟨e,f,hef,hinc⟩ := crossing_two_edges D x hx
  simp_rw [hinc]
  have hp : ∀ a b : BipartiteEdge m n,
      (a ≠ b ∧ (a = e ∨ a = f) ∧ (b = e ∨ b = f)) ↔
        ((a = e ∧ b = f) ∨ (a = f ∧ b = e)) := by
    intro a b
    constructor
    · rintro ⟨hab, rfl | rfl, rfl | rfl⟩ <;> tauto
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> tauto
  simp_rw [hp]
  have hi : ∀ a b : BipartiteEdge m n,
      (if (a = e ∧ b = f) ∨ (a = f ∧ b = e) then (1 : ℕ) else 0) =
        (if a = e ∧ b = f then 1 else 0) + (if a = f ∧ b = e then 1 else 0) := by
    intro a b
    split_ifs <;> simp_all
  simp_rw [hi, Finset.sum_add_distrib]
  simp [ite_and]

theorem sum_pairCrossings_card (D : AdmissibleDrawing m n) :
    (∑ e : BipartiteEdge m n, ∑ f : BipartiteEdge m n, (pairCrossings D e f).card) =
      2 * crossingCount D := by
  classical
  simp only [pairCrossings, Finset.card_filter]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext f; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have he : ∀ x ∈ D.crossings_finite.toFinset,
      (∑ f : BipartiteEdge m n, ∑ e : BipartiteEdge m n,
        if e ≠ f ∧ x ∈ edgeInterior D.toContinuousDrawing e ∧
          x ∈ edgeInterior D.toContinuousDrawing f then (1 : ℕ) else 0) = 2 := by
    intro x hx
    rw [Finset.sum_comm]
    exact crossing_ordered_incidence D x (by simpa using hx)
  simp_rw [Finset.sum_congr rfl he]
  simp [crossingCount, Nat.mul_comm]

end Zarankiewicz

end

end OAI

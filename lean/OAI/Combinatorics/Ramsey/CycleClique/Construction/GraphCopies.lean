import OAI.Combinatorics.Ramsey.CycleClique.Construction.Definitions
import OAI.Combinatorics.Ramsey.CycleClique.Basic

namespace OAI

/-! Equivalence between labelled cycles and copies of the Mathlib cycle graph. -/

namespace CycleClique.Construction

open scoped SimpleGraph

theorem hasCycle_iff_copy {V : Type*} {G : SimpleGraph V} {m : ℕ} (hm : 3 ≤ m) :
    HasCycle G m ↔ SimpleGraph.cycleGraph m ⊑ G := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hnext (i : Fin (k + 2)) : cycleNext i = i + 1 := by
    apply Fin.ext
    simp [cycleNext, Fin.val_add]
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
    intro i j hij
    rcases SimpleGraph.cycleGraph_adj.mp hij with hij | hij
    · have h : i = j + 1 := (sub_eq_iff_eq_add').mp hij
      rw [h]
      exact (hnext j ▸ he j).symm
    · have h : j = i + 1 := (sub_eq_iff_eq_add').mp hij
      rw [h]
      exact hnext i ▸ he i
  · rintro ⟨f⟩
    refine ⟨f, f.injective, fun i => f.toHom.map_adj ?_⟩
    rw [hnext]
    apply SimpleGraph.cycleGraph_adj.mpr
    exact Or.inr (add_sub_cancel_left i 1)

theorem hasIndependent_iff_copy {V : Type*} {G : SimpleGraph V} {n : ℕ} :
    HasIndependent G n ↔ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ := by
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
    intro i j hij
    exact ⟨fun h => hij (hf h), he i j⟩
  · rintro ⟨f⟩
    refine ⟨f, f.injective, ?_⟩
    intro i j
    by_cases hij : i = j
    · subst j
      exact G.loopless.irrefl _
    · exact (f.toHom.map_adj hij).2

theorem ramseyProperty_iff {m n N : ℕ} (hm : 3 ≤ m) :
    RamseyProperty m n N ↔ CycleClique.RamseyProperty m n N := by
  simp only [RamseyProperty, CycleClique.RamseyProperty, hasCycle_iff_copy hm,
    hasIndependent_iff_copy]

theorem isRamseyNumber_iff {m n N : ℕ} (hm : 3 ≤ m) :
    IsRamseyNumber m n N ↔
      CycleClique.RamseyProperty m n N ∧ ∀ M < N, ¬ CycleClique.RamseyProperty m n M := by
  simp only [IsRamseyNumber, ramseyProperty_iff hm]

end CycleClique.Construction

end OAI

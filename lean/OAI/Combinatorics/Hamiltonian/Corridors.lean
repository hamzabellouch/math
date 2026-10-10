import OAI.Combinatorics.Hamiltonian.SquareGrid

namespace OAI

/-! Disjoint lattice corridors obtained from a crossing-free plane embedding. -/

namespace Barnette

structure CorridorModel {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : V → Set W
  corridor : G.Dart → Set W
  branch_finite : ∀ v, (branch v).Finite
  corridor_finite : ∀ d, (corridor d).Finite
  branch_connected : ∀ v, (H.induce (branch v)).Connected
  corridor_connected : ∀ d, (H.induce (corridor d)).Connected
  branches_disjoint : ∀ v w, v ≠ w → Disjoint (branch v) (branch w)
  corridors_disjoint : ∀ d e, d.edge ≠ e.edge → Disjoint (corridor d) (corridor e)
  nonincident_disjoint : ∀ v d, v ≠ d.fst → v ≠ d.snd →
    Disjoint (branch v) (corridor d)
  incident_meets : ∀ d, (branch d.fst ∩ corridor d).Nonempty ∧
    (branch d.snd ∩ corridor d).Nonempty

namespace PlaneEmbedding

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] (E : PlaneEmbedding G)

private def allSets : V ⊕ G.Dart → Set (ℝ × ℝ)
  | .inl v => E.branch v
  | .inr d => E.core d

private def apart : V ⊕ G.Dart → V ⊕ G.Dart → Prop
  | .inl v, .inl w => v ≠ w
  | .inl v, .inr d => v ≠ d.fst ∧ v ≠ d.snd
  | .inr d, .inl v => v ≠ d.fst ∧ v ≠ d.snd
  | .inr d, .inr e => d.edge ≠ e.edge

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem allSets_compact (i : V ⊕ G.Dart) : IsCompact (E.allSets i) := by
  cases i with
  | inl v => exact E.branch_compact v
  | inr d => exact E.core_compact d

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem allSets_disjoint (i j : V ⊕ G.Dart) (h : apart i j) :
    Disjoint (E.allSets i) (E.allSets j) := by
  cases i with
  | inl v =>
    cases j with
    | inl w => exact E.branch_disjoint h
    | inr d => exact E.branch_core_disjoint h.1 h.2
  | inr d =>
    cases j with
    | inl v => exact (E.branch_core_disjoint h.1 h.2).symm
    | inr e => exact E.core_disjoint h

omit [DecidableEq V] in
include E in

theorem exists_lattice_corridor_model : Nonempty (CorridorModel G SquareGrid.graph) := by
  classical
  obtain ⟨ε, hε, hsep⟩ := uniform_thickening E.allSets E.allSets_compact apart E.allSets_disjoint
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hδε : δ < ε := half_lt_self hε
  have hdis (i j : V ⊕ G.Dart) (h : apart i j) :
      Disjoint (SquareGrid.cells δ (E.allSets i)) (SquareGrid.cells δ (E.allSets j)) :=
    SquareGrid.cells_disjoint hδε (hsep i j h)
  refine ⟨{
    branch := fun v => SquareGrid.cells δ (E.branch v)
    corridor := fun d => SquareGrid.cells δ (E.core d)
    branch_finite := fun v => SquareGrid.cells_finite hδ (E.branch_compact v)
    corridor_finite := fun d => SquareGrid.cells_finite hδ (E.core_compact d)
    branch_connected := fun v => SquareGrid.cells_connected hδ (E.branch_compact v)
      (E.branch_connected v)
    corridor_connected := fun d => SquareGrid.cells_connected hδ (E.core_compact d)
      (E.core_connected d)
    branches_disjoint := fun v w h => hdis (.inl v) (.inl w) h
    corridors_disjoint := fun d e h => hdis (.inr d) (.inr e) h
    nonincident_disjoint := fun v d h₁ h₂ => hdis (.inl v) (.inr d) ⟨h₁, h₂⟩
    incident_meets := ?_
  }⟩
  intro d
  have meets {K L : Set (ℝ × ℝ)} (h : (K ∩ L).Nonempty) :
      (SquareGrid.cells δ K ∩ SquareGrid.cells δ L).Nonempty := by
    obtain ⟨p, hpK, hpL⟩ := h
    obtain ⟨z, hz⟩ := SquareGrid.cell_cover hδ p
    exact ⟨z, ⟨p, hz, hpK⟩, ⟨p, hz, hpL⟩⟩
  exact ⟨meets (E.branch_core_meets d).1, meets (E.branch_core_meets d).2⟩

end
end PlaneEmbedding
end Barnette

end OAI

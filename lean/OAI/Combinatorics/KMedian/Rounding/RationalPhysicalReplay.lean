import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalRound
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalKernel

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F J : Type} [LinearOrder F] {Δ : ℕ}

noncomputable def labels (g β : ℚ) (x : ℝ) (d : J → F → ℝ)
    (s : State F Δ g β) (S : J → Finset (CopyState.Copy (F := F) Δ)) :
    J → Finset (CopyState.Copy (F := F) Δ) :=
  match s.2 with
  | none => S
  | some ⟨A,⟨G,Z⟩⟩ => fun j => CopyState.roundAlive A (S j) G
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z x (g:ℝ) (d j)

noncomputable def replayList (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ)) :
    List (State F Δ g β) → J → Finset (CopyState.Copy (F := F) Δ)
  | [] => S₀
  | s::L => labels g β (x (L.length-1)) d s (replayList g β x d S₀ L)

noncomputable def replay (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (h : SparseHistories.History (State F Δ g β)) :
    J → Finset (CopyState.Copy (F := F) Δ) := replayList g β x d S₀ (h.1::h.2)

theorem labels_subset (g β : ℚ) (x : ℝ) (d : J → F → ℝ)
    (s : State F Δ g β) (S : J → Finset (CopyState.Copy (F := F) Δ)) (j : J) :
    labels g β x d s S j ⊆ S j := by
  obtain ⟨A,e⟩ := s
  cases e with
  | none => exact Subset.rfl
  | some e =>
    obtain ⟨B,⟨G,Z⟩⟩ := e
    exact CopyState.roundAlive_subset B (S j) G _ Z x (g:ℝ) (d j)

theorem labels_active (g β : ℚ) (x : ℝ) (d : J → F → ℝ)
    (A : Finset (CopyState.Copy (F := F) Δ)) (e : RationalBatchData.Event A g β)
    (S : J → Finset (CopyState.Copy (F := F) Δ)) (j : J) :
    labels g β x d (updateEvent g β A e) S j ⊆ (updateEvent g β A e).1 := by
  obtain ⟨G,Z⟩ := e
  exact CopyState.roundAlive_active A (S j) G _ Z x (g:ℝ) (d j)

theorem replay_extend (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (h : SparseHistories.History (State F Δ g β)) (s : State F Δ g β) :
    replay g β x d S₀ (SparseHistories.extend h s)=
      labels g β (x h.2.length) d s (replay g β x d S₀ h) := by
  simp only [replay,SparseHistories.extend,replayList,List.length_cons,Nat.add_sub_cancel]

theorem replay_subset (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (h : SparseHistories.History (State F Δ g β)) (j : J) :
    replay g β x d S₀ h j ⊆ S₀ j := by
  have hh : ∀ L, replayList g β x d S₀ L j ⊆ S₀ j := by
    intro L
    induction L with
    | nil => exact Subset.rfl
    | cons s L ih => exact (labels_subset g β (x (L.length-1)) d s _ j).trans ih
  exact hh _

theorem histories_alive (d₀ : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (x : ℕ → ℝ) (d : J → F → ℝ) (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (hactive : ∀ j, S₀ j ⊆ A)
    (i : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) (j : J) :
    replay g β x d S₀ (histories d₀ g β p φ P hp hφ hupper A T).states[i.val] j ⊆
      (histories d₀ g β p φ P hp hφ hupper A T).states[i.val].1.1 := by
  have hh := SparseHistories.tree_property
    (fun t => step d₀ g β p φ (P t) hp hφ hupper) (A,none)
    (fun _ h => ∀ j, replay g β x d S₀ h j ⊆ h.1.1) hactive
    (fun t h _ k => by
      obtain ⟨e,he⟩ := step_records d₀ g β p φ (P t) hp hφ hupper h.1 k
      intro j
      rw [replay_extend,he]
      exact labels_active g β (x h.2.length) d h.1.1 e _ j) T i
  exact hh j

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI

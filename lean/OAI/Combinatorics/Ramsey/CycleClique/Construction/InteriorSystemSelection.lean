import OAI.Combinatorics.Ramsey.CycleClique.Construction.InteriorChainSelection
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalClassification

namespace OAI

/-! Counting the selected internal vertices, with one unit of loss for
components that contain more than a single amount-two path. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

noncomputable def selectedChains (Q : Finset V) (C : List (List V)) : List V :=
  (C.map (selectedChain Q)).flatten

noncomputable def selectionLoss (C : List (List V)) : ℕ :=
  (C.map (fun l => if l.length = 4 then 0 else 1)).sum

theorem selectedChains_sublist (C : List (List V)) :
    (selectedChains Q C).Sublist C.flatten := by
  induction C with
  | nil => exact .refl _
  | cons l C ih => exact (selectedChain_sublist l).append ih

namespace SystemAssignedAmounts

theorem selected_length_bounds {C : List (List V)} {w : List ℕ}
    (h : SystemAssignedAmounts Q C w) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hlen : ∀ l ∈ C, 3 ≤ l.length)
    (hlast : ∀ l ∈ C, ∀ x ∈ l.getLast?, x ∈ Q) :
    (selectedChains Q C).length + selectionLoss C = w.length + C.length ∧
      w.length + C.length + selectionLoss C ≤ w.sum := by
  induction h with
  | nil => simp [selectedChains, selectionLoss]
  | @cons l C a w ha hw ih =>
    have hla := hlen l (by simp)
    have hane : a ≠ [] := by
      intro he
      have hh := ha.chain_length (by intro he'; simp [he'] at hla)
      simp only [he, List.sum_nil, List.length_nil, zero_add] at hh
      omega
    have hb := selectedChain_length_bounds ha hane
      (fun a ha => hmin a (List.mem_append_left _ ha)) (hlast l (by simp))
    have hi := ih (fun a ha => hmin a (List.mem_append_right _ ha))
      (fun l hl => hlen l (by simp [hl])) (fun l hl => hlast l (by simp [hl]))
    simp only [selectedChains, List.map_cons, List.flatten_cons, List.length_append,
      selectionLoss, List.sum_cons, List.length_cons] at hi ⊢
    simp only [List.sum_append]
    omega

end SystemAssignedAmounts

namespace ExpandedPathSystem

theorem selectedChains_nodup (S : ExpandedPathSystem G Q) :
    (selectedChains Q S.chains).Nodup :=
  S.flatten_nodup.sublist (selectedChains_sublist S.chains)

theorem selectedChains_mem_vertices (S : ExpandedPathSystem G Q) {x : V}
    (hx : x ∈ selectedChains Q S.chains) : x ∈ S.vertices :=
  List.mem_toFinset.mpr ((selectedChains_sublist S.chains).subset hx)

theorem selectedChains_large (S : ExpandedPathSystem G Q) {w : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hincident : S.incident = Q.card) (hamount : S.amount ≤ Q.card + 1) :
    Q.card - 1 ≤ (selectedChains Q S.chains).length := by
  have hb := h.selected_length_bounds hmin S.nontrivial (fun l hl => (S.endpoints l hl).2)
  have hsum : w.sum = S.amount := by
    rw [h.sum_eq]
    exact S.toRaw.amount_eq_outside_count.symm
  have hwlen : w.length = S.assignedCount := by
    rw [h.length_eq, S.assignedCount_eq_raw]
  have hc := S.assignedCount_add_chains_length
  rw [hwlen, hsum] at hb
  rw [hincident] at hc
  omega

end ExpandedPathSystem

end CycleClique.Construction

end OAI

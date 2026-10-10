import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCoverage

namespace OAI

/-! First-use initialization contributes at most two qubits at each gate time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaFirstUseSites (c : QMACircuit) (t : Fin c.gates.length) : Finset (Fin (c.work+1)) :=
  Finset.univ.filter (fun i => qmaFirstUse c i = t.val)

theorem qmaFirstUseSites_subset (c : QMACircuit) (t : Fin c.gates.length) :
    qmaFirstUseSites c t ⊆ qmaGateSites c.work c.gates[t.val] := by
  intro i hi
  have he := (Finset.mem_filter.mp hi).2
  have ht : qmaFirstUse c i < c.gates.length := he.symm ▸ t.isLt
  have hh := List.findIdx_getElem (p := fun g => decide (i ∈ qmaGateSites c.work g))
    (xs := c.gates) (w := ht)
  change decide (i ∈ qmaGateSites c.work c.gates[qmaFirstUse c i]) = true at hh
  simpa only [he,decide_eq_true_eq] using hh

theorem qmaFirstUseSites_card (c : QMACircuit) (t : Fin c.gates.length) :
    (qmaFirstUseSites c t).card ≤ 2 :=
  (Finset.card_le_card (qmaFirstUseSites_subset c t)).trans (qmaGateSites_card _ _)

theorem qmaFirstUse_lt_of_touched (c : QMACircuit) (i : Fin (c.work+1))
    (h : ∃ g ∈ c.gates, i ∈ qmaGateSites c.work g) : qmaFirstUse c i < c.gates.length := by
  apply List.findIdx_lt_length_of_exists
  simpa only [decide_eq_true_eq] using h

theorem qmaSweepFirstUse_lt (c : QMACircuit) (hne : c.gates ≠ [])
    (i : Fin ((qmaSweepCircuit c).work+1)) :
    qmaFirstUse (qmaSweepCircuit c) i < (qmaSweepCircuit c).gates.length :=
  qmaFirstUse_lt_of_touched _ _ (qmaSweepCircuit_touches c hne i)

theorem qmaList_filter_index_card {α : Type*} (xs : List α) (p : α → Bool) :
    (Finset.univ.filter (fun i : Fin xs.length => p xs[i.val])).card = (xs.filter p).length := by
  rw [Finset.card_filter]
  induction xs with
  | nil => simp
  | cons a xs ih =>
    change (∑ i : Fin (xs.length+1), if p (a::xs)[i.val] = true then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    change (if p a = true then 1 else 0)+
      (∑ i : Fin xs.length, if p xs[i.val] = true then 1 else 0) = _
    rw [ih]
    by_cases ha : p a = true
    · simp [ha,Nat.add_comm]
    · have hf : p a = false := Bool.eq_false_iff.mpr ha
      simp [hf]

end ContinuumCoulomb

end

end OAI

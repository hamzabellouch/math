import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedReference

namespace OAI

/-! At most eight actual interaction terms are assigned to any clock time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaSumFilter_card {α β : Type*} [Fintype α] [Fintype β]
    (p : α ⊕ β → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      (Finset.univ.filter (fun a => p (.inl a))).card+
      (Finset.univ.filter (fun b => p (.inr b))).card := by
  simp only [Finset.card_filter,Fintype.sum_sum_type]

theorem qmaBoundedClockTime_fiber_card (T : ℕ) (hT : 0 < T) (t : Fin T) :
    (Finset.univ.filter (fun i : Fin (T+1) => qmaBoundedClockTime T hT i.val = t)).card ≤ 2 := by
  have hs : Finset.univ.filter (fun i : Fin (T+1) => qmaBoundedClockTime T hT i.val = t) ⊆
      {t.castSucc,Fin.last T} := by
    intro i hi
    have hv := congrArg Fin.val (Finset.mem_filter.mp hi).2
    change min i.val (T-1) = t.val at hv
    have hit := i.isLt
    have htt := t.isLt
    have he : i.val = t.val ∨ i.val = T := by omega
    simpa only [Finset.mem_insert,Finset.mem_singleton] using
      he.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  have hp := Finset.card_insert_le t.castSucc {Fin.last T}
  rw [Finset.card_singleton] at hp
  exact (Finset.card_le_card hs).trans hp

theorem qmaHistoryTimeFiber_card (c : QMACircuit) (hT : 0 < c.gates.length)
    (hi : ∀ i, qmaFirstUse c i < c.gates.length) (t : Fin c.gates.length) :
    (Finset.univ.filter (fun a : QMACircuitTerm c =>
      qmaHistoryTermTime c hT (qmaFirstUseTime c) a = t)).card ≤ 8 := by
  have hclock := qmaBoundedClockTime_fiber_card c.gates.length hT t
  have hboundary : (Finset.univ.filter (fun b : Fin 2 =>
      (if b = 0 then (⟨0,hT⟩ : Fin c.gates.length)
      else qmaBoundedClockTime _ hT c.gates.length) = t)).card ≤ 2 := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hinput : (Finset.univ.filter (fun i : Fin (c.work+1) =>
      qmaBoundedClockTime _ hT (qmaFirstUse c i) = t)).card ≤ 2 := by
    apply le_trans (Finset.card_le_card (show _ ⊆ qmaFirstUseSites c t from ?_))
      (qmaFirstUseSites_card c t)
    intro i hm
    have hv := congrArg Fin.val (Finset.mem_filter.mp hm).2
    change min (qmaFirstUse c i) (c.gates.length-1) = t.val at hv
    simp only [qmaFirstUseSites,Finset.mem_filter,Finset.mem_univ,true_and]
    have := hi i
    omega
  have houtput : (Finset.univ.filter (fun _ : Unit =>
      qmaBoundedClockTime _ hT c.gates.length = t)).card ≤ 1 := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hprop : (Finset.univ.filter (fun u : Fin c.gates.length => u = t)).card ≤ 1 := by
    have hs : (Finset.univ.filter (fun u : Fin c.gates.length => u = t)) ⊆
        ({t} : Finset (Fin c.gates.length)) := by
      intro u hu
      simpa only [Finset.mem_singleton] using (Finset.mem_filter.mp hu).2
    exact (Finset.card_le_card hs).trans (by simp)
  change (Finset.univ.filter (fun a :
    Fin (c.gates.length+1) ⊕ (Fin 2 ⊕ (Fin (c.work+1) ⊕ (Unit ⊕ Fin c.gates.length))) =>
    qmaHistoryTermTime c hT (qmaFirstUseTime c) a = t)).card ≤ 8
  rw [qmaSumFilter_card,qmaSumFilter_card,qmaSumFilter_card,qmaSumFilter_card]
  simp only [qmaHistoryTermTime]
  exact (Nat.add_le_add hclock (Nat.add_le_add hboundary
    (Nat.add_le_add hinput (Nat.add_le_add houtput hprop)))).trans (by decide)

end ContinuumCoulomb

end

end OAI

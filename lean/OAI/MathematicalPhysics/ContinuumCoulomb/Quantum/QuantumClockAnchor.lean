import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumClockPath
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSparseFirstUse

namespace OAI

/-! The two endpoint clock bits and each internal clock bit have a local time anchor. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaClockAnchorIndex (T : ℕ) (hT : 0 < T) (b : Fin (T+2)) : Fin T :=
  ⟨min (b.val-1) (T-1),by omega⟩

theorem qmaClockAnchorIndex_near (T : ℕ) (hT : 0 < T) (t : Fin T) (b : Fin (T+2))
    (hb : t.val ≤ b.val ∧ b.val ≤ t.val+2) :
    (qmaClockAnchorIndex T hT b).val ≤ t.val+1 ∧ t.val ≤ (qmaClockAnchorIndex T hT b).val+1 := by
  change min (b.val-1) (T-1) ≤ t.val+1 ∧ t.val ≤ min (b.val-1) (T-1)+1
  have ht := t.isLt
  omega

theorem qmaClockAnchorIndex_middle (T : ℕ) (hT : 0 < T) (t : Fin T) :
    qmaClockAnchorIndex T hT (qmaClockMiddle T t) = t := by
  apply Fin.ext
  change min (t.val+1-1) (T-1) = t.val
  have ht := t.isLt
  omega

theorem qmaClockAnchorIndex_fiber (T : ℕ) (hT : 0 < T) (t : Fin T) (b : Fin (T+2))
    (hb : qmaClockAnchorIndex T hT b = t) :
    b = 0 ∨ b = qmaClockMiddle T t ∨ b = Fin.last (T+1) := by
  have hv := congrArg Fin.val hb
  change min (b.val-1) (T-1) = t.val at hv
  have ht := t.isLt
  have hb' := b.isLt
  have h : b.val = 0 ∨ b.val = t.val+1 ∨ b.val = T+1 := by omega
  exact h.imp (fun h => Fin.ext h) (fun h => h.imp (fun h => Fin.ext h) (fun h => Fin.ext h))

theorem qmaClockAnchorIndex_fiber_card (T : ℕ) (hT : 0 < T) (t : Fin T) :
    (Finset.univ.filter (fun b : Fin (T+2) => qmaClockAnchorIndex T hT b = t)).card ≤ 3 := by
  have hs : Finset.univ.filter (fun b : Fin (T+2) => qmaClockAnchorIndex T hT b = t) ⊆
      {0,qmaClockMiddle T t,Fin.last (T+1)} := by
    intro b hb
    simpa only [Finset.mem_insert,Finset.mem_singleton] using
      qmaClockAnchorIndex_fiber T hT t b (Finset.mem_filter.mp hb).2
  apply (Finset.card_le_card hs).trans
  have h1 := Finset.card_insert_le (0 : Fin (T+2)) {qmaClockMiddle T t,Fin.last (T+1)}
  have h2 := Finset.card_insert_le (qmaClockMiddle T t) {Fin.last (T+1)}
  simp only [Finset.card_singleton] at h2
  omega

theorem qmaGridTagNear_refl {rows width : ℕ} (p : QMAGate × QMAGridCell rows width) :
    QMAGridTagNear p p := by
  unfold QMAGridTagNear
  omega

theorem qmaGridTagNear_symm {rows width : ℕ} {p q : QMAGate × QMAGridCell rows width}
    (h : QMAGridTagNear p q) : QMAGridTagNear q p := ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

theorem qmaGridTagChain_near {rows width : ℕ} (ps : List (QMAGate × QMAGridCell rows width))
    (hp : ps.IsChain QMAGridTagNear) (i j : Fin ps.length)
    (hij : i.val ≤ j.val+1) (hji : j.val ≤ i.val+1) :
    QMAGridTagNear ps[i.val] ps[j.val] := by
  have h : i.val = j.val ∨ i.val+1 = j.val ∨ j.val+1 = i.val := by omega
  rcases h with h | h | h
  · have he : i = j := Fin.ext h
    subst j
    exact qmaGridTagNear_refl _
  · have hh := (List.isChain_iff_getElem.mp hp) i.val (by omega)
    simpa only [h] using hh
  · apply qmaGridTagNear_symm
    have hh := (List.isChain_iff_getElem.mp hp) j.val (by omega)
    simpa only [h] using hh

end ContinuumCoulomb

end

end OAI

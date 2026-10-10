import OAI.Probability.SwitchChain.DisjointEncoding
import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

private theorem pair_count {n : Nat} (G : SimpleGraph (Fin n))
    (u v w : Fin n) (huv : u ≠ v) :
    (({u, v} : Finset (Fin n)).filter (G.Adj w)).card = edgeBit G u w + edgeBit G v w := by
  rw [Finset.card_filter, Finset.sum_pair huv]
  simp [edgeBit, SimpleGraph.adj_comm]

private theorem outside_pair {n : Nat} (e : Fin 4 ↪ Fin n) (w : Fin n)
    (hw : Outside e w) (a b : Fin 4) : w ∉ ({e a, e b} : Finset (Fin n)) := by
  simp [hw a, hw b]

theorem sameCell_of_leftFiber {n : Nat} (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 0, e 1} G H) : SameCell e G H := by
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h20 : e 2 ≠ e 0 := e.injective.ne (by decide)
  have h21 : e 2 ≠ e 1 := e.injective.ne (by decide)
  have h30 : e 3 ≠ e 0 := e.injective.ne (by decide)
  have h31 : e 3 ≠ e 1 := e.injective.ne (by decide)
  have h2 : e 2 ∉ ({e 0, e 1} : Finset (Fin n)) := by simp [h20, h21]
  have h3 : e 3 ∉ ({e 0, e 1} : Finset (Fin n)) := by simp [h30, h31]
  constructor
  · intro u v hu hv
    exact h.1 u (outside_pair e u hu 0 1) v (outside_pair e v hv 0 1)
  · exact h.2.1 (e 0) (by simp) (e 1) (by simp)
  · exact h.1 (e 2) h2 (e 3) h3
  · intro w hw
    have hc := h.2.2 w (outside_pair e w hw 0 1)
    simpa only [pair_count G (e 0) (e 1) w h01, pair_count H (e 0) (e 1) w h01] using hc
  · intro w hw
    have h2w := h.1 (e 2) h2 w (outside_pair e w hw 0 1)
    have h3w := h.1 (e 3) h3 w (outside_pair e w hw 0 1)
    rw [(edgeBit_eq_iff G H (e 2) w).mpr h2w, (edgeBit_eq_iff G H (e 3) w).mpr h3w]

theorem sameCell_of_rightFiber {n : Nat} (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 2, e 3} G H) : SameCell e G H := by
  have h23 : e 2 ≠ e 3 := e.injective.ne (by decide)
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have h03 : e 0 ≠ e 3 := e.injective.ne (by decide)
  have h12 : e 1 ≠ e 2 := e.injective.ne (by decide)
  have h13 : e 1 ≠ e 3 := e.injective.ne (by decide)
  have h0 : e 0 ∉ ({e 2, e 3} : Finset (Fin n)) := by simp [h02, h03]
  have h1 : e 1 ∉ ({e 2, e 3} : Finset (Fin n)) := by simp [h12, h13]
  constructor
  · intro u v hu hv
    exact h.1 u (outside_pair e u hu 2 3) v (outside_pair e v hv 2 3)
  · exact h.1 (e 0) h0 (e 1) h1
  · exact h.2.1 (e 2) (by simp) (e 3) (by simp)
  · intro w hw
    have h0w := h.1 (e 0) h0 w (outside_pair e w hw 2 3)
    have h1w := h.1 (e 1) h1 w (outside_pair e w hw 2 3)
    rw [(edgeBit_eq_iff G H (e 0) w).mpr h0w, (edgeBit_eq_iff G H (e 1) w).mpr h1w]
  · intro w hw
    have hc := h.2.2 w (outside_pair e w hw 2 3)
    simpa only [pair_count G (e 2) (e 3) w h23, pair_count H (e 2) (e 3) w h23] using hc

end Problem315.DisjointEncoding

end

end OAI

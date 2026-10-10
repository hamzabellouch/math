import OAI.Probability.SwitchChain.DisjointEncoding
import OAI.Probability.SwitchChain.PairProjectionCell

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.DisjointEncoding

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

private theorem pair_count_eq (G : SimpleGraph (Fin n)) (i j w : Fin n)
    (hij : i ≠ j) :
    (({i, j} : Finset (Fin n)).filter (G.Adj w)).card =
      edgeBit G i w + edgeBit G j w := by
  by_cases hi : G.Adj i w <;> by_cases hj : G.Adj j w <;>
    simp [edgeBit, Finset.filter_insert, Finset.filter_singleton,
      G.adj_comm w i, G.adj_comm w j, hi, hj, hij]

theorem sameCell_of_sameFiber_left (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 0, e 1} G H) : SameCell e G H := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b := fun h => hab (e.injective h)
  have hout (w : Fin n) (hw : Outside e w) : w ∉ ({e 0, e 1} : Finset (Fin n)) := by
    simp [hw 0, hw 1]
  have h2 : e 2 ∉ ({e 0, e 1} : Finset (Fin n)) := by
    simp [he 2 0 (by decide), he 2 1 (by decide)]
  have h3 : e 3 ∉ ({e 0, e 1} : Finset (Fin n)) := by
    simp [he 3 0 (by decide), he 3 1 (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun u v hu hv => h.1 u (hout u hu) v (hout v hv)
  · exact h.2.1 (e 0) (by simp) (e 1) (by simp)
  · exact h.1 (e 2) h2 (e 3) h3
  · intro w hw
    have hc := h.2.2 w (hout w hw)
    simpa only [pair_count_eq G _ _ _ (he 0 1 (by decide)),
      pair_count_eq H _ _ _ (he 0 1 (by decide))] using hc
  · intro w hw
    rw [(edgeBit_eq_iff G H (e 2) w).mpr (h.1 (e 2) h2 w (hout w hw)),
      (edgeBit_eq_iff G H (e 3) w).mpr (h.1 (e 3) h3 w (hout w hw))]

theorem sameCell_of_sameFiber_right (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 2, e 3} G H) : SameCell e G H := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b := fun h => hab (e.injective h)
  have hout (w : Fin n) (hw : Outside e w) : w ∉ ({e 2, e 3} : Finset (Fin n)) := by
    simp [hw 2, hw 3]
  have h0 : e 0 ∉ ({e 2, e 3} : Finset (Fin n)) := by
    simp [he 0 2 (by decide), he 0 3 (by decide)]
  have h1 : e 1 ∉ ({e 2, e 3} : Finset (Fin n)) := by
    simp [he 1 2 (by decide), he 1 3 (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun u v hu hv => h.1 u (hout u hu) v (hout v hv)
  · exact h.1 (e 0) h0 (e 1) h1
  · exact h.2.1 (e 2) (by simp) (e 3) (by simp)
  · intro w hw
    rw [(edgeBit_eq_iff G H (e 0) w).mpr (h.1 (e 0) h0 w (hout w hw)),
      (edgeBit_eq_iff G H (e 1) w).mpr (h.1 (e 1) h1 w (hout w hw))]
  · intro w hw
    have hc := h.2.2 w (hout w hw)
    simpa only [pair_count_eq G _ _ _ (he 2 3 (by decide)),
      pair_count_eq H _ _ _ (he 2 3 (by decide))] using hc

def stateCellSetoid (e : Fin 4 ↪ Fin n) : Setoid (GraphState n d) where
  r G H := SameCell e G.val H.val
  iseqv := ⟨fun G => SameCell.refl e G.val,
    fun h => h.symm, fun h h' => h.trans h'⟩

abbrev CellIndex (e : Fin 4 ↪ Fin n) (d : Fin n → ℕ) := Quotient (stateCellSetoid (d := d) e)

noncomputable instance (e : Fin 4 ↪ Fin n) : Fintype (CellIndex e d) := Fintype.ofFinite _

def cellIndex (e : Fin 4 ↪ Fin n) (G : GraphState n d) : CellIndex e d := Quotient.mk _ G

@[simp] theorem cellIndex_eq_iff (e : Fin 4 ↪ Fin n) (G H : GraphState n d) :
    cellIndex e G = cellIndex e H ↔ SameCell e G.val H.val :=
  Quotient.eq

theorem cellInvariant_left (e : Fin 4 ↪ Fin n) (c : CellIndex e d) :
    PairResampling.CellInvariant {e 0, e 1} (fun G => cellIndex e G = c) := by
  intro G H h
  have heq := (cellIndex_eq_iff e G H).mpr (sameCell_of_sameFiber_left e G.val H.val h)
  change cellIndex e G = c ↔ cellIndex e H = c
  rw [heq]

theorem cellInvariant_right (e : Fin 4 ↪ Fin n) (c : CellIndex e d) :
    PairResampling.CellInvariant {e 2, e 3} (fun G => cellIndex e G = c) := by
  intro G H h
  have heq := (cellIndex_eq_iff e G H).mpr (sameCell_of_sameFiber_right e G.val H.val h)
  change cellIndex e G = c ↔ cellIndex e H = c
  rw [heq]

theorem interaction_eq_sum_cells (e : Fin 4 ↪ Fin n) (f : PairResampling.StateSpace n d) :
    ⟪PairResampling.fluctuation n d {e 0, e 1} f,
      PairResampling.fluctuation n d {e 2, e 3} f⟫ =
    ∑ c : CellIndex e d,
      ⟪PairResampling.fluctuation n d {e 0, e 1}
          (PairResampling.restrictCell (fun G => cellIndex e G = c) f),
        PairResampling.fluctuation n d {e 2, e 3}
          (PairResampling.restrictCell (fun G => cellIndex e G = c) f)⟫ :=
  PairResampling.fluctuation_interaction_eq_sum_cells (cellIndex e) _ _
    (cellInvariant_left e) (cellInvariant_right e) f

theorem interaction_bound_of_cell_bounds (e : Fin 4 ↪ Fin n)
    (g r s : PairResampling.StateSpace n d → PairResampling.StateSpace n d)
    (f : PairResampling.StateSpace n d)
    (hg : ∀ c : CellIndex e d,
      g (PairResampling.restrictCell (fun G => cellIndex e G = c) f) =
        PairResampling.restrictCell (fun G => cellIndex e G = c) (g f))
    (hr : ∀ c : CellIndex e d,
      r (PairResampling.restrictCell (fun G => cellIndex e G = c) f) =
        PairResampling.restrictCell (fun G => cellIndex e G = c) (r f))
    (hs : ∀ c : CellIndex e d,
      s (PairResampling.restrictCell (fun G => cellIndex e G = c) f) =
        PairResampling.restrictCell (fun G => cellIndex e G = c) (s f))
    (hlocal : ∀ c : CellIndex e d,
      let fc := PairResampling.restrictCell (fun G => cellIndex e G = c) f
      2 * ‖g fc‖ ^ 2 - ‖r fc‖ ^ 2 - ‖s fc‖ ^ 2 ≤
        2 * ⟪PairResampling.fluctuation n d {e 0, e 1} fc,
          PairResampling.fluctuation n d {e 2, e 3} fc⟫) :
    2 * ‖g f‖ ^ 2 - ‖r f‖ ^ 2 - ‖s f‖ ^ 2 ≤
      2 * ⟪PairResampling.fluctuation n d {e 0, e 1} f,
        PairResampling.fluctuation n d {e 2, e 3} f⟫ := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hlocal c)
  simp_rw [hg, hr, hs] at hsum
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← PairResampling.norm_sq_eq_sum_cell_norm_sq,
    ← interaction_eq_sum_cells] at hsum
  exact hsum

end Problem315.DisjointEncoding

end

end OAI

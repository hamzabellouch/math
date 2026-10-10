import OAI.Probability.SwitchChain.DisjointRealization
import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

variable {V : Type*} [Fintype V]

theorem rightAssignment_eq_iff_first_edges
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K) :
    rightAssignment e G H = rightAssignment e G K ↔
      ∀ w, Outside e w → (H.Adj (e 2) w ↔ K.Adj (e 2) w) := by
  constructor
  · intro h w hw
    apply first_edge_iff_of_counts G H K (e 2) (e 3) w
      (hH.rightCount w hw) (hK.rightCount w hw)
    intro hs
    have he := Finset.ext_iff.mp h ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (rightCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
  · intro h
    ext w
    simp only [rightAssignment, Finset.mem_filter]
    rw [h w.val w.property]

theorem leftAssignment_eq_iff_first_edges
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K) :
    leftAssignment e G H = leftAssignment e G K ↔
      ∀ w, Outside e w → (H.Adj (e 0) w ↔ K.Adj (e 0) w) := by
  constructor
  · intro h w hw
    apply first_edge_iff_of_counts G H K (e 0) (e 1) w
      (hH.leftCount w hw) (hK.leftCount w hw)
    intro hs
    have he := Finset.ext_iff.mp h ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (leftCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
  · intro h
    ext w
    simp only [leftAssignment, Finset.mem_filter]
    rw [h w.val w.property]

theorem right_boundary_eq_of_assignment_eq
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K)
    (h : rightAssignment e G H = rightAssignment e G K)
    (w : V) (hw : Outside e w) :
    (H.Adj (e 2) w ↔ K.Adj (e 2) w) ∧
      (H.Adj (e 3) w ↔ K.Adj (e 3) w) := by
  have hfirst := (rightAssignment_eq_iff_first_edges e G H K hH hK).mp h w hw
  refine ⟨hfirst, ?_⟩
  apply (edgeBit_eq_iff H K (e 3) w).mp
  have hbit := (edgeBit_eq_iff H K (e 2) w).mpr hfirst
  have hHcount := hH.rightCount w hw
  have hKcount := hK.rightCount w hw
  omega

theorem left_boundary_eq_of_assignment_eq
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K)
    (h : leftAssignment e G H = leftAssignment e G K)
    (w : V) (hw : Outside e w) :
    (H.Adj (e 0) w ↔ K.Adj (e 0) w) ∧
      (H.Adj (e 1) w ↔ K.Adj (e 1) w) := by
  have hfirst := (leftAssignment_eq_iff_first_edges e G H K hH hK).mp h w hw
  refine ⟨hfirst, ?_⟩
  apply (edgeBit_eq_iff H K (e 1) w).mp
  have hbit := (edgeBit_eq_iff H K (e 0) w).mpr hfirst
  have hHcount := hH.leftCount w hw
  have hKcount := hK.leftCount w hw
  omega

variable {n : Nat} {d : Fin n → Nat}

theorem sameFiber_left_iff_rightAssignment_eq
    (e : Fin 4 ↪ Fin n) (G H K : GraphState n d)
    (hH : SameCell e G.val H.val) (hK : SameCell e G.val K.val) :
    PairResampling.SameFiber {e 0, e 1} H.val K.val ↔
      rightAssignment e G.val H.val = rightAssignment e G.val K.val := by
  have he (a b : Fin 4) (h : a ≠ b) : e a ≠ e b := fun heq => h (e.injective heq)
  constructor
  · intro h
    apply (rightAssignment_eq_iff_first_edges e G.val H.val K.val hH hK).mpr
    intro w hw
    exact h.1 (e 2) (by simp [he 2 0 (by decide), he 2 1 (by decide)])
      w (by simp [hw 0, hw 1])
  · intro h
    apply (PairResampling.sameFiber_state_iff {e 0,e 1} H K).mpr
    have hc := hH.symm.trans hK
    have hb := right_boundary_eq_of_assignment_eq e G.val H.val K.val hH hK h
    constructor
    · intro u hu v hv
      obtain ⟨u, rfl⟩ := (blockEquiv e).surjective u
      obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
      cases u with
      | inl a =>
        fin_cases a
        · simp at hu
        · simp at hu
        · cases v with
          | inl b =>
            fin_cases b
            · simp at hv
            · simp at hv
            · simp
            · exact hc.rightInternal
          | inr w => exact (hb w.val w.property).1
        · cases v with
          | inl b =>
            fin_cases b
            · simp at hv
            · simp at hv
            · exact (H.val.adj_comm _ _).trans (hc.rightInternal.trans (K.val.adj_comm _ _))
            · simp
          | inr w => exact (hb w.val w.property).2
      | inr u =>
        cases v with
        | inl b =>
          fin_cases b
          · simp at hv
          · simp at hv
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).1.trans (K.val.adj_comm _ _))
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).2.trans (K.val.adj_comm _ _))
        | inr v => exact hc.outer u.val v.val u.property v.property
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · simp
      · exact hc.leftInternal
      · exact (H.val.adj_comm _ _).trans (hc.leftInternal.trans (K.val.adj_comm _ _))
      · simp

theorem sameFiber_right_iff_leftAssignment_eq
    (e : Fin 4 ↪ Fin n) (G H K : GraphState n d)
    (hH : SameCell e G.val H.val) (hK : SameCell e G.val K.val) :
    PairResampling.SameFiber {e 2, e 3} H.val K.val ↔
      leftAssignment e G.val H.val = leftAssignment e G.val K.val := by
  have he (a b : Fin 4) (h : a ≠ b) : e a ≠ e b := fun heq => h (e.injective heq)
  constructor
  · intro h
    apply (leftAssignment_eq_iff_first_edges e G.val H.val K.val hH hK).mpr
    intro w hw
    exact h.1 (e 0) (by simp [he 0 2 (by decide), he 0 3 (by decide)])
      w (by simp [hw 2, hw 3])
  · intro h
    apply (PairResampling.sameFiber_state_iff {e 2,e 3} H K).mpr
    have hc := hH.symm.trans hK
    have hb := left_boundary_eq_of_assignment_eq e G.val H.val K.val hH hK h
    constructor
    · intro u hu v hv
      obtain ⟨u, rfl⟩ := (blockEquiv e).surjective u
      obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
      cases u with
      | inl a =>
        fin_cases a
        · cases v with
          | inl b =>
            fin_cases b
            · simp
            · exact hc.leftInternal
            · simp at hv
            · simp at hv
          | inr w => exact (hb w.val w.property).1
        · cases v with
          | inl b =>
            fin_cases b
            · exact (H.val.adj_comm _ _).trans (hc.leftInternal.trans (K.val.adj_comm _ _))
            · simp
            · simp at hv
            · simp at hv
          | inr w => exact (hb w.val w.property).2
        · simp at hu
        · simp at hu
      | inr u =>
        cases v with
        | inl b =>
          fin_cases b
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).1.trans (K.val.adj_comm _ _))
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).2.trans (K.val.adj_comm _ _))
          · simp at hv
          · simp at hv
        | inr v => exact hc.outer u.val v.val u.property v.property
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · simp
      · exact hc.rightInternal
      · exact (H.val.adj_comm _ _).trans (hc.rightInternal.trans (K.val.adj_comm _ _))
      · simp

end Problem315.DisjointEncoding

end

end OAI

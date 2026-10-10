import Mathlib

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

variable {V : Type*}

def edgeBit (G : SimpleGraph V) (u v : V) : Nat := if G.Adj u v then 1 else 0

@[simp] theorem edgeBit_eq_iff (G H : SimpleGraph V) (u v : V) :
    edgeBit G u v = edgeBit H u v ↔ (G.Adj u v ↔ H.Adj u v) := by
  by_cases hG : G.Adj u v <;> by_cases hH : H.Adj u v <;> simp [edgeBit, hG, hH]

def Outside (e : Fin 4 ↪ V) (w : V) : Prop := ∀ a, w ≠ e a

structure SameCell (e : Fin 4 ↪ V) (G H : SimpleGraph V) : Prop where
  outer : ∀ u v, Outside e u → Outside e v → (G.Adj u v ↔ H.Adj u v)
  leftInternal : G.Adj (e 0) (e 1) ↔ H.Adj (e 0) (e 1)
  rightInternal : G.Adj (e 2) (e 3) ↔ H.Adj (e 2) (e 3)
  leftCount : ∀ w, Outside e w →
    edgeBit G (e 0) w + edgeBit G (e 1) w =
      edgeBit H (e 0) w + edgeBit H (e 1) w
  rightCount : ∀ w, Outside e w →
    edgeBit G (e 2) w + edgeBit G (e 3) w =
      edgeBit H (e 2) w + edgeBit H (e 3) w

structure SameCoordinates (e : Fin 4 ↪ V) (G H : SimpleGraph V) : Prop where
  cross02 : G.Adj (e 0) (e 2) ↔ H.Adj (e 0) (e 2)
  cross03 : G.Adj (e 0) (e 3) ↔ H.Adj (e 0) (e 3)
  cross12 : G.Adj (e 1) (e 2) ↔ H.Adj (e 1) (e 2)
  cross13 : G.Adj (e 1) (e 3) ↔ H.Adj (e 1) (e 3)
  leftChoice : ∀ w, Outside e w → (G.Adj (e 0) w ↔ H.Adj (e 0) w)
  rightChoice : ∀ w, Outside e w → (G.Adj (e 2) w ↔ H.Adj (e 2) w)

theorem block_to_outside (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) (he : SameCoordinates e G H)
    (a : Fin 4) (w : V) (hw : Outside e w) :
    G.Adj (e a) w ↔ H.Adj (e a) w := by
  fin_cases a
  · exact he.leftChoice w hw
  · change G.Adj (e 1) w ↔ H.Adj (e 1) w
    apply (edgeBit_eq_iff G H _ _).mp
    have hfirst := (edgeBit_eq_iff G H (e 0) w).mpr (he.leftChoice w hw)
    have hsum := hc.leftCount w hw
    omega
  · exact he.rightChoice w hw
  · change G.Adj (e 3) w ↔ H.Adj (e 3) w
    apply (edgeBit_eq_iff G H _ _).mp
    have hfirst := (edgeBit_eq_iff G H (e 2) w).mpr (he.rightChoice w hw)
    have hsum := hc.rightCount w hw
    omega

theorem block_to_block (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) (he : SameCoordinates e G H) (a b : Fin 4) :
    G.Adj (e a) (e b) ↔ H.Adj (e a) (e b) := by
  have h01 := hc.leftInternal
  have h23 := hc.rightInternal
  have h02 := he.cross02
  have h03 := he.cross03
  have h12 := he.cross12
  have h13 := he.cross13
  fin_cases a <;> fin_cases b
  · simp
  · exact h01
  · exact h02
  · exact h03
  · exact (G.adj_comm _ _).trans (h01.trans (H.adj_comm _ _))
  · simp
  · exact h12
  · exact h13
  · exact (G.adj_comm _ _).trans (h02.trans (H.adj_comm _ _))
  · exact (G.adj_comm _ _).trans (h12.trans (H.adj_comm _ _))
  · simp
  · exact h23
  · exact (G.adj_comm _ _).trans (h03.trans (H.adj_comm _ _))
  · exact (G.adj_comm _ _).trans (h13.trans (H.adj_comm _ _))
  · exact (G.adj_comm _ _).trans (h23.trans (H.adj_comm _ _))
  · simp

theorem graph_eq_of_cell_coordinates (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) (he : SameCoordinates e G H) : G = H := by
  ext u v
  by_cases hu : ∃ a, u = e a
  · obtain ⟨a, rfl⟩ := hu
    by_cases hv : ∃ b, v = e b
    · obtain ⟨b, rfl⟩ := hv
      exact block_to_block e G H hc he a b
    · exact block_to_outside e G H hc he a v (by simpa [Outside] using hv)
  · have hu' : Outside e u := by simpa [Outside] using hu
    by_cases hv : ∃ b, v = e b
    · obtain ⟨b, rfl⟩ := hv
      simpa only [SimpleGraph.adj_comm] using block_to_outside e G H hc he b u hu'
    · exact hc.outer u v hu' (by simpa [Outside] using hv)

theorem SameCell.refl (e : Fin 4 ↪ V) (G : SimpleGraph V) : SameCell e G G := by
  constructor <;> intros <;> rfl

theorem SameCell.symm {e : Fin 4 ↪ V} {G H : SimpleGraph V}
    (h : SameCell e G H) : SameCell e H G := by
  exact ⟨fun u v hu hv => (h.outer u v hu hv).symm,
    h.leftInternal.symm, h.rightInternal.symm,
    fun w hw => (h.leftCount w hw).symm, fun w hw => (h.rightCount w hw).symm⟩

theorem SameCell.trans {e : Fin 4 ↪ V} {G H K : SimpleGraph V}
    (h : SameCell e G H) (h' : SameCell e H K) : SameCell e G K := by
  exact ⟨fun u v hu hv => (h.outer u v hu hv).trans (h'.outer u v hu hv),
    h.leftInternal.trans h'.leftInternal, h.rightInternal.trans h'.rightInternal,
    fun w hw => (h.leftCount w hw).trans (h'.leftCount w hw),
    fun w hw => (h.rightCount w hw).trans (h'.rightCount w hw)⟩

def leftIndex (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩

def rightIndex (i : Fin 2) : Fin 4 := ⟨i.val + 2, by omega⟩

def encode (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    (Fin 2 → Fin 2 → Bool) × Set V × Set V :=
  (fun i j => decide (G.Adj (e (leftIndex i)) (e (rightIndex j))),
    {w | Outside e w ∧ G.Adj (e 0) w}, {w | Outside e w ∧ G.Adj (e 2) w})

theorem sameCoordinates_of_encode_eq (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (h : encode e G = encode e H) : SameCoordinates e G H := by
  constructor
  · have h' := congrArg (fun z => z.1 0 0) h
    simpa [encode, leftIndex, rightIndex] using h'
  · have h' := congrArg (fun z => z.1 0 1) h
    simpa [encode, leftIndex, rightIndex] using h'
  · have h' := congrArg (fun z => z.1 1 0) h
    simpa [encode, leftIndex, rightIndex] using h'
  · have h' := congrArg (fun z => z.1 1 1) h
    simpa [encode, leftIndex, rightIndex] using h'
  · intro w hw
    have h' := Set.ext_iff.mp (congrArg (fun z => z.2.1) h) w
    simpa [encode, hw] using h'
  · intro w hw
    have h' := Set.ext_iff.mp (congrArg (fun z => z.2.2) h) w
    simpa [encode, hw] using h'

theorem encode_eq_iff (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) : encode e G = encode e H ↔ G = H := by
  constructor
  · intro h
    exact graph_eq_of_cell_coordinates e G H hc (sameCoordinates_of_encode_eq e G H h)
  · intro h
    exact congrArg (encode e) h

theorem encode_cell_injective (e : Fin 4 ↪ V) (G₀ : SimpleGraph V) :
    Function.Injective (fun G : {G : SimpleGraph V // SameCell e G₀ G} => encode e G.val) := by
  intro G H h
  apply Subtype.ext
  exact (encode_eq_iff e G.val H.val (G.property.symm.trans H.property)).mp h

end Problem315.DisjointEncoding

end

end OAI

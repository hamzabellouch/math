import OAI.Probability.SwitchChain.DisjointStateLaw
import OAI.Probability.SwitchChain.CrossCellMoments
import OAI.Probability.SwitchChain.PairFibers

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.DisjointMarginal
attribute [local instance] Classical.propDecidable
open DisjointEncoding

variable {V : Type*} [Fintype V]

def jointCrossEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    JointData e G ≃ CrossCellMoments.Cell (CrossBlock.total (crossCode e G))
      (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) where
  toFun z := ⟨(z.2.2.val, z.1, z.2.1), z.2.2.property⟩
  invFun z := ⟨z.val.2.1, z.val.2.2, z.val.1, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def degreeCellCrossEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    DegreeCell e G ≃ CrossCellMoments.Cell (CrossBlock.total (crossCode e G))
      (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) :=
  (degreeCellJointEquiv e G).trans (jointCrossEquiv e G)

variable {n : Nat} {d : Fin n → Nat}

abbrev CrossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d) :=
  CrossCellMoments.Cell (CrossBlock.total (crossCode e G.val))
    (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1)

def stateCellCrossEquiv (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    StateCell e G ≃ CrossCell e G :=
  (stateCellJointEquiv e G).trans (jointCrossEquiv e G.val)

@[simp] theorem stateCellCrossEquiv_left (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellCrossEquiv e G H).val.2.1 = stateLeftData e G H := rfl

@[simp] theorem stateCellCrossEquiv_right (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellCrossEquiv e G H).val.2.2 = stateRightData e G H := rfl

@[simp] theorem stateCellCrossEquiv_matrix (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellCrossEquiv e G H).val.1 = crossCode e H.val.val := rfl

theorem sameFiber_left_iff_crossCell_right (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H K : StateCell e G) :
    PairResampling.SameFiber {e 0, e 1} H.val.val K.val.val ↔
      (stateCellCrossEquiv e G H).val.2.2 = (stateCellCrossEquiv e G K).val.2.2 :=
  sameFiber_left_iff_stateRightData_eq e G H K

theorem sameFiber_right_iff_crossCell_left (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H K : StateCell e G) :
    PairResampling.SameFiber {e 2, e 3} H.val.val K.val.val ↔
      (stateCellCrossEquiv e G H).val.2.1 = (stateCellCrossEquiv e G K).val.2.1 :=
  sameFiber_right_iff_stateLeftData_eq e G H K

end Problem315.DisjointMarginal

namespace Problem315.PairFibers
attribute [local instance] Classical.propDecidable

theorem expectation_ker_pullback {α β ι : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (key : β → ι) (f : EuclideanSpace ℝ β) (x : α) :
    expectation (Setoid.ker (key ∘ e)) (WithLp.toLp 2 (fun y => f (e y))) x =
      expectation (Setoid.ker key) f (e x) := by
  classical
  have hcell : (cell (Setoid.ker (key ∘ e)) x).map e.toEmbedding =
      cell (Setoid.ker key) (e x) := by
    ext y
    simp only [Finset.mem_map, mem_cell, Setoid.ker_def, Function.comp_apply,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨e.symm y, by simpa using hy, by simp⟩
  have hcard := congrArg Finset.card hcell
  rw [Finset.card_map] at hcard
  rw [expectation_apply, expectation_apply, hcard]
  congr 1
  rw [← hcell, Finset.sum_map]
  rfl

end Problem315.PairFibers

namespace Problem315.DisjointMarginal
attribute [local instance] Classical.propDecidable
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

theorem expectation_stateLeftData_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : EuclideanSpace ℝ (CrossCell e G)) (H : StateCell e G) :
    PairFibers.expectation (Setoid.ker (stateLeftData e G))
      (WithLp.toLp 2 (fun K => f (stateCellCrossEquiv e G K))) H =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
        f (stateCellCrossEquiv e G H) :=
by
  have h := PairFibers.expectation_ker_pullback (stateCellCrossEquiv e G)
    (fun z : CrossCell e G => z.val.2.1) f H
  simpa only [Function.comp_def, stateCellCrossEquiv_left] using h

theorem expectation_stateRightData_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : EuclideanSpace ℝ (CrossCell e G)) (H : StateCell e G) :
    PairFibers.expectation (Setoid.ker (stateRightData e G))
      (WithLp.toLp 2 (fun K => f (stateCellCrossEquiv e G K))) H =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
        f (stateCellCrossEquiv e G H) :=
by
  have h := PairFibers.expectation_ker_pullback (stateCellCrossEquiv e G)
    (fun z : CrossCell e G => z.val.2.2) f H
  simpa only [Function.comp_def, stateCellCrossEquiv_right] using h

end Problem315.DisjointMarginal

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable
variable {n : Nat} {d : Fin n → Nat}

theorem expectation_eq_subtype_key {ι : Type*}
    (a : Finset (Fin n)) (C : GraphState n d → Prop) (key : {G // C G} → ι)
    (hclosed : ∀ (H : {G // C G}) (K : GraphState n d),
      SameFiber a H.val.val K.val → C K)
    (hkey : ∀ H K : {G // C G}, SameFiber a H.val.val K.val.val ↔ key H = key K)
    (f : StateSpace n d) (H : {G // C G}) :
    expectation n d a f H.val =
      PairFibers.expectation (Setoid.ker key) (WithLp.toLp 2 (fun K => f K.val)) H := by
  classical
  let emb : {G // C G} ↪ GraphState n d := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (PairFibers.cell (Setoid.ker key) H).map emb = fiberStates a H.val := by
    ext K
    simp only [Finset.mem_map, PairFibers.mem_cell, Setoid.ker_def, mem_fiberStates]
    constructor
    · rintro ⟨L, hL, hLK⟩
      have hrel := (hkey H L).mpr hL
      change L.val = K at hLK
      simpa only [hLK] using hrel
    · intro hK
      refine ⟨⟨K, hclosed H K hK⟩, ?_, rfl⟩
      exact (hkey H ⟨K, hclosed H K hK⟩).mp hK
  rw [expectation_eq_average, PairFibers.expectation_apply, ← hmap,
    Finset.sum_map, Finset.card_map]
  rfl

end Problem315.PairResampling

namespace Problem315.DisjointMarginal
attribute [local instance] Classical.propDecidable
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

theorem expectation_leftPair_eq_stateRightData (e : Fin 4 ↪ Fin n)
    (G : GraphState n d) (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 0, e 1} f H.val =
      PairFibers.expectation (Setoid.ker (stateRightData e G))
        (WithLp.toLp 2 (fun K => f K.val)) H := by
  exact PairResampling.expectation_eq_subtype_key {e 0, e 1}
    (fun K => SameCell e G.val K.val) (stateRightData e G)
    (stateCell_of_leftFiber e G) (sameFiber_left_iff_stateRightData_eq e G) f H

theorem expectation_rightPair_eq_stateLeftData (e : Fin 4 ↪ Fin n)
    (G : GraphState n d) (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 2, e 3} f H.val =
      PairFibers.expectation (Setoid.ker (stateLeftData e G))
        (WithLp.toLp 2 (fun K => f K.val)) H := by
  exact PairResampling.expectation_eq_subtype_key {e 2, e 3}
    (fun K => SameCell e G.val K.val) (stateLeftData e G)
    (stateCell_of_rightFiber e G) (sameFiber_right_iff_stateLeftData_eq e G) f H

end Problem315.DisjointMarginal

end

end OAI

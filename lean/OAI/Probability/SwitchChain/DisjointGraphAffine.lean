import OAI.Probability.SwitchChain.DisjointCrossCellEquiv
import OAI.Probability.SwitchChain.DisjointEqualityFlags
import OAI.Probability.SwitchChain.CrossCellAffineComposition

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointMarginal
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

def crossCellRestriction (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) : EuclideanSpace ℝ (CrossCell e G) :=
  WithLp.toLp 2 (fun z => f ((stateCellCrossEquiv e G).symm z).val)

@[simp] theorem crossCellRestriction_apply_equiv
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    crossCellRestriction e G f (stateCellCrossEquiv e G H) = f H.val := by
  simp [crossCellRestriction]

theorem left_expectation_eq_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 0,e 1} f H.val =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
        (crossCellRestriction e G f) (stateCellCrossEquiv e G H) := by
  rw [expectation_leftPair_eq_stateRightData e G f H]
  have heq : (WithLp.toLp 2 (fun K : StateCell e G => f K.val)) =
      WithLp.toLp 2 (fun K => crossCellRestriction e G f (stateCellCrossEquiv e G K)) := by
    ext K
    change f K.val = crossCellRestriction e G f (stateCellCrossEquiv e G K)
    rw [crossCellRestriction_apply_equiv]
  rw [heq, expectation_stateRightData_crossCell]

theorem right_expectation_eq_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 2,e 3} f H.val =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
        (crossCellRestriction e G f) (stateCellCrossEquiv e G H) := by
  rw [expectation_rightPair_eq_stateLeftData e G f H]
  have heq : (WithLp.toLp 2 (fun K : StateCell e G => f K.val)) =
      WithLp.toLp 2 (fun K => crossCellRestriction e G f (stateCellCrossEquiv e G K)) := by
    ext K
    change f K.val = crossCellRestriction e G f (stateCellCrossEquiv e G K)
    rw [crossCellRestriction_apply_equiv]
  rw [heq, expectation_stateLeftData_crossCell]

theorem crossCellRestriction_left_expectation
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    crossCellRestriction e G (PairResampling.expectation n d {e 0,e 1} f) =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
        (crossCellRestriction e G f) := by
  ext z
  have h := left_expectation_eq_crossCell e G f ((stateCellCrossEquiv e G).symm z)
  simpa only [Equiv.apply_symm_apply, crossCellRestriction] using h

theorem crossCellRestriction_right_expectation
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    crossCellRestriction e G (PairResampling.expectation n d {e 2,e 3} f) =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
        (crossCellRestriction e G f) := by
  ext z
  have h := right_expectation_eq_crossCell e G f ((stateCellCrossEquiv e G).symm z)
  simpa only [Equiv.apply_symm_apply, crossCellRestriction] using h

theorem right_left_expectation_cell_affine
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    ∃ A B : ℝ, (CrossBlock.total (crossCode e G.val) ≠ 2 → B = 0) ∧
      ∀ H : StateCell e G,
        PairResampling.expectation n d {e 2,e 3}
          (PairResampling.expectation n d {e 0,e 1} f) H.val =
            A + B * PairEquality.observable (e 0) (e 2) (e 3) H.val := by
  obtain ⟨A,B,hB,hAB⟩ := CrossCellMoments.expectation_first_second_affine
    (CrossBlock.total (crossCode e G.val))
    (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1)
    (crossCellRestriction e G f)
  refine ⟨A,B,hB,?_⟩
  intro H
  rw [right_expectation_eq_crossCell, crossCellRestriction_left_expectation]
  have h := hAB (stateCellCrossEquiv e G H)
  change PairFibers.expectation
    (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
    (PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
      (crossCellRestriction e G f)) (stateCellCrossEquiv e G H) =
        A + B * flag (stateLeftData e G H).val.1 at h
  rw [stateLeftFlag_eq_observable] at h
  exact h

theorem left_right_expectation_cell_affine
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    ∃ A B : ℝ, (CrossBlock.total (crossCode e G.val) ≠ 2 → B = 0) ∧
      ∀ H : StateCell e G,
        PairResampling.expectation n d {e 0,e 1}
          (PairResampling.expectation n d {e 2,e 3} f) H.val =
            A + B * PairEquality.observable (e 2) (e 0) (e 1) H.val := by
  obtain ⟨A,B,hB,hAB⟩ := CrossCellMoments.expectation_second_first_affine
    (CrossBlock.total (crossCode e G.val))
    (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1)
    (crossCellRestriction e G f)
  refine ⟨A,B,hB,?_⟩
  intro H
  rw [left_expectation_eq_crossCell, crossCellRestriction_right_expectation]
  have h := hAB (stateCellCrossEquiv e G H)
  change PairFibers.expectation
    (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
    (PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
      (crossCellRestriction e G f)) (stateCellCrossEquiv e G H) =
        A + B * flag (stateRightData e G H).val.1 at h
  rw [stateRightFlag_eq_observable] at h
  exact h

end Problem315.DisjointMarginal

end

end OAI

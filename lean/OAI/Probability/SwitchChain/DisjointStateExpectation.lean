import OAI.Probability.SwitchChain.DisjointStateLaw
import OAI.Probability.SwitchChain.PairFibers

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

abbrev CellSpace (e : Fin 4 ↪ Fin n) (G : GraphState n d) :=
  EuclideanSpace ℝ (StateCell e G)

def restrictToStateCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) : CellSpace e G :=
  WithLp.toLp 2 (fun H => f H.val)

@[simp] theorem restrictToStateCell_apply
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    restrictToStateCell e G f H = f H.val := rfl

def stateCellFiberEquiv {β : Type*}
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (a : Finset (Fin n))
    (key : StateCell e G → β)
    (hkey : ∀ H K : StateCell e G,
      PairResampling.SameFiber a H.val.val K.val.val ↔ key H = key K)
    (hclosed : ∀ (H : StateCell e G) (K : GraphState n d),
      PairResampling.SameFiber a H.val.val K.val → SameCell e G.val K.val)
    (H : StateCell e G) :
    ↥(PairFibers.cell (Setoid.ker key) H) ≃ ↥(PairResampling.fiberStates a H.val) where
  toFun K := ⟨K.val.val,
    (PairResampling.mem_fiberStates a H.val K.val.val).mpr
      ((hkey H K.val).mpr ((PairFibers.mem_cell _ H K.val).mp K.property))⟩
  invFun K :=
    let hK := (PairResampling.mem_fiberStates a H.val K.val).mp K.property
    ⟨⟨K.val, hclosed H K.val hK⟩,
      (PairFibers.mem_cell _ H _).mpr ((hkey H _).mp hK)⟩
  left_inv K := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv K := by apply Subtype.ext; rfl

theorem expectation_restrictToStateCell {β : Type*}
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (a : Finset (Fin n))
    (key : StateCell e G → β)
    (hkey : ∀ H K : StateCell e G,
      PairResampling.SameFiber a H.val.val K.val.val ↔ key H = key K)
    (hclosed : ∀ (H : StateCell e G) (K : GraphState n d),
      PairResampling.SameFiber a H.val.val K.val → SameCell e G.val K.val)
    (f : PairResampling.StateSpace n d) :
    PairFibers.expectation (Setoid.ker key) (restrictToStateCell e G f) =
      restrictToStateCell e G (PairResampling.expectation n d a f) := by
  ext H
  let E := stateCellFiberEquiv e G a key hkey hclosed H
  have hcard : (PairFibers.cell (Setoid.ker key) H).card =
      (PairResampling.fiberStates a H.val).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr E
  have hsum :
      (∑ K ∈ PairFibers.cell (Setoid.ker key) H, restrictToStateCell e G f K) =
      ∑ K ∈ PairResampling.fiberStates a H.val, f K := by
    apply Finset.sum_bij (fun K _ => K.val)
    · intro K hK
      exact (PairResampling.mem_fiberStates a H.val K.val).mpr
        ((hkey H K).mpr ((PairFibers.mem_cell _ H K).mp hK))
    · intro K hK L hL h
      exact Subtype.ext h
    · intro K hK
      have hF := (PairResampling.mem_fiberStates a H.val K).mp hK
      refine ⟨⟨K, hclosed H K hF⟩, ?_, rfl⟩
      exact (PairFibers.mem_cell _ H _).mpr ((hkey H _).mp hF)
    · intro K hK
      rfl
  rw [PairFibers.expectation_apply, restrictToStateCell_apply,
    PairResampling.expectation_eq_average, hcard, hsum]

theorem left_expectation_restrictToStateCell
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    PairFibers.expectation (Setoid.ker (stateRightData e G)) (restrictToStateCell e G f) =
      restrictToStateCell e G (PairResampling.expectation n d {e 0,e 1} f) :=
  expectation_restrictToStateCell e G {e 0,e 1} (stateRightData e G)
    (sameFiber_left_iff_stateRightData_eq e G) (stateCell_of_leftFiber e G) f

theorem right_expectation_restrictToStateCell
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    PairFibers.expectation (Setoid.ker (stateLeftData e G)) (restrictToStateCell e G f) =
      restrictToStateCell e G (PairResampling.expectation n d {e 2,e 3} f) :=
  expectation_restrictToStateCell e G {e 2,e 3} (stateLeftData e G)
    (sameFiber_right_iff_stateLeftData_eq e G) (stateCell_of_rightFiber e G) f

theorem left_deviation_restrictToStateCell
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    PairFibers.deviation (Setoid.ker (stateRightData e G)) (restrictToStateCell e G f) =
      restrictToStateCell e G (PairResampling.fluctuation n d {e 0,e 1} f) := by
  rw [PairFibers.deviation_eq_sub, left_expectation_restrictToStateCell,
    PairResampling.fluctuation_eq_sub]
  rfl

theorem right_deviation_restrictToStateCell
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    PairFibers.deviation (Setoid.ker (stateLeftData e G)) (restrictToStateCell e G f) =
      restrictToStateCell e G (PairResampling.fluctuation n d {e 2,e 3} f) := by
  rw [PairFibers.deviation_eq_sub, right_expectation_restrictToStateCell,
    PairResampling.fluctuation_eq_sub]
  rfl

end Problem315.DisjointMarginal

end

end OAI

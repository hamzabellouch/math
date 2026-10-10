import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySizeBounds

namespace OAI

/-! One uniform power bounds all finite geometric inputs of the actual
history-to-lattice coefficient program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumForkList QuantumPaddedLabelProgram

attribute [local irreducible] spatialDensity

def geometryEnvelope (A B D R n : ℕ) : ℕ :=
  rawBondFactor*n+spatialSizeFactor D*n+spatialSizeFactor D*n*R+
    boxFactor A B*(n+1)+1

private theorem geometryEnvelope_parts (A B D R n : ℕ) :
    rawBondFactor*n ≤ geometryEnvelope A B D R n ∧
    spatialSizeFactor D*n ≤ geometryEnvelope A B D R n ∧
    spatialSizeFactor D*n*R ≤ geometryEnvelope A B D R n ∧
    boxFactor A B*(n+1) ≤ geometryEnvelope A B D R n := by
  unfold geometryEnvelope
  omega

theorem geometryEnvelope_power (A B D R : ℕ) : ∃ k : ℕ, ∀ n,
    geometryEnvelope A B D R n ≤ (n+2)^k := by
  let p : Polynomial ℕ := Polynomial.C rawBondFactor*Polynomial.X+
    Polynomial.C (spatialSizeFactor D)*Polynomial.X+
    Polynomial.C (spatialSizeFactor D*R)*Polynomial.X+
    Polynomial.C (boxFactor A B)*(Polynomial.X+1)+1
  obtain ⟨k,hk⟩ := natPolynomial_power_bound p
  refine ⟨k,fun n => ?_⟩
  have h := hk n
  simp only [p,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one] at h
  convert h using 1; unfold geometryEnvelope; ring

private theorem crossing_card_bound {A B R : ℕ} (M : QMASpatialExchangeModel A B)
    (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (hR : QMASpatialExchangeModel.routeLengthBound A B=R) :
    (M.portRouteData hA hd).crossingCells.card ≤ Fintype.card M.Term*R := by
  have h := (M.portRouteData hA hd).crossingCells_card_le (M.bufferedPath_length hd)
  change _ ≤ Fintype.card M.Term*QMASpatialExchangeModel.routeLengthBound A B at h
  rw [hR] at h
  exact h

theorem model_geometry_power : ∃ k : ℕ, ∀ (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ),
    (input c hc hT hne N).bonds.length ≤ (qubitCount (qmaSparseCircuit c)+2)^k ∧
    Fintype.card (model c hc hT hne N).Term ≤ (qubitCount (qmaSparseCircuit c)+2)^k ∧
    ((model c hc hT hne N).portRouteData finalDensity_pos
      (model_degree c hc hT hne N)).crossingCells.card ≤
        (qubitCount (qmaSparseCircuit c)+2)^k ∧
    256*(model c hc hT hne N).bufferedWidth ≤ (qubitCount (qmaSparseCircuit c)+2)^k ∧
    256*(model c hc hT hne N).bufferedHeight ≤ (qubitCount (qmaSparseCircuit c)+2)^k := by
  obtain ⟨k,hk⟩ := geometryEnvelope_power (spatialDensity rawDensity historyDegree)
    (27*spatialDensity rawDensity historyDegree) historyDegree routeRounds
  refine ⟨k,fun c hc hT hne N => ?_⟩
  have hb := history_bonds_linear (qmaSparseCircuit c) hT N
  rw [← input_bonds c hc hT hne N] at hb
  have hs := model_size_linear c hc hT hne N
  have he : Fintype.card (model c hc hT hne N).Term ≤
      spatialSizeFactor historyDegree*qubitCount (qmaSparseCircuit c) := by omega
  have hx := model_box_bound (model c hc hT hne N)
    (model_rows_bound c hc hT hne N) (model_width_bound c hc hT hne N)
  have hr := crossing_card_bound (model c hc hT hne N) finalDensity_pos
    (model_degree c hc hT hne N) routeRounds_eq
  have hr' : ((model c hc hT hne N).portRouteData finalDensity_pos
      (model_degree c hc hT hne N)).crossingCells.card ≤
      spatialSizeFactor historyDegree*qubitCount (qmaSparseCircuit c)*routeRounds :=
    hr.trans (Nat.mul_le_mul_right routeRounds he)
  have hp := hk (qubitCount (qmaSparseCircuit c))
  obtain ⟨hb',he',hr'',hx'⟩ := geometryEnvelope_parts (spatialDensity rawDensity historyDegree)
    (27*spatialDensity rawDensity historyDegree) historyDegree routeRounds
    (qubitCount (qmaSparseCircuit c))
  exact ⟨hb.trans (hb'.trans hp),he.trans (he'.trans hp),hr'.trans (hr''.trans hp),
    hx.1.trans (hx'.trans hp),hx.2.trans (hx'.trans hp)⟩

theorem outputCoefficientNat_one (m D L T : ℕ) : 1 ≤ outputCoefficientNat m D L T := by
  have h (M L T k : ℕ) (hL : 1 ≤ L) : 1 ≤ envelopeNat M L T k := by
    induction k with
    | zero => exact hL
    | succ k ih => dsimp only [envelopeNat,coefficientNat]; omega
  exact h _ _ _ _ (by dsimp only [coefficientNat]; omega)

theorem outputCoefficientNat_of_power {D a n k m L T : ℕ}
    (h : ∀ x : QuantumCoefficientPrograms.Input, outputCoefficientNat x.1 D x.2.1 x.2.2 ≤
      ((QuantumCoefficientPrograms.inputCode x).length+2)^a)
    (hm : m ≤ (n+2)^k) (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    outputCoefficientNat m D L T ≤ (n+2)^((k+4)*a) :=
  QuantumCoefficientPrograms.input_function_power h hm hL hT

theorem latticeBound_of_power {D a n k m r L T : ℕ}
    (h : ∀ x : QuantumCoefficientPrograms.LatticeInput,
      QuantumCoefficientPrograms.latticeBound D x.1 x.2.1 x.2.2.1 x.2.2.2 ≤
        ((QuantumCoefficientPrograms.latticeInputCode x).length+2)^a)
    (hm : m ≤ (n+2)^k) (hr : r ≤ (n+2)^k)
    (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    QuantumCoefficientPrograms.latticeBound D m r L T ≤ (n+2)^((k+4)*a) :=
  QuantumCoefficientPrograms.lattice_function_power h hm hr hL hT

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI

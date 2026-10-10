import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGeometryPowers

namespace OAI

/-! The literal coefficient programs and the exact geometry admit a common
polynomial exponent, uniform over verifier circuits. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumAlgebraicHistory QuantumForkList QuantumPaddedLabelProgram
open QuantumCoefficientPrograms

theorem source_data_power : ∃ k : ℕ, ∀ (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []), ∃ L : ℕ,
    1 ≤ L ∧ (model c hc hT hne (latticePrecision c)).exchangeGraph.CoefficientBound L ∧
    256*(model c hc hT hne (latticePrecision c)).bufferedWidth ≤
      (qubitCount (qmaSparseCircuit c)+2)^k ∧
    256*(model c hc hT hne (latticePrecision c)).bufferedHeight ≤
      (qubitCount (qmaSparseCircuit c)+2)^k ∧
    latticeBound routeRounds (Fintype.card (model c hc hT hne (latticePrecision c)).Term)
      ((model c hc hT hne (latticePrecision c)).portRouteData finalDensity_pos
        (model_degree c hc hT hne (latticePrecision c))).crossingCells.card L (latticePrecision c) ≤
          (qubitCount (qmaSparseCircuit c)+2)^k := by
  obtain ⟨g,hg⟩ := model_geometry_power
  obtain ⟨a,ha⟩ := historyCoefficientBudget_power totalRounds
  obtain ⟨b,hb⟩ := parameters_power totalRounds
  obtain ⟨d,hd⟩ := outputCoefficientNat_power historyDegree
  obtain ⟨e,he⟩ := latticeBound_power routeRounds
  let k₁ := g+a+b
  let k₂ := k₁+(k₁+4)*d
  refine ⟨k₂+(k₂+4)*e,fun c hc hT hne => ?_⟩
  let n := qubitCount (qmaSparseCircuit c)
  let N := latticePrecision c
  let L := outputCoefficientNat (input c hc hT hne N).bonds.length historyDegree
    (historyCoefficientBudget (qmaSparseCircuit c) N) N
  have lift {i j : ℕ} (h : i ≤ j) : (n+2)^i ≤ (n+2)^j :=
    pow_le_pow_right₀ (by omega : 1 ≤ n+2) h
  obtain ⟨hm,ht,hr,hx,hy⟩ := hg c hc hT hne N
  have hraw := ha (qmaSparseCircuit c)
  have hN := (hb (qmaSparseCircuit c)).2.2.2
  have hL : L ≤ (n+2)^((k₁+4)*d) := outputCoefficientNat_of_power hd
    (hm.trans (lift (by dsimp [k₁]; omega)))
    (hraw.trans (lift (by dsimp [k₁]; omega)))
    (hN.trans (lift (by dsimp [k₁]; omega)))
  have hf : latticeBound routeRounds (Fintype.card (model c hc hT hne N).Term)
      ((model c hc hT hne N).portRouteData finalDensity_pos
        (model_degree c hc hT hne N)).crossingCells.card L N ≤
      (n+2)^((k₂+4)*e) := latticeBound_of_power he
    (ht.trans (lift (by dsimp [k₂,k₁]; omega)))
    (hr.trans (lift (by dsimp [k₂,k₁]; omega)))
    (hL.trans (lift (by dsimp [k₂]; omega)))
    (hN.trans (lift (by dsimp [k₂,k₁]; omega)))
  exact ⟨L,outputCoefficientNat_one _ _ _ _,model_coefficientBound c hc hT hne N,
    hx.trans (lift (by dsimp [k₂,k₁]; omega)),
    hy.trans (lift (by dsimp [k₂,k₁]; omega)),
    hf.trans (lift (by omega))⟩

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI

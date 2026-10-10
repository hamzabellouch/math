import OAI.Combinatorics.ContingencyTables.Rooted.RootedCorrectionProgram

namespace OAI

/-! # The executed correction equals the analysed rational correction -/

namespace ContingencyTables.RootedCorrectionProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary RootedCompletion
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) : Input :=
  ((RootedOracleWalkProgram.data A C a K z v,
    List.ofFn (fun i => (f (RootedForestCatalog.freeEquiv A i)).val)),(degree,depth))

lemma exponentInput_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    exponentInput (data A C a K z v f degree depth)=
      RootedPenaltyEvaluateProgram.data A C a
        (ForestCountIdentification.smallX A.small z)
        (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j)
        (RootedCatalogGrid.naturalValues A v) := by
  rw [RootedCatalogGrid.evaluatorInput_grid]
  rfl

lemma exponent_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    RootedPenaltyEvaluateProgram.evaluate (exponentInput (data A C a K z v f degree depth))=
      RootedOracleDensity.gridExponent A (rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K v) :=
  RootedCatalogGrid.evaluate_grid A C a K hC z v

lemma pointInput_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    pointInput (data A C a K z v f degree depth)=
      RootedForestPrepareProgram.data A C (rationalBinWidth A C)
        (ForestCountIdentification.smallX A.small z)
        (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j)
        (fun t => (f t).val) := by
  change (((C,RootedPenaltyEvaluateProgram.width ((A.d,A.W),(C,a))),
    RootedDemandProgram.data A (ForestCountIdentification.smallX A.small z)
      (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j)),_)=_
  rw [RootedPenaltyEvaluateProgram.width_data]
  rfl

lemma point_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    TreeFraction.val (RootedPointPenaltyProgram.output
      (pointInput (data A C a K z v f degree depth)))=
      RootedOracleDensity.rationalD A (rowColumn A.T) C z (rationalIntegerPoint A C f) := by
  rw [pointInput_data]
  exact RootedPointPenaltyProgram.output_integerPoint A C hC z f

lemma populationInput_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    populationInput (data A C a K z v f degree depth)=
      BinPopulationProgram.data A K (RootedCatalogGrid.gridEquiv A K v) := by
  change (RootedBinFramesProgram.frames (RootedBinFramesProgram.data A 0 v)).map Prod.fst=_
  rw [RootedBinFramesProgram.frames_data,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,RootedCatalogGrid.naturalBin_grid,
    RootedCatalogGrid.naturalValues,Equiv.symm_apply_apply]

lemma population_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hK : 0 < K)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool)
    (hf : integerBin A K hK f=RootedCatalogGrid.gridEquiv A K v) :
    TreeFraction.val (BinPopulationProgram.output
      (populationInput (data A C a K z v f degree depth)))=rationalPopulation A K hK f := by
  rw [populationInput_data,←hf]
  exact BinPopulationProgram.output_integerBin A K hK f

lemma phase_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    TreeFraction.val (phase (data A C a K z v f degree depth))=(a:ℚ)/rationalHeight A C := by
  change (a:ℚ)/RootedPenaltyEvaluateProgram.height ((A.d,A.W),(C,a))=_
  rw [RootedPenaltyEvaluateProgram.height_data]

theorem output_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 0 < K)
    (hB : (K:ℝ)=binWidth A C) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) (sigma : ℚ)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth : depth.length=PowerOfTwoApproximation.depth sigma)
    (hf : integerBin A K hK f=RootedCatalogGrid.gridEquiv A K v) :
    TreeFraction.val (output (data A C a K z v f degree depth))=
      RootedOracleDensity.computedCorrection A (rowColumn A.T) C a z K hK sigma f := by
  let input := data A C a K z v f degree depth
  let frame : CorrectionValueProgram.Frame :=
    ((RootedPenaltyEvaluateProgram.evaluate (exponentInput input),phase input),
      RootedPointPenaltyProgram.output (pointInput input))
  let population := BinPopulationProgram.output (populationInput input)
  have hexponent : (frame.1.1:ℚ)-TreeFraction.val frame.1.2*TreeFraction.val frame.2=
      RootedOracleDensity.correctionExponent A (rowColumn A.T) C a z K hK f := by
    dsimp only [frame,input]
    rw [exponent_data A C a K hC,phase_data,point_data A C a K hC,←hf]
    rfl
  have hb := RootedOracleDensity.correctionExponent_bounds A (rowColumn A.T) C a
    hC haH z K hK hB f
  have hlo : -2 ≤ (frame.1.1:ℚ)-TreeFraction.val frame.1.2*TreeFraction.val frame.2 := by
    rw [hexponent]; exact hb.1
  have hhi : (frame.1.1:ℚ)-TreeFraction.val frame.1.2*TreeFraction.val frame.2 ≤ 2 := by
    rw [hexponent]; exact hb.2
  have he := CorrectionValueProgram.output_approximate frame population degree depth sigma
    hdegree hdepth hlo hhi
  change TreeFraction.val (CorrectionValueProgram.output ((frame,population),(degree,depth)))=_
  rw [he,hexponent]
  rw [show TreeFraction.val population=rationalPopulation A K hK f from
    population_data A C a K hK z v f degree depth hf]
  rfl

end
end ContingencyTables.RootedCorrectionProgram

end OAI

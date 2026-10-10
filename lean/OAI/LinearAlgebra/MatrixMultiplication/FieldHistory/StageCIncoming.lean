import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Support
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageCStatistics
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageCProductRates

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryStageCIncoming

open AllFieldHistory AllFieldHistorySupport AllFieldParameters
open CWStageCProducts InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def stageCActive (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick) :
    Active K tick := ⟨(.stageC h, phi), ht⟩

def positionEquiv (allocation : Allocation) (dilation : ℕ) (h : PartC K)
    (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation)) :
    JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation dilation) (stageCActive h phi ht) ≃
      CWStageCProducts.Positions (populationAtomCounts allocation dilation (h, phi)) :=
  (JointCanonicalization.positionEquiv (activeCounts (K := K) (tick := tick) allocation dilation) e
    (stageCActive h phi ht)).trans
      (branchPositionEquiv allocation dilation (.stageC h, phi))

theorem positionEquiv_shape (allocation : Allocation) (dilation : ℕ) (h : PartC K)
    (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation))
    (j : JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation dilation) (stageCActive h phi ht)) :
    branchShape (.stageC h, phi) (positionEquiv allocation dilation h phi ht e j).1 =
      (e (stageCActive h phi ht)).val j := by
  exact (branchPositionEquiv_shape allocation dilation (.stageC h, phi)
    (JointCanonicalization.positionEquiv (activeCounts (K := K) (tick := tick) allocation dilation) e
      (stageCActive h phi ht) j)).trans
    (JointCanonicalization.positionEquiv_shape (activeCounts (K := K) (tick := tick) allocation dilation) e
      (stageCActive h phi ht) j)

theorem positionEquiv_symm_shape (allocation : Allocation) (dilation : ℕ) (h : PartC K)
    (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation))
    (p : CWStageCProducts.Positions (populationAtomCounts allocation dilation (h, phi))) :
    (e (stageCActive h phi ht)).val ((positionEquiv allocation dilation h phi ht e).symm p) =
      branchShape (.stageC h, phi) p.1 := by
  have hp := positionEquiv_shape allocation dilation h phi ht e
    ((positionEquiv allocation dilation h phi ht e).symm p)
  simpa only [Equiv.apply_symm_apply] using hp.symm

theorem typeWindow_of_target_side_weights (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation dilation) (side : Fin 3)
    (hweights : ∀ j : JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation dilation)
        (stageCActive h phi ht),
      CWLeafStatistics.weight ((w (stageCActive h phi ht) j).1 (0 : Fin 1)) =
          (JointPopulation.shapeSide side ((e (stageCActive h phi ht)).val j)).val ∧
      CWLeafStatistics.weight ((w (stageCActive h phi ht) j).2 (0 : Fin 1)) =
          activeParentShape (stageCActive h phi ht) side -
            (JointPopulation.shapeSide side ((e (stageCActive h phi ht)).val j)).val)
    (η : ℝ) (hη : 0 ≤ η) :
    typeWindow
      (fun a : Fin 6 =>
        (littleLaw (cParameterParent h) (cShapeParent h) (phi.symm side) a : ℝ)) η
      (fun j => CWCompleteStatistics.twoStatistic
        ![(w (stageCActive h phi ht) j).1 (0 : Fin 1), (w (stageCActive h phi ht) j).2 (0 : Fin 1)]) := by
  let p := positionEquiv allocation dilation h phi ht e
  let words : CWStageCProducts.Positions (populationAtomCounts allocation dilation (h, phi)) →
      CWStageCProducts.Word := fun j =>
    ![(w (stageCActive h phi ht) (p.symm j)).1 (0 : Fin 1),
      (w (stageCActive h phi ht) (p.symm j)).2 (0 : Fin 1)]
  have hgeometry (j : CWStageCProducts.Positions
      (populationAtomCounts allocation dilation (h, phi))) :
      CWLeafStatistics.weight (words j 0) =
        branchAtom (stageCDistinguished (cShapeParent h)) j.1 (phi.symm side) ∧
      CWLeafStatistics.weight (words j 1) =
        CWStageCProducts.shape (stageCDistinguished (cShapeParent h)) (phi.symm side) -
          branchAtom (stageCDistinguished (cShapeParent h)) j.1 (phi.symm side) := by
    have hw := hweights (p.symm j)
    have hs := positionEquiv_symm_shape allocation dilation h phi ht e j
    change (e (stageCActive h phi ht)).val (p.symm j) = _ at hs
    rw [hs] at hw
    simpa only [words, Matrix.cons_val_zero, Matrix.cons_val_one,
      activeParentShape, stageCActive, Work.parentShape, branchShape,
      encodePhysicalShape_side, physicalShape, Work.splitShape, cSplit,
      branchAtom_eq_stageCAtom, shape_eq_parent (cShapeParent h) (bShape_size h.1.val)
        h.1.property] using hw
  have hwindow := typeWindow_of_placed_side_weights
    (populationAtomCounts allocation dilation (h, phi))
    (cParameterParent h) (cShapeParent h) (bShape_size h.1.val) h.1.property
    (population allocation dilation (.partC h, phi))
    (work_source_population_pos allocation hd (.stageC h, phi))
    (populationAtomCounts_parent allocation dilation (h, phi))
    phi side words hgeometry η hη
  exact (JointCanonicalization.typeWindow_reindex _ η
    (fun j => CWCompleteStatistics.twoStatistic
      ![(w (stageCActive h phi ht) j).1 (0 : Fin 1), (w (stageCActive h phi ht) j).2 (0 : Fin 1)])
    p.symm).mp hwindow

end MatrixMultiplication.AllFieldHistoryStageCIncoming

end

end OAI

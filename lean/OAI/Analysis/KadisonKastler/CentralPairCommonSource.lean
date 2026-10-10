import OAI.Analysis.KadisonKastler.CenterAlgebra
import OAI.Analysis.KadisonSimilarity.Tracial.CentralCStarSource
import OAI.Analysis.KadisonSimilarity.Tracial.JointCStarSource

namespace OAI

/-! # One norm-separable source for the common central decomposition -/

namespace KadisonKastler

open KadisonSimilarity TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure CentralPairCommonSource (M N : VonNeumannAlgebra H)
    (C : StarSubalgebra ℂ (H →L[ℂ] H)) where
  leftComm : StarSubalgebra ℂ (H →L[ℂ] H)
  rightComm : StarSubalgebra ℂ (H →L[ℂ] H)
  source : StarSubalgebra ℂ (H →L[ℂ] H)
  left_closed : IsClosed (leftComm : Set (H →L[ℂ] H))
  right_closed : IsClosed (rightComm : Set (H →L[ℂ] H))
  source_closed : IsClosed (source : Set (H →L[ℂ] H))
  left_separable : SeparableSpace leftComm
  right_separable : SeparableSpace rightComm
  source_separable : SeparableSpace source
  left_mem : leftComm ≤ M.commutant.toStarSubalgebra
  right_mem : rightComm ≤ N.commutant.toStarSubalgebra
  left_generates : (starSubalgebraCommutant leftComm).commutant = M.commutant
  right_generates : (starSubalgebraCommutant rightComm).commutant = N.commutant
  original_le : C ≤ source
  left_le : leftComm ≤ source
  right_le : rightComm ≤ source
  central : source ≤ (concreteCenter M).commutant.toStarSubalgebra

theorem exists_centralPairCommonSource [SeparableSpace H]
    (M N : VonNeumannAlgebra H) (hcenter : concreteCenter M = concreteCenter N)
    (C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hCs : IsSeparable (C : Set (H →L[ℂ] H)))
    (hC : C ≤ (concreteCenter M).commutant.toStarSubalgebra) :
    Nonempty (CentralPairCommonSource M N C) := by
  obtain ⟨L, hLc, hLs, hLM, hLg⟩ := exists_separable_generating_cstar_subalgebra M.commutant
  obtain ⟨R, hRc, hRs, hRN, hRg⟩ := exists_separable_generating_cstar_subalgebra N.commutant
  let : SeparableSpace C := hCs.separableSpace
  let : SeparableSpace L := hLs
  let : SeparableSpace R := hRs
  let S := jointCStarSource C (jointCStarSource L R)
  have hclosed : IsClosed ((concreteCenter M).commutant.toStarSubalgebra : Set (H →L[ℂ] H)) := by
    change IsClosed ((concreteCenter M).commutant : Set (H →L[ℂ] H))
    rw [VonNeumannAlgebra.coe_commutant]
    exact Set.isClosed_centralizer _
  have hL : L ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    intro T hT
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    exact VonNeumannAlgebra.mem_commutant_iff.mp (hLM hT) z hz.1
  have hR : R ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    intro T hT
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    have hzN : z ∈ concreteCenter N := hcenter ▸ hz
    exact VonNeumannAlgebra.mem_commutant_iff.mp (hRN hT) z hzN.1
  exact ⟨{
    leftComm := L
    rightComm := R
    source := S
    left_closed := hLc
    right_closed := hRc
    source_closed := jointCStarSource_isClosed _ _
    left_separable := hLs
    right_separable := hRs
    source_separable := inferInstance
    left_mem := hLM
    right_mem := hRN
    left_generates := hLg
    right_generates := hRg
    original_le := le_jointCStarSource_left _ _
    left_le := (le_jointCStarSource_left L R).trans (le_jointCStarSource_right _ _)
    right_le := (le_jointCStarSource_right L R).trans (le_jointCStarSource_right _ _)
    central := jointCStarSource_minimal _ _ _ hC
      (jointCStarSource_minimal _ _ _ hL hR hclosed) hclosed }⟩

end

end KadisonKastler

end OAI

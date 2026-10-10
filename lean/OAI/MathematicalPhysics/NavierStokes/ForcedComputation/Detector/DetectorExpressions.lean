import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedResidual
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorClockExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FieldReindex
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPerturbations
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularFluid

namespace OAI

/-! Finite expressions for an individual prescribed detector block.
The processor and bump are sampled by explicit rational clock profiles. -/

namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped BigOperators

def bumpExpression (b : ℚ) : FieldExpr :=
  .mul (.atom 1 (.cutoff 1 (1 / 4 - b) (1 / 4 - b / 2) (1 / 4 + b / 2) (1 / 4 + b)))
    (.atom 2 (.cutoff 1 (1 / 4 - b) (1 / 4 - b / 2) (1 / 4 + b / 2) (1 / 4 + b)))

theorem bumpExpression_valid {b : ℚ} (hb : 0 < b) : (bumpExpression b).Valid := by
  constructor <;> exact PeriodicExpr.cutoff_valid (by norm_num) (by linarith) (by linarith)

theorem bumpExpression_val (b : ℚ) (y : SpaceTime) :
    (bumpExpression b).val y = detectorBump b (horizontal y.2) := by
  simp only [bumpExpression, FieldExpr.val, PeriodicExpr.cutoff_val,
    Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rfl

def processorComponent (H : FieldExpr) (j : Fin 2) : FieldExpr :=
  ((SpatialExpression.suspensionCode H) j.castSucc).reindex timeHeightSwap

theorem processorComponent_valid {H : FieldExpr} (hH : H.Valid) (j : Fin 2) :
    (processorComponent H j).Valid :=
  FieldExpr.valid_reindex (SpatialExpression.suspensionCode_valid hH j.castSucc) _

theorem processorComponent_val {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (j : Fin 2) (y : SpaceTime) :
    (processorComponent H j).val y = planarSlice H y.1 (horizontal y.2) j := by
  rw [processorComponent, FieldExpr.val_timeHeightSwap, planarSlice_eq_horizontal hH]
  have h := congrFun (congrFun (SpatialExpression.suspensionCode_val hH hT)
    (y.2 2, atHeight (horizontal y.2) y.1)) j.castSucc
  fin_cases j <;> exact h

def sourceTermExpression (C L n : ℕ) : ClockedExpr :=
  .mul (.profile (injectionExpression C L n).diff)
    (.field (.const 0) (bumpExpression (width L n)))

theorem sourceTermExpression_valid (C L n : ℕ) :
    (sourceTermExpression C L n).Valid :=
  ⟨trivial, bumpExpression_valid (width_pos L n)⟩

theorem sourceTermExpression_val (C L n : ℕ) (y : SpaceTime) :
    (sourceTermExpression C L n).val y = detectorSourceTerm C L n (y.1, horizontal y.2) := by
  simp only [sourceTermExpression, ClockedExpr.val, injectionExpression_diff_val,
    bumpExpression_val, clockedPoint]
  rfl

def driftComponentExpression (H : FieldExpr) (C L n : ℕ) (j : Fin 2) : ClockedExpr :=
  .mul (.profile (phaseExpression C L n).diff)
    (.field (phaseExpression C L n) (processorComponent H j))

theorem driftComponentExpression_valid {H : FieldExpr} (hH : H.Valid)
    (C L n : ℕ) (j : Fin 2) : (driftComponentExpression H C L n j).Valid :=
  ⟨trivial, processorComponent_valid hH j⟩

theorem driftComponentExpression_val {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (C L n : ℕ) (j : Fin 2) (y : SpaceTime) :
    (driftComponentExpression H C L n j).val y =
      detectorDriftTerm (planarSlice H) C L n (y.1, horizontal y.2) j := by
  simp only [driftComponentExpression, ClockedExpr.val, phaseExpression_diff_val,
    processorComponent_val hH hT, clockedPoint, phaseExpression_val]
  rfl

def driftTermExpression (H : FieldExpr) (C L n : ℕ) : ClockedVector :=
  ![driftComponentExpression H C L n 0, driftComponentExpression H C L n 1, .const 0]

theorem driftTermExpression_valid {H : FieldExpr} (hH : H.Valid) (C L n : ℕ) :
    (driftTermExpression H C L n).Valid := by
  intro j
  fin_cases j
  · exact driftComponentExpression_valid hH C L n 0
  · exact driftComponentExpression_valid hH C L n 1
  · trivial

theorem driftTermExpression_val {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (C L n : ℕ) (y : SpaceTime) :
    (driftTermExpression H C L n).val y =
      triangularLift (fun x => detectorDriftTerm (planarSlice H) C L n (y.1, x))
        (fun _ => 0) y.2 := by
  rw [triangularLift_eq]
  ext j
  fin_cases j
  · exact driftComponentExpression_val hH hT C L n 0 y
  · exact driftComponentExpression_val hH hT C L n 1 y
  · change (ClockedExpr.const 0).val y = 0
    simp only [ClockedExpr.val, Rat.cast_zero]

def sourcePrefixExpression (C L N : ℕ) : ClockedExpr :=
  ClockedExpr.sum (List.ofFn (fun n : Fin N => sourceTermExpression C L n))

def driftPrefixExpression (H : FieldExpr) (C L N : ℕ) : ClockedVector := fun j =>
  ClockedExpr.sum (List.ofFn (fun n : Fin N => driftTermExpression H C L n j))

theorem sourcePrefixExpression_valid (C L N : ℕ) : (sourcePrefixExpression C L N).Valid :=
  ClockedExpr.sum_ofFn_valid _ (fun _ => sourceTermExpression_valid C L _)

theorem driftPrefixExpression_valid {H : FieldExpr} (hH : H.Valid) (C L N : ℕ) :
    (driftPrefixExpression H C L N).Valid :=
  fun j => ClockedExpr.sum_ofFn_valid _ (fun _ => driftTermExpression_valid hH C L _ j)

theorem sourcePrefixExpression_val (C L N : ℕ) (y : SpaceTime) :
    (sourcePrefixExpression C L N).val y =
      ∑ n : Fin N, detectorSourceTerm C L n (y.1, horizontal y.2) := by
  rw [sourcePrefixExpression, ClockedExpr.sum_ofFn_val]
  simp only [sourceTermExpression_val]

theorem driftPrefixExpression_val (H : FieldExpr) (C L N : ℕ) (y : SpaceTime) :
    (driftPrefixExpression H C L N).val y =
      ∑ n : Fin N, (driftTermExpression H C L n).val y := by
  ext j
  simp only [driftPrefixExpression, ClockedVector.val, ClockedExpr.sum_ofFn_val,
    Finset.sum_apply]

end ForcedComputation.VelocityDetector

end OAI

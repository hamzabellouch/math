import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StartupEffective

namespace OAI

/-! Each local detector force is represented by a finite prefix of the
clocked program. The prefix is chosen from a coarse time bound. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped BigOperators ContDiff Topology

def prefixDrift (V : ℝ → Plane → Plane) (C L N : ℕ) (t : ℝ) (x : Plane) : Plane :=
  ∑ n : Fin N, detectorDriftTerm V C L n (t, x)

def prefixSource (C L N : ℕ) (t : ℝ) (x : Plane) : ℝ :=
  ∑ n : Fin N, detectorSourceTerm C L n (t, x)

theorem driftPrefixExpression_value {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (C L N : ℕ) :
    (driftPrefixExpression H C L N).val =
      triangularVelocity (prefixDrift (planarSlice H) C L N) (fun _ _ => 0) := by
  funext y
  rw [driftPrefixExpression_val]
  simp_rw [driftTermExpression_val hH hT]
  simp only [triangularVelocity, triangularLift, prefixDrift, map_sum,
    zero_smul, add_zero]

theorem sourcePrefixExpression_value (C L N : ℕ) (y : SpaceTime) :
    (sourcePrefixExpression C L N).val y = prefixSource C L N y.1 (horizontal y.2) :=
  sourcePrefixExpression_val C L N y

def verticalSourceExpression (C L N : ℕ) : ClockedVector :=
  ![.const 0, .const 0, sourcePrefixExpression C L N]

theorem verticalSourceExpression_valid (C L N : ℕ) :
    (verticalSourceExpression C L N).Valid := by
  intro j
  fin_cases j
  · trivial
  · trivial
  · exact sourcePrefixExpression_valid C L N

theorem verticalSourceExpression_value (C L N : ℕ) :
    (verticalSourceExpression C L N).val =
      triangularVelocity (fun _ _ => 0) (prefixSource C L N) := by
  funext y
  rw [triangularVelocity, triangularLift_eq]
  ext j
  fin_cases j
  · change (ClockedExpr.const 0).val y = 0
    simp only [ClockedExpr.val, Rat.cast_zero]
  · change (ClockedExpr.const 0).val y = 0
    simp only [ClockedExpr.val, Rat.cast_zero]
  · exact sourcePrefixExpression_value C L N y

def forcePrefixExpression (H : FieldExpr) (C L N : ℕ) : ClockedVector := fun j =>
  .add (ClockedResidual.code (driftPrefixExpression H C L N) 1 j)
    (verticalSourceExpression C L N j)

theorem forcePrefixExpression_valid {H : FieldExpr} (hH : H.Valid) (C L N : ℕ) :
    (forcePrefixExpression H C L N).Valid :=
  fun j => ⟨ClockedResidual.valid (driftPrefixExpression_valid hH C L N) 1 j,
    verticalSourceExpression_valid C L N j⟩

theorem forcePrefixExpression_value {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (C L N : ℕ) :
    (forcePrefixExpression H C L N).val =
      residual 1 (triangularVelocity (prefixDrift (planarSlice H) C L N) (fun _ _ => 0)) +
        triangularVelocity (fun _ _ => 0) (prefixSource C L N) := by
  have he : (forcePrefixExpression H C L N).val =
      (ClockedResidual.code (driftPrefixExpression H C L N) 1).val +
        (verticalSourceExpression C L N).val := rfl
  rw [he, ClockedResidual.val (driftPrefixExpression_valid hH C L N),
    driftPrefixExpression_value hH hT, verticalSourceExpression_value]
  norm_num only [Rat.cast_one]

theorem detectorDrift_prefix_germ (V : ℝ → Plane → Plane) (C L N : ℕ)
    (y : ℝ × Plane) (hN : y.1 + 1 ≤ (N : ℝ)) :
    Function.uncurry (detectorDrift V C L) =ᶠ[𝓝 y]
      Function.uncurry (prefixDrift V C L N) := by
  have h := detectorBlockSum_local_of_time_bound (detectorDriftTerm V C L)
    (detectorDriftTerm_before V C L) y N hN
  filter_upwards [h] with z hz
  change detectorBlockSum (detectorDriftTerm V C L) z =
    ∑ n : Fin N, detectorDriftTerm V C L n z
  exact hz.trans (Fin.sum_univ_eq_sum_range
    (fun n : ℕ => detectorDriftTerm V C L n z) N).symm

theorem detectorSource_prefix_germ (C L N : ℕ)
    (y : ℝ × Plane) (hN : y.1 + 1 ≤ (N : ℝ)) :
    Function.uncurry (detectorSource C L) =ᶠ[𝓝 y]
      Function.uncurry (prefixSource C L N) := by
  have h := detectorBlockSum_local_of_time_bound (detectorSourceTerm C L)
    (detectorSourceTerm_before C L) y N hN
  filter_upwards [h] with z hz
  change detectorBlockSum (detectorSourceTerm C L) z =
    ∑ n : Fin N, detectorSourceTerm C L n z
  exact hz.trans (Fin.sum_univ_eq_sum_range
    (fun n : ℕ => detectorSourceTerm C L n z) N).symm

end ForcedComputation.VelocityDetector

end

end OAI

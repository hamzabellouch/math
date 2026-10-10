import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Quadratic
import OAI.Geometry.CAT0Fillings.Differentiation.LocalBounds
import OAI.Geometry.CAT0Fillings.Charts.JacobianBound
import OAI.Geometry.CAT0Fillings.Charts.CurrentContinuity
import OAI.Geometry.CAT0Fillings.Charts.ScalarPieces
import OAI.Geometry.CAT0Fillings.Slicing.CycleCoarea
import OAI.Geometry.CAT0Fillings.Currents.IntegralPush
import OAI.Geometry.CAT0Fillings.Prism.Differential
import OAI.Geometry.CAT0Fillings.Prism.Action
import OAI.Geometry.CAT0Fillings.Currents.CycleDerivative
import OAI.Geometry.CAT0Fillings.Currents.CycleFTC
import OAI.Geometry.CAT0Fillings.Fillings.Existence
import OAI.Geometry.CAT0Fillings.Fillings.ConeBound
import OAI.Geometry.CAT0Fillings.Geometry.DeterminantBound
import OAI.Geometry.CAT0Fillings.Radial.FirstVariation
import OAI.Geometry.CAT0Fillings.Tangent.Transfer
import OAI.Geometry.CAT0Fillings.Calculus.ClosedChain
import OAI.Geometry.CAT0Fillings.Calculus.ClosedLevel
import OAI.Geometry.CAT0Fillings.Calculus.VectorLimit
import OAI.Geometry.CAT0Fillings.Calculus.Piecewise
import OAI.Geometry.CAT0Fillings.Calculus.Truncation
import OAI.Geometry.CAT0Fillings.Calculus.PositiveBivariate
import OAI.Geometry.CAT0Fillings.Powers.ClosedLimit
import OAI.Geometry.CAT0Fillings.Calculus.Polynomial
import OAI.Geometry.CAT0Fillings.Compactness.Projected
import OAI.Geometry.CAT0Fillings.Compactness.Borel
import OAI.Geometry.CAT0Fillings.Compactness.Interpolation
import OAI.Geometry.CAT0Fillings.Mass.Gradient
import OAI.Geometry.CAT0Fillings.Rearrangement.Gradient
import OAI.Geometry.CAT0Fillings.Minimizers.Nonnegative
import OAI.Geometry.CAT0Fillings.Chord.GroundState
import OAI.Geometry.CAT0Fillings.Chord.GroundProducts
import OAI.Geometry.CAT0Fillings.Calculus.Atlas
import OAI.Geometry.CAT0Fillings.Calculus.ChainSet
import OAI.Geometry.CAT0Fillings.Radial.Extension
import OAI.Geometry.CAT0Fillings.Chord.RadialIntegral
import OAI.Geometry.CAT0Fillings.Chord.TestIdentity
import OAI.Geometry.CAT0Fillings.Chord.Distribution
import OAI.Geometry.CAT0Fillings.Chord.DensityContradiction
import OAI.Geometry.CAT0Fillings.Euler.OppositeIntegral
import OAI.Geometry.CAT0Fillings.Euler.Contradiction
import OAI.Geometry.CAT0Fillings.Density.NearEuclidean
import OAI.Geometry.CAT0Fillings.Density.Normalized
import OAI.Geometry.CAT0Fillings.Fillings.Compact
import OAI.Geometry.CAT0Fillings.Geometry.Ball
import OAI.Geometry.CAT0Fillings.Transport.Proper
import OAI.Geometry.CAT0Fillings.Transport.Support

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open Foundations CurrentOperations

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
lemma proper_filling_bound [Nonempty X] (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hTc : CompactlySupported T)
    (hz : boundarySucc T = 0) :
    ∃ S : Functional X (k+3), IsIntegral (k+3) S ∧ CompactlySupported S ∧
      boundarySucc S = T ∧ mass S ≤ fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)) := by
  classical
  obtain ⟨K,hK,hTK⟩ := hTc
  let o : X := Classical.choice inferInstance
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_closedBall_lt 0 o
  obtain ⟨P,hP,hPr,hPf⟩ := hX.exists_ball_retraction o (R := R+2) (by linarith)
  let B := closedBall o (R+2)
  have : Nonempty B := ⟨o,by simp [B]; linarith⟩
  let p : X → B := fun x => ⟨P x,by simpa only [B,mem_closedBall,dist_comm] using hPr x⟩
  have hp : LipschitzWith 1 p := hP
  have hinc : LipschitzWith 1 (Subtype.val : B → X) := LipschitzWith.subtype_val B
  have hiA : AntilipschitzWith 1 (Subtype.val : B → X) := by
    intro x y
    change edist (x : X) (y : X) ≤ (1:ℝ≥0∞)*edist (x : X) (y : X)
    rw [one_mul]
  let U := pushCurrent p T
  have hU : IsIntegral (k+2) U := integral_push_proper hT hp
  have hUz : boundarySucc U = 0 := pushCurrent_cycle hz hp
  have hUm : mass U ≤ mass T := mass_push_one_general hT.1 hp
  have hB : IsCAT0 B := hX.closedBall o (by linarith)
  obtain ⟨V,hV,hVb,hVm⟩ := hB.exists_minimal_integral_filling hU hUz
  let S := pushCurrent (Subtype.val : B → X) V
  have hS : IsIntegral (k+3) S := integral_push_of_bilipschitz hV hinc hiA
  have hb : boundarySucc S = T := by
    rw [pushCurrent_boundarySucc V hinc,hVb,←pushCurrent_comp hinc]
    exact pushCurrent_eq_of_ball_support hT.1 hTK o R hKR hP
      (fun x hx => hPf x (by rwa [dist_comm]))
  refine ⟨S,hS,?_,hb,?_⟩
  · refine ⟨B,isCompact_closedBall o (R+2),?_⟩
    intro b π hab hbK
    change pushCurrent (Subtype.val : B → X) V b π = 0
    rw [pushCurrent_apply _ _ hab]
    have heq : b ∘ (Subtype.val : B → X) = fun _ => 0 := funext fun x => hbK x x.property
    rw [heq]
    have hπ := (admissible_comp hab hinc).2
    simpa using hV.1.linearFirst (fun _ => 0) (fun _ => 0) (fun i => π i ∘ Subtype.val)
      0 0 (BoundedLip.const 0) (BoundedLip.const 0) hπ
  · calc
      mass S ≤ mass V := mass_push_one_general hV.1 hinc
      _ = fillingVolume U := hVm
      _ ≤ fillingCoefficient (k+2)*(mass U)^(fillingPower (k+2)) := compact_filling_bound k B hB U hU hUz
      _ ≤ fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mass_nonneg U) hUm
          (le_of_lt (lt_trans zero_lt_one (fillingPower_gt_one (by omega)))))
          (fillingCoefficient_pos (by omega)).le

theorem sharp_integral_filling
    (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
    (hX : IsCAT0 X) (n : ℕ) (hn : 2 ≤ n) (T : IntegralCurrent X n)
    (hTc : CompactlySupported T.val) (hTz : IsCycle T.val) :
    ∃ S : IntegralCurrent X (n + 1), CompactlySupported S.val ∧
      boundarySucc S.val = T.val ∧
      mass S.val ≤ fillingCoefficient n * (mass T.val) ^ fillingPower n := by
  classical
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
  have hnEq : n = k+2 := by omega
  clear hk
  subst n
  rcases isEmpty_or_nonempty X with hE | hN
  · have hT0 : T.val = 0 := by
      funext b π
      by_cases hab : Admissible b π
      · have heq : b = fun _ => 0 := funext fun x => isEmptyElim x
        rw [heq]
        simpa using T.property.1.linearFirst (fun _ => 0) (fun _ => 0) π 0 0
          (BoundedLip.const 0) (BoundedLip.const 0) hab.2
      · exact T.property.1.offDomain b π hab
    refine ⟨⟨0,isIntegral_zero _⟩,compactlySupported_zero _,?_,?_⟩
    · rw [hT0]; exact boundarySucc_zero _
    · rw [show mass (0 : Functional X (k+2+1)) = 0 from mass_zero _]
      exact mul_nonneg (fillingCoefficient_pos (by omega)).le (Real.rpow_nonneg (mass_nonneg _) _)
  · obtain ⟨S,hS,hSc,hSb,hSm⟩ := proper_filling_bound hX T.property hTc hTz
    exact ⟨⟨S,hS⟩,hSc,hSb,hSm⟩
end CAT0Fillings
end

end OAI

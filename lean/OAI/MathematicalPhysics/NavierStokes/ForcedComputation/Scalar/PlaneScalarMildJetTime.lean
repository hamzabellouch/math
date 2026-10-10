import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildTimeEquation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetTimeDerivative

namespace OAI

/-! The scalar PDE holds as an ODE between successive finite spatial-jet spaces. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild
open ShearFlows Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

def laplacianJetCLM (k : ℕ) : Jet (k+2) →L[ℝ] Jet k :=
  ∑ j : Fin 2, (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k (Pi.single j 1)).comp
    (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ (k+1) (Pi.single j 1))

theorem function_laplacianJetCLM (k : ℕ) (J : Jet (k+2)) (x : Plane) :
    BoundedSpatialJets.function Plane ℝ k (laplacianJetCLM k J) x =
      ∑ j : Fin 2, PlaneHeat.spatialPartial ℝ j (PlaneHeat.spatialPartial ℝ j
        (BoundedSpatialJets.function Plane ℝ (k+2) J)) x := by
  let L : Jet k →L[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (BoundedSpatialJets.functionMap Plane ℝ k)
  change L ((laplacianJetCLM k) J) = _
  simp only [laplacianJetCLM, sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change BoundedSpatialJets.function Plane ℝ k
    (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k (Pi.single j 1)
      (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ (k+1) (Pi.single j 1) J)) x = _
  rw [BoundedSpatialJets.function_directionalDerivativeCLM]
  have he : (BoundedSpatialJets.function Plane ℝ (k+1)
      (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ (k+1) (Pi.single j 1) J) : Plane → ℝ) =
        PlaneHeat.spatialPartial ℝ j (BoundedSpatialJets.function Plane ℝ (k+2) J) := by
    funext y
    exact BoundedSpatialJets.function_directionalDerivativeCLM Plane ℝ (k+1) (Pi.single j 1) J y
  rw [he]
  rfl

namespace CompatibleData

def solutionJetValue {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (D : CompatibleData T)
    (k : ℕ) (s : ℝ) : Jet k := WeaklySingular.extendPath (Jet k) hT (D.solutionJet hT hν k) s

def timeRHSJet {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (D : CompatibleData T)
    (k : ℕ) (s : ℝ) : Jet k :=
  ν • laplacianJetCLM k (D.solutionJetValue hT hν (k+2) s) +
    WeaklySingular.extendPath (Jet k) hT (D.effectiveSource hT hν k) s

theorem solutionJetValue_continuous {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) : Continuous (D.solutionJetValue hT hν k) :=
  WeaklySingular.continuous_extendPath (Jet k) hT _

theorem timeRHSJet_continuous {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) : Continuous (D.timeRHSJet hT hν k) :=
  ((laplacianJetCLM k).continuous.comp (D.solutionJetValue_continuous hT hν (k+2))).const_smul ν |>.add
    (WeaklySingular.continuous_extendPath (Jet k) hT _)

theorem solutionJetValue_function {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) (s : ℝ) :
    (BoundedSpatialJets.function Plane ℝ k (D.solutionJetValue hT hν k s) : Plane → ℝ) =
      D.solutionValue hT hν s := by
  funext x
  exact D.solutionJet_function hT hν k (projIcc 0 T hT s) x

theorem timeRHSJet_function {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) (s : ℝ) (x : Plane) :
    BoundedSpatialJets.function Plane ℝ k (D.timeRHSJet hT hν k s) x =
      ν * ∑ j : Fin 2, PlaneHeat.spatialPartial ℝ j
        (PlaneHeat.spatialPartial ℝ j (D.solutionValue hT hν s)) x +
          D.effectiveSourceValue hT hν (projIcc 0 T hT s) x := by
  rw [timeRHSJet, BoundedSpatialJets.function_add, BoundedSpatialJets.function_smul,
    function_laplacianJetCLM, D.solutionJetValue_function]
  change _ + sourceValue hT k (D.effectiveSource hT hν k) s x = _
  rw [D.sourceValue_effectiveSource]
  rfl

/-- The time derivative exists in the full jet norm, including the two endpoints. -/
theorem solutionJetValue_hasDerivWithinAt {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (D.solutionJetValue hT hν k) (D.timeRHSJet hT hν k t)
      (Icc (0 : ℝ) T) t := by
  apply BoundedSpatialJets.hasDerivWithinAt_of_pointwise_derivative k _ _
    (D.solutionJetValue_continuous hT hν k) (D.timeRHSJet_continuous hT hν k) _ ht
  intro s hs x
  have hd := D.solutionValue_interior_equation hT hν hs x
  have he : (fun r => BoundedSpatialJets.function Plane ℝ k (D.solutionJetValue hT hν k r) x) =
      (fun r => D.solutionValue hT hν r x) := by
    funext r
    exact congrFun (D.solutionJetValue_function hT hν k r) x
  rw [he, D.timeRHSJet_function]
  exact hd

end CompatibleData
end ForcedComputation.PlaneScalarMild

end

end OAI

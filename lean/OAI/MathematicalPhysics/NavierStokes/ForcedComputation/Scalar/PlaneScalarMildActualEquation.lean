import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildJetTime
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarDuhamelCoefficients

namespace OAI

/-! The canonical mild solution satisfies the prescribed scalar drift equation. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild.CompatibleData
open ShearFlows Set VelocityDetector
open scoped Topology ContDiff BigOperators

theorem solutionValue_equation {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) {a : ℝ → Plane → Plane} {h : ℝ → Plane → ℝ}
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hsource : ∀ k t x, BoundedSpatialJets.function Plane ℝ k (D.source k t) x = h t.val x)
    (hcoeff : ∀ k i t x, BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t) x =
      driftCoefficients a i (t.val,x)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Plane) :
    HasDerivWithinAt (fun s => D.solutionValue hT hν s x)
      (scalarGenerator ν (a t) (D.solutionValue hT hν t) x + h t x) (Icc (0 : ℝ) T) t := by
  let L : Jet 0 →L[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (BoundedSpatialJets.functionMap Plane ℝ 0)
  have hd := L.hasFDerivAt.comp_hasDerivWithinAt t
    (D.solutionJetValue_hasDerivWithinAt hT hν 0 ht)
  have hf : (fun s => L (D.solutionJetValue hT hν 0 s)) =
      (fun s => D.solutionValue hT hν s x) := by
    funext s
    exact congrFun (D.solutionJetValue_function hT hν 0 s) x
  change HasDerivWithinAt (fun s => L (D.solutionJetValue hT hν 0 s)) _ _ _ at hd
  rw [hf] at hd
  have hs : D.effectiveSourceValue hT hν (projIcc 0 T hT t) x =
      h t x - fderiv ℝ (D.solutionValue hT hν t) x (a t x) := by
    have he := D.effectiveSource_function hT hν (Function.uncurry h) (driftCoefficients a)
      hsource hcoeff 0 (projIcc 0 T hT t) x
    change D.effectiveSourceValue hT hν (projIcc 0 T hT t) x = _ at he
    have hv : ((projIcc 0 T hT t : Icc (0 : ℝ) T) : ℝ) = t :=
      congrArg Subtype.val (projIcc_of_mem hT ht)
    simp only [hv, Function.uncurry_apply_pair, driftCoefficients_zero,
      driftCoefficients_succ] at he
    have hslice : ContDiff ℝ ∞ (a t) :=
      ha.comp (show ContDiff ℝ ∞ (fun x : Plane => (t,x)) from
        contDiff_const.prodMk contDiff_id)
    exact he.trans (driftCoefficients_effective_source hslice
      (D.solution_smooth hT hν (projIcc 0 T hT t)) (h t) x)
  have hr : L (D.timeRHSJet hT hν 0 t) =
      scalarGenerator ν (a t) (D.solutionValue hT hν t) x + h t x := by
    change BoundedSpatialJets.function Plane ℝ 0 (D.timeRHSJet hT hν 0 t) x = _
    rw [D.timeRHSJet_function, hs]
    change ν * scalarLaplacian (D.solutionValue hT hν t) x +
      (h t x - fderiv ℝ (D.solutionValue hT hν t) x (a t x)) = _
    unfold scalarGenerator
    ring
  rwa [hr] at hd

end ForcedComputation.PlaneScalarMild.CompatibleData

end

end OAI

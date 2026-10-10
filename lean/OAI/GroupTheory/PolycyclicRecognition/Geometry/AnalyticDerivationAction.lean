import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticDerivationFlow
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProductCoordinates

namespace OAI

/-! # Smooth real actions on polynomial exponential groups

Any derivation gives an action; nilpotence of the derivation is unnecessary.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem contDiff_analyticDerivationFlow (D : LieDerivation ℝ L L) :
    ContDiff ℝ ⊤ (fun p : ℝ × L => analyticDerivationFlow D p.1 p.2) := by
  have he : ContDiff ℝ ⊤ (NormedSpace.exp : (L →L[ℝ] L) → (L →L[ℝ] L)) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have ht : ContDiff ℝ ⊤ (fun p : ℝ × L =>
      p.1 • LinearMap.toContinuousLinearMap D.toLinearMap) :=
    contDiff_fst.smul_const _
  exact (he.comp ht).clm_apply contDiff_snd

namespace PolynomialExponentialCoordinates
variable [P : PolynomialExponentialCoordinates L]

def analyticDerivationAction (D : LieDerivation ℝ L L) : Multiplicative ℝ →* MulAut L where
  toFun t := groupAutomorphism (P := P) (analyticDerivationFlow D t.toAdd)
  map_one' := by
    apply DFunLike.ext
    intro x
    exact analyticDerivationFlow_zero D x
  map_mul' s t := by
    apply DFunLike.ext
    intro x
    exact analyticDerivationFlow_add D s.toAdd t.toAdd x

@[simp] theorem analyticDerivationAction_apply (D : LieDerivation ℝ L L)
    (t : Multiplicative ℝ) (x : L) :
    analyticDerivationAction (P := P) D t x = analyticDerivationFlow D t.toAdd x := rfl

theorem analyticDerivationAction_smooth (D : LieDerivation ℝ L L) :
    ContDiff ℝ ⊤ (fun p : ℝ × L =>
      analyticDerivationAction (P := P) D (Multiplicative.ofAdd p.1) p.2) :=
  contDiff_analyticDerivationFlow D

end PolynomialExponentialCoordinates
end PolycyclicRecognition

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealPhaseDerivative
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteFrameDifferentiation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraOneParameter

namespace OAI

/-! # Compact Cartan rotations as exponentials of their imaginary derivations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

/-- The imaginary derivation with the original model-space norm. -/
def tangentImaginaryOperator (h : H) : E →L[ℝ] E :=
  (show E →ₗ[ℝ] E from realImaginaryOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H h).toContinuousLinearMap

theorem tangentPhase_eq_exp (h : H) (t : ℝ) :
    (tangentTorusUnitAction H
      (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H (t • h)) : E →L[ℝ] E) =
      NormedSpace.exp (t • tangentImaginaryOperator H h) := by
  let L := GroupLieAlgebra (𝓘(ℝ,E)) G
  let R : ℝ → E →L[ℝ] E := fun s =>
    tangentTorusUnitAction H (realPhaseVector L H (s • h))
  let line : ℝ →ₗ[ℝ] H := LinearMap.toSpanSingleton ℝ H h
  let q := (realPhaseHom L H).comp line.toAddMonoidHom.toMultiplicative
  let U : Multiplicative ℝ →* (E →L[ℝ] E) :=
    (Units.coeHom (E →L[ℝ] E)).comp ((tangentTorusUnitAction H).comp q)
  have hR (s : ℝ) : R s = U (Multiplicative.ofAdd s) := rfl
  have hzero : R 0 = 1 := by
    rw [hR]
    exact U.map_one
  have hadd (s u : ℝ) : R (s+u) = R s * R u := by
    rw [hR, hR, hR]
    exact U.map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd u)
  have hd := (differentiableAt_clm_of_apply (A := R)
    (fun v => (hasDerivAt_realPhase_line H h v).differentiableAt)).hasDerivAt
  have he : deriv R 0 = tangentImaginaryOperator H h := by
    ext v
    have hv := hd.clm_apply (hasDerivAt_const (0 : ℝ) v)
    have hp := hasDerivAt_realPhase_line H h v
    have hh := hv.unique hp
    change (deriv R 0) v =
      (show E from realImaginaryOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H h v)
    simpa only [map_zero, add_zero] using hh
  rw [he] at hd
  exact oneParameter_eq_exp hzero hadd hd t

theorem tangentPhase_inv_eq_exp (h : H) :
    (tangentTorusUnitAction H
      (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹ : E →L[ℝ] E) =
      NormedSpace.exp (-tangentImaginaryOperator H h) := by
  have he : realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H (-h) =
      (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹ :=
    (realPhaseHom (GroupLieAlgebra (𝓘(ℝ,E)) G) H).map_inv (Multiplicative.ofAdd h)
  simpa only [neg_one_smul, he] using tangentPhase_eq_exp H h (-1)

end PolycyclicRecognition

end

end OAI

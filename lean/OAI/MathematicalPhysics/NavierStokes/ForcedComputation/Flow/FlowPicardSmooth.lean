import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowSuperposition
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowPathIntegral
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! Smooth Picard residual on a fixed unit interval.  The elapsed time is a
parameter, so evaluating the solution at the endpoint is a bounded linear map. -/

noncomputable section
namespace ForcedComputation.Flow
open Set
open scoped Topology ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

def picardResidual (Z : C(E, E)) (p : (ℝ × E) × C(UnitTime, E)) : C(UnitTime, E) :=
  p.2 - ContinuousLinearMap.const ℝ UnitTime p.1.2 -
    p.1.1 • primitivePathL (postcompose Z p.2)

theorem picardResidual_smooth (Z : C(E, E)) (hZ : ContDiff ℝ ∞ (Z : E → E)) :
    ContDiff ℝ ∞ (picardResidual Z) := by
  have ht : ContDiff ℝ ∞ (fun p : (ℝ × E) × C(UnitTime, E) => p.1.1) :=
    contDiff_fst.fst
  have hx : ContDiff ℝ ∞ (fun p : (ℝ × E) × C(UnitTime, E) => p.1.2) :=
    contDiff_fst.snd
  have hγ : ContDiff ℝ ∞ (fun p : (ℝ × E) × C(UnitTime, E) => p.2) := contDiff_snd
  exact (hγ.sub ((ContinuousLinearMap.const ℝ UnitTime).contDiff.comp hx)).sub
    (ht.smul ((primitivePathL (E := E)).contDiff.comp
      ((postcompose_contDiff Z hZ).comp hγ)))

def picardPathDerivative (Z : C(E, E)) (hZ : ContDiff ℝ ∞ (Z : E → E))
    (τ : ℝ) (γ : C(UnitTime, E)) : C(UnitTime, E) →L[ℝ] C(UnitTime, E) :=
  1 - τ • primitivePathL.comp
    (applyPath ⟨fun s => fderiv ℝ Z (γ s),
      (hZ.continuous_fderiv (by simp)).comp γ.continuous⟩)

theorem picardResidual_hasFDerivAt_path (Z : C(E, E))
    (hZ : ContDiff ℝ ∞ (Z : E → E)) (τ : ℝ) (x : E) (γ : C(UnitTime, E)) :
    HasFDerivAt (fun η => picardResidual Z ((τ, x), η))
      (picardPathDerivative Z hZ τ γ) γ := by
  have hs := postcompose_hasFDerivAt Z (hZ.of_le (by simp)) γ
  have hp := primitivePathL.hasFDerivAt.comp γ hs
  exact ((hasFDerivAt_id γ).sub_const (ContinuousLinearMap.const ℝ UnitTime x)).sub
    (hp.const_smul τ)

omit [FiniteDimensional ℝ E] in
theorem isInvertible_one_sub_of_norm_lt_one
    {A : C(UnitTime, E) →L[ℝ] C(UnitTime, E)} (hA : ‖A‖ < 1) :
    (1 - A).IsInvertible := by
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one (x := A) hA
  refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ _ u, ?_⟩
  exact hu

omit [FiniteDimensional ℝ E] in
theorem picardPathDerivative_invertible (Z : C(E, E))
    (hZ : ContDiff ℝ ∞ (Z : E → E)) {L τ : ℝ}
    (hL : 0 ≤ L) (hbound : ∀ x, ‖fderiv ℝ Z x‖ ≤ L)
    (hτ : |τ| * L < 1) (γ : C(UnitTime, E)) :
    (picardPathDerivative Z hZ τ γ).IsInvertible := by
  apply isInvertible_one_sub_of_norm_lt_one
  let A : C(UnitTime, E →L[ℝ] E) :=
    ⟨fun s => fderiv ℝ Z (γ s),
      (hZ.continuous_fderiv (by simp)).comp γ.continuous⟩
  have hA : ‖A‖ ≤ L := (ContinuousMap.norm_le _ hL).mpr fun s => hbound (γ s)
  calc
    ‖τ • primitivePathL.comp (applyPath A)‖
        ≤ |τ| * ‖primitivePathL.comp (applyPath A)‖ := by
      simpa only [Real.norm_eq_abs] using
        ContinuousLinearMap.opNorm_smul_le τ (primitivePathL.comp (applyPath A))
    _ ≤ |τ| * (‖primitivePathL (E := E)‖ * ‖applyPath A‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (abs_nonneg τ)
    _ ≤ |τ| * (1 * L) := by
      gcongr
      · exact primitivePathL_norm
      · exact (applyPath_norm A).trans hA
    _ < 1 := by simpa only [one_mul] using hτ

theorem picardResidual_partial (Z : C(E, E))
    (hZ : ContDiff ℝ ∞ (Z : E → E)) (τ : ℝ) (x : E) (γ : C(UnitTime, E)) :
    fderiv ℝ (picardResidual Z) ((τ, x), γ) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × E) C(UnitTime, E) =
        picardPathDerivative Z hZ τ γ := by
  have hp : HasFDerivAt (fun η : C(UnitTime, E) => ((τ, x), η))
      (ContinuousLinearMap.inr ℝ (ℝ × E) C(UnitTime, E)) γ := by
    simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
      ((ContinuousLinearMap.inr ℝ (ℝ × E) C(UnitTime, E)).hasFDerivAt (x := γ)).const_add
        ((τ, x), 0)
  have hd := ((picardResidual_smooth Z hZ).differentiable (by simp) ((τ, x), γ)).hasFDerivAt.comp γ hp
  exact hd.unique (picardResidual_hasFDerivAt_path Z hZ τ x γ)

/-- A short Picard solution belongs to a smooth local family of Picard solutions.
The family is obtained from the library implicit-function theorem. -/
theorem exists_local_picard_family (Z : C(E, E))
    (hZ : ContDiff ℝ ∞ (Z : E → E)) {L τ : ℝ}
    (hL : 0 ≤ L) (hbound : ∀ x, ‖fderiv ℝ Z x‖ ≤ L)
    (hτ : |τ| * L < 1) (x : E) (γ : C(UnitTime, E))
    (hγ : picardResidual Z ((τ, x), γ) = 0) :
    ∃ Γ : (ℝ × E) → C(UnitTime, E),
      ContDiffAt ℝ ∞ Γ (τ, x) ∧ Γ (τ, x) = γ ∧
        ∀ᶠ p in 𝓝 (τ, x), picardResidual Z (p, Γ p) = 0 := by
  have hc := (picardResidual_smooth Z hZ).contDiffAt (x := ((τ, x), γ))
  have hi : (fderiv ℝ (picardResidual Z) ((τ, x), γ) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × E) C(UnitTime, E)).IsInvertible := by
    rw [picardResidual_partial Z hZ]
    exact picardPathDerivative_invertible Z hZ hL hbound hτ γ
  refine ⟨hc.implicitFunction (by simp) hi,
    hc.contDiffAt_implicitFunction (by simp) hi,
    hc.implicitFunction_apply_self (by simp) hi, ?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with p hp
  exact hp.trans hγ

end ForcedComputation.Flow

end

end OAI

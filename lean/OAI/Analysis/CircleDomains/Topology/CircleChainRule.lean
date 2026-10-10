import OAI.Analysis.CircleDomains.Topology.CircleCovectors
import OAI.Analysis.CircleDomains.Sobolev.PlanarEnergyChange

namespace OAI

/-!
# Pullback of the intrinsic circle differential

The ordinary real chain rule applies to a local real lift. Independence
of that lift identifies the result with the intrinsic circle differential.
-/

open Set Filter Matrix
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem circleFDeriv_comp
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u : H → UnitAddCircle} {U : Set H} (hU : IsOpen U) (hu : SmoothCircleOn u U)
    {f : E → H} {x : E} (hf : DifferentiableAt ℝ f x) (hfx : f x ∈ U) :
    circleFDeriv (u ∘ f) x = (circleFDeriv u (f x)).comp (fderiv ℝ f x) := by
  let w := circleBranch u (circleCut u (f x))
  have hw : ContDiffAt ℝ ∞ w (f x) := hu (f x) hfx _ (circleCut_ne u (f x))
  have huc : ContinuousAt u (f x) := hu.continuousOn.continuousAt (hU.mem_nhds hfx)
  have hchain := (hw.differentiableAt (by simp)).hasFDerivAt.comp x hf.hasFDerivAt
  rw [circleFDeriv_eq_lift (huc.comp hf.continuousAt) (hw.continuousAt.comp hf.continuousAt)
    (u := w ∘ f) (Filter.Eventually.of_forall fun y => coe_circleBranch u _ (f y))]
  exact hchain.fderiv

theorem planeDerivativeMatrix_eq_columns (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    planeDerivativeMatrix A = !![(A (1, 0)).1, (A (0, 1)).1;
      (A (1, 0)).2, (A (0, 1)).2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeDerivativeMatrix, LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero,
      Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]

theorem real_covector_apply (L : (ℝ × ℝ) →L[ℝ] ℝ) (z : ℝ × ℝ) :
    L z = z.1 * L (1, 0) + z.2 * L (0, 1) := by
  have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
  calc
    L z = L (z.1 • (1, 0) + z.2 • (0, 1)) := congrArg L hz
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

theorem circleGradient_comp_vector
    {u : (ℝ × ℝ) → UnitAddCircle} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hu : SmoothCircleOn u U)
    {f : (ℝ × ℝ) → (ℝ × ℝ)} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) (hfx : f x ∈ U) :
    ![(circleGradient (u ∘ f) x).1, (circleGradient (u ∘ f) x).2] =
      (planeDerivativeMatrix (fderiv ℝ f x))ᵀ *ᵥ
        ![(circleGradient u (f x)).1, (circleGradient u (f x)).2] := by
  rw [planeDerivativeMatrix_eq_columns]
  simp only [circleGradient, circleFDeriv_comp hU hu hf hfx, ContinuousLinearMap.comp_apply]
  ext i
  fin_cases i
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      real_covector_apply (circleFDeriv u (f x)) (fderiv ℝ f x (1, 0))
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      real_covector_apply (circleFDeriv u (f x)) (fderiv ℝ f x (0, 1))

end CircleDomainRigidity.FiniteTransfer

end

end OAI

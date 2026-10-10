import OAI.Analysis.Mahler.SourceFullExterior

namespace OAI

open ContinuousAlternatingMap
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Taking the real part commutes with the actual exterior derivative. -/
theorem extDeriv_realPart {n : ℕ} {ω : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (hω : DifferentiableAt ℝ ω x) :
    extDeriv (fun y => Complex.reCLM.compContinuousAlternatingMap (ω y)) x =
      Complex.reCLM.compContinuousAlternatingMap (extDeriv ω x) := by
  have hr : DifferentiableAt ℝ (fun y => Complex.reCLM.compContinuousAlternatingMap (ω y)) x :=
    (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E ℂ ℝ (Fin n)
      Complex.reCLM).differentiableAt.comp x hω
  ext v
  rw [extDeriv_apply hr]
  change _ = Complex.reCLM (extDeriv ω x v)
  rw [extDeriv_apply hω, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [map_zsmul]
  congr 1
  have hd := Complex.reCLM.hasFDerivAt.comp x
    (hω.hasFDerivAt.continuousAlternatingMap_apply_const (p.removeNth v))
  rw [fderiv_continuousAlternatingMap_apply_const hω]
  exact congrArg (fun L : E →L[ℝ] ℝ => L (v p)) hd.fderiv

variable [FiniteDimensional ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem extDeriv_sourceRealBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) (v : Fin ((2*k+1)+1) → E) :
    extDeriv (sourceRealBoundaryForm u k) x v =
      (wedgePower (extDeriv (oneForm (dcLinear u)) x).toAlternatingMap (k+1)
        (fun s => v (sourceTopSlots k s))).re := by
  have hω : DifferentiableAt ℝ (sourceComplexBoundaryForm u k) x :=
    ((sourceReindexCLM (E := E) (sourceBoundarySlots k)).contDiff.contDiffAt.comp x
      (contDiffAt_sourceBoundaryForm hu k)).differentiableAt one_ne_zero
  change extDeriv (fun y => Complex.reCLM.compContinuousAlternatingMap
    (sourceComplexBoundaryForm u k y)) x v = _
  rw [extDeriv_realPart hω]
  exact congrArg (fun a => (a v).re) (extDeriv_sourceComplexBoundaryForm hu k)

end
end Mahler

end OAI

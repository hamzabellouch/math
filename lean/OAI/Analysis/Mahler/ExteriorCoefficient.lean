import OAI.Analysis.Mahler.WedgeOne
import OAI.Analysis.Mahler.ExteriorFlux

namespace OAI

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [Fintype J]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- Exterior differentiation of a scalar coefficient times an arbitrary
constant continuous form, in every degree and the actual shuffle convention. -/
theorem extDeriv_scalar_const [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (basis : Module.Basis J ℝ E) {n : ℕ}
    (B : E [⋀^Fin n]→L[ℝ] ℂ) {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    (extDeriv (fun y => f y • B) x).toAlternatingMap =
      (wedge (covectorVolume (fun _ : Fin 1 => (fderiv ℝ f x).toLinearMap))
        B.toAlternatingMap).domDomCongr (prependFinEquiv n) := by
  ext v
  rw [wedge_one_eval basis]
  change extDeriv (fun y => f y • B) x v = _
  rw [extDeriv_apply (hf.smul_const B)]
  apply Finset.sum_congr rfl
  intro i hi
  have he : fderiv ℝ (fun y => (f y • B) (i.removeNth v)) x (v i) =
      fderiv ℝ f x (v i) * B (i.removeNth v) := by
    simpa [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_comm] using
      congrArg (fun L : E →L[ℝ] ℂ => L (v i))
        (hf.hasFDerivAt.mul_const (B (i.removeNth v))).fderiv
  rw [he]
  simp [ContinuousLinearMap.coe_coe, zsmul_eq_mul, mul_assoc]

end Mahler

end OAI

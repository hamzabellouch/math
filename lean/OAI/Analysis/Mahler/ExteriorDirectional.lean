import OAI.Analysis.Mahler.ExteriorCoordinates

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
/-- The actual exterior derivative is the sum of coordinate one-forms wedged
with directional derivatives. No Leibniz rule is assumed. -/
theorem extDeriv_directional [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] (basis : Module.Basis J ℝ E) {n : ℕ}
    {A : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E} (hA : DifferentiableAt ℝ A x) :
    (extDeriv A x).toAlternatingMap =
      ∑ j : J, (wedge (covectorVolume (fun _ : Fin 1 => complexCoord basis j))
        (fderiv ℝ A x (basis j)).toAlternatingMap).domDomCongr (prependFinEquiv n) := by
  ext v
  simp only [alternating_sum_eval, wedge_one_eval basis, complexCoord_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  rw [extDeriv_apply hA, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have he : fderiv ℝ (fun y => A y (i.removeNth v)) x (v i) =
      fderiv ℝ A x (v i) (i.removeNth v) := by
    exact congrArg (fun L : E →L[ℝ] ℂ => L (v i))
      ((ContinuousAlternatingMap.apply ℝ E ℂ (i.removeNth v)).hasFDerivAt.comp x hA.hasFDerivAt).fderiv
  rw [he]
  conv_lhs => rw [← basis.sum_repr (v i)]
  simp only [map_sum, map_smul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, Complex.real_smul, Finset.smul_sum, zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

end Mahler

end OAI

import OAI.Geometry.NodalSets.Elliptic.RealFinCubePoincare
import OAI.Geometry.NodalSets.Elliptic.RealScaledCubeIntegration

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
open scoped ContDiff
noncomputable section

lemma real_affine_coordPartial (n : ℕ) (W : (Fin n → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (c : Fin n → ℝ) (r : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    Yau.coordPartial (fun y ↦ W (c+r • y)) x i = r*Yau.coordPartial W (c+r • x) i := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := r • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hd : HasFDerivAt (fun y ↦ c+r • y) L x := L.hasFDerivAt.const_add c
  have h := ((hW.differentiable (by simp) (c+r • x)).hasFDerivAt.comp x hd).fderiv
  simp only [Function.comp_def] at h
  simp [Yau.coordPartial,h,L]

theorem real_scaledCube_poincare (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (W : (Fin n → ℝ) → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realScaledCube n c r,
      (W x-(∫ y in realScaledCube n c r, W y)/(2*r)^n)^2) ≤
      4*r^2*(∫ x in realScaledCube n c r, ∑ i, (Yau.coordPartial W x i)^2) := by
  have hm : (∫ y in realScaledCube n c r, W y)/(2*r)^n =
      (∫ y in realFinCube n, W (c+r • y))/2^n := by
    rw [realScaledCube_integral n c hr,mul_pow]
    field_simp
  have h := real_finCube_poincare n (fun x ↦ W (c+r • x))
    (hW.comp (contDiff_const.add (contDiff_id.const_smul r)))
  simp_rw [real_affine_coordPartial n W hW,mul_pow,← Finset.mul_sum] at h
  rw [integral_const_mul] at h
  rw [hm,realScaledCube_integral n c hr,realScaledCube_integral n c hr]
  calc
    _ ≤ r^n*(4*(r^2*(∫ x in realFinCube n, ∑ i, (Yau.coordPartial W (c+r • x) i)^2))) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hr.le n)
    _ = _ := by ring

theorem real_scaledCube_poincare_integrable (n : ℕ) (c : Fin n → ℝ) (r : ℝ)
    (W : (Fin n → ℝ) → ℝ) (hW : ContDiff ℝ ∞ W) :
    IntegrableOn (fun x ↦ (W x-(∫ y in realScaledCube n c r, W y)/(2*r)^n)^2)
      (realScaledCube n c r) ∧
    IntegrableOn (fun x ↦ ∑ i, (Yau.coordPartial W x i)^2) (realScaledCube n c r) := by
  constructor
  · exact ((hW.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      (realScaledCube_isCompact n c r)
  · apply ContinuousOn.integrableOn_compact (realScaledCube_isCompact n c r)
    exact (continuous_finsetSum _ (fun i _ ↦ (Yau.real_coordPartial_smooth W hW i).continuous.pow 2)).continuousOn

end
end Yau.Geometry

end OAI

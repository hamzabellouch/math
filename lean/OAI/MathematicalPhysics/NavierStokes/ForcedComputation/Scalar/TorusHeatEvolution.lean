import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarBounds

namespace OAI

/-! Consequences of the heat representation used during the detector waits:
mass bounds for a nonnegative bump, linear splitting, and propagation of a
uniform error estimate. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff

theorem torusHeatEvolution_nonnegative {g : Plane → ℝ} (hg : ∀ x, 0 ≤ g x)
    (t : ℝ) (x : Plane) : 0 ≤ torusHeatEvolution g t x := by
  unfold torusHeatEvolution
  split_ifs with ht
  · exact hg x
  · exact integral_nonneg (fun y => mul_nonneg (torusHeatKernel_nonneg (lt_of_not_ge ht) _)
      (hg y))

theorem torusHeatEvolution_add (hK : TorusHeatInput) {g h : Plane → ℝ}
    (hg : Continuous g) (hh : Continuous h) (t : ℝ) (x : Plane) :
    torusHeatEvolution (fun y => g y + h y) t x =
      torusHeatEvolution g t x + torusHeatEvolution h t x := by
  unfold torusHeatEvolution
  split_ifs with ht
  · rfl
  · have hc : Continuous (fun y => torusHeatKernel t (x - y)) :=
      (hK.continuous t (lt_of_not_ge ht)).comp (continuous_const.sub continuous_id)
    simp_rw [mul_add]
    exact integral_add (hc.mul hg).integrableOn_Icc (hc.mul hh).integrableOn_Icc

theorem torusHeatEvolution_mass_bound (hK : TorusHeatInput) {g : Plane → ℝ}
    (hg : Continuous g) (hg₀ : ∀ x, 0 ≤ g x) {t H : ℝ} (ht : 0 < t) (x : Plane)
    (hbound : ∀ y ∈ Icc (0 : Plane) (fun _ => 1),
      g y ≠ 0 → torusHeatKernel t (x - y) ≤ H) :
    torusHeatEvolution g t x ≤ H * ∫ y in Icc (0 : Plane) (fun _ => 1), g y := by
  have hc : Continuous (fun y => torusHeatKernel t (x - y)) :=
    (hK.continuous t ht).comp (continuous_const.sub continuous_id)
  rw [torusHeatEvolution, ite_eq_right (not_le.mpr ht), ← integral_const_mul]
  apply setIntegral_mono_on (hc.mul hg).integrableOn_Icc
    (hg.const_mul H).integrableOn_Icc measurableSet_Icc
  intro y hy
  change torusHeatKernel t (x - y) * g y ≤ H * g y
  by_cases hz : g y = 0
  · simp only [hz, mul_zero, le_refl]
  · exact mul_le_mul_of_nonneg_right (hbound y hy hz) (hg₀ y)

theorem torusHeatEvolution_after_one (hK : TorusHeatInput) {g : Plane → ℝ}
    (hg : Continuous g) (hg₀ : ∀ x, 0 ≤ g x) {t : ℝ} (ht : 1 ≤ t) (x : Plane) :
    torusHeatEvolution g t x ≤ 16 * ∫ y in Icc (0 : Plane) (fun _ => 1), g y :=
  torusHeatEvolution_mass_bound hK hg hg₀ (by linarith) x
    (fun y _ _ => torusHeatKernel_after_one hK ht (x - y))

theorem torusHeatEvolution_error_bound (hK : TorusHeatInput) {g : Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hp : PlanePeriodic g) {E : ℝ} (hE : ∀ x, |g x| ≤ E)
    {t : ℝ} (ht : 0 ≤ t) (x : Plane) : |torusHeatEvolution g t x| ≤ E := by
  have hb := (hK.solution t ht g hg hp).absolute_bound ht (by norm_num)
    (M := E) (A := 0) (fun _ _ _ => by simp) hE t ⟨ht, le_rfl⟩ x
  simpa only [zero_mul, add_zero] using hb

end ForcedComputation.VelocityDetector

end

end OAI

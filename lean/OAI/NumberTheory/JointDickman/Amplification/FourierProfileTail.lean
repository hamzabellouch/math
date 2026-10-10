import OAI.NumberTheory.JointDickman.Amplification.SchwartzFourierProfile

namespace OAI

/-! # Quantitative tail bounds from the fixed Fourier profile's moments -/

namespace JointDickman
open MeasureTheory
open scoped SchwartzMap

theorem norm_integral_tail_le_moment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) (k : ℕ)
    (hk : Integrable (fun x : ℝ => |x|^k*‖f x‖)) {R : ℝ} (hR : 0 < R) :
    (∫ x in {x : ℝ | R < |x|}, ‖f x‖) ≤ (R^k)⁻¹*(∫ x : ℝ, |x|^k*‖f x‖) := by
  let S : Set ℝ := {x | R < |x|}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hpoint (x : ℝ) (hx : x ∈ S) : ‖f x‖ ≤ (R^k)⁻¹*(|x|^k*‖f x‖) := by
    have hp : R^k ≤ |x|^k := pow_le_pow_left₀ hR.le hx.le k
    calc
      _ = (R^k)⁻¹*(R^k*‖f x‖) := by rw [inv_mul_cancel_left₀ (pow_pos hR k).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) (inv_nonneg.mpr (pow_nonneg hR.le k))
  calc
    _ ≤ ∫ x in S, (R^k)⁻¹*(|x|^k*‖f x‖) :=
      setIntegral_mono_on hf.norm.integrableOn (hk.const_mul _).integrableOn hS hpoint
    _ = (R^k)⁻¹*(∫ x in S, |x|^k*‖f x‖) := integral_const_mul _ _
    _ ≤ (R^k)⁻¹*(∫ x : ℝ, |x|^k*‖f x‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_le_integral hk (Filter.Eventually.of_forall (fun x => by positivity))

theorem schwartz_testFourier_tail (w : 𝓢(ℝ, ℝ)) (k : ℕ) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in {ξ : ℝ | R < |ξ|}, ‖testFourierTransform w ξ‖) ≤
      (R^k)⁻¹*(∫ ξ : ℝ, |ξ|^k*‖testFourierTransform w ξ‖) :=
  norm_integral_tail_le_moment (schwartz_testFourier_integrable w) k
    (schwartz_testFourier_moment w k) hR

theorem schwartz_testFourier_linear_moment (w : 𝓢(ℝ, ℝ)) :
    Integrable (fun ξ : ℝ => ‖testFourierTransform w ξ‖*(1+|ξ|)) := by
  have h0 := schwartz_testFourier_moment w 0
  have h1 := schwartz_testFourier_moment w 1
  apply (h0.add h1).congr
  exact Filter.Eventually.of_forall (fun ξ => by
    simp only [Pi.add_apply,pow_zero,one_mul,pow_one]
    ring)

end JointDickman

end OAI

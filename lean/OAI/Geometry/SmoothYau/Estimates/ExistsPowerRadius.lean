import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.SphereProjection

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
lemma exists_power_radius (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    ∃ z : ℂ, Complex.normSq z = r^2 ∧ (z^n).im ≠ 0 := by
  let θ : ℝ := Real.pi / (2 * (n:ℝ))
  let z : ℂ := (r:ℂ) * Complex.exp ((θ:ℂ)*Complex.I)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hθ : (n:ℝ)*θ = Real.pi/2 := by dsimp [θ]; field_simp
  have hpow : z^n = (r^n:ℝ)*Complex.I := by
    rw [show z = (r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) from rfl,mul_pow,
      ←Complex.exp_nat_mul]
    have he : (n:ℂ)*((θ:ℂ)*Complex.I) = ((Real.pi/2:ℝ):ℂ)*Complex.I := by
      rw [←mul_assoc,←Complex.ofReal_natCast,←Complex.ofReal_mul,hθ]
    rw [he,Complex.exp_ofReal_mul_I]
    simp
  refine ⟨z,?_,?_⟩
  · rw [show z = (r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) from rfl,map_mul]
    rw [Complex.normSq_ofReal]
    have he : Complex.normSq (Complex.exp ((θ:ℂ)*Complex.I)) = 1 := by
      rw [Complex.normSq_apply,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [he,mul_one]
    ring
  · rw [hpow]
    simpa only [Complex.mul_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,
      ←Complex.ofReal_pow,Complex.ofReal_re] using (pow_pos hr n).ne'
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma planar_sphere_point (a b c : E)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (z : ℂ) (hz : Complex.normSq z ≤ 1) :
    ∃ p : E, ‖p‖ = 1 ∧ planarLinear a b p = z := by
  let p := z.re • a + z.im • b + Real.sqrt (1-Complex.normSq z) • c
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  have hca : inner ℝ c a = 0 := (real_inner_comm a c).trans hac
  have hcb : inner ℝ c b = 0 := (real_inner_comm b c).trans hbc
  have hpp : inner ℝ p p = 1 := by
    simp only [p,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
      ha,hb,hc,hab,hac,hbc,hba,hca,hcb,conj_trivial,mul_zero,mul_one,zero_add,add_zero]
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr hz),Complex.normSq_apply z]
  refine ⟨p,?_,?_⟩
  · rw [real_inner_self_eq_norm_sq] at hpp
    nlinarith [norm_nonneg p]
  · simp only [planarLinear_apply,p,inner_add_right,inner_smul_right,
      ha,hb,hab,hac,hbc,hba,mul_one,mul_zero,add_zero,zero_add]
    simpa only [mul_comm Complex.I] using Complex.re_add_im z
end YauCounterexamples


end

end OAI

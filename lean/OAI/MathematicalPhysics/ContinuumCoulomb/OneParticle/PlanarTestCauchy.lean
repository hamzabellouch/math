import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarGroundIdentity

namespace OAI

/-! The integral Cauchy–Schwarz estimate used in the planar ground-state
duality argument, on actual compact real test functions. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem planar_toLp_inner (f g : PlanarPosition → ℝ)
    (hf : MemLp f 2) (hg : MemLp g 2) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x*g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  rw [hx,hy,RCLike.inner_apply,conj_trivial]
  ring

private theorem planar_toLp_sq (f : PlanarPosition → ℝ) (hf : MemLp f 2) :
    ‖hf.toLp f‖^2 = ∫ x, f x^2 := by
  rw [← real_inner_self_eq_norm_sq,planar_toLp_inner f f hf hf]
  simp only [pow_two]

theorem planar_test_cauchy_square (f g : PlanarPosition → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x, f x*g x)^2 ≤ (∫ x, f x^2)*(∫ x, g x^2) := by
  have hfi : MemLp f 2 := hf.memLp_of_hasCompactSupport hfc
  have hgi : MemLp g 2 := hg.memLp_of_hasCompactSupport hgc
  have h := (sq_le_sq₀ (abs_nonneg (inner ℝ (hfi.toLp f) (hgi.toLp g)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (abs_real_inner_le_norm (hfi.toLp f) (hgi.toLp g))
  simpa only [sq_abs,mul_pow,planar_toLp_inner,planar_toLp_sq] using h

end ContinuumCoulomb

end

end OAI

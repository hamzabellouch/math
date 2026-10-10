import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles
import Mathlib.Tactic.Group

namespace OAI

/-! # Exact basepoint changes for the sampled height profiles -/

namespace PolycyclicRecognition

/-- A change of ambient basepoint by `u d` conjugates the nilpotent sample
and left translates the Cartan sample. Factor overlap is allowed. -/
theorem factor_basepoint_change
    {N D G : Type*} [Group N] [Group D] [Group G]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (u a : N) (d z : D) :
    (x * (ι u * κ d)) * ι (φ d⁻¹ (u⁻¹ * a)) * κ (d⁻¹ * z) =
      x * ι a * κ z := by
  rw [hconj, map_inv, map_mul, map_inv, map_mul, map_inv]
  group

/-- Matched sample points have exactly the same unnormalized value.
Only the two deterministic center values differ. -/
theorem rescaled_profile_basepoint_change
    {G W Z Z' : Type*} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : G → W) (x y a b : G) (φ : Z → G) (ψ : Z' → G)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : Z) (z' : Z')
    (hpoint : x * a * φ z = y * b * ψ z') :
    r • rescaledMapProfile J x a (Real.log r) φ z =
      s • rescaledMapProfile J y b (Real.log s) ψ z' + (J y - J x) := by
  simp only [rescaledMapProfile, Real.exp_log hr, Real.exp_log hs, smul_smul,
    mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ hs.ne', one_smul]
  rw [hpoint]
  abel

end PolycyclicRecognition

end OAI

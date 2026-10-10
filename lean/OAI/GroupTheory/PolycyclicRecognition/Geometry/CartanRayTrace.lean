import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConeHeightMultiplier
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PositiveWeightCones

namespace OAI

/-! # The actual boundary trace is a positive multiple of its generator ray -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The positive pure-word multiplicities in a ray quotient identify its
Haar trace with a strictly positive multiple of the chosen height ray. -/
theorem ray_height_trace_pos_multiple
    (j : Fin M.letterCount) (c : Fin M.letterCount → ℕ)
    (hout : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay
      (M.weight j : H →ₗ[ℝ] ℝ) → c i = 0)
    (hcj : 0 < c j) :
    ∃ r : ℝ, 0 < r ∧
      (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp eW.symm.toLinearMap =
        r • (cartanHeightWeight T H (M.weight j)).comp eW.symm.toLinearMap := by
  obtain ⟨r, hr, he⟩ := positive_sum_on_weightRay
    (M.weight j : H →ₗ[ℝ] ℝ) (fun i => (M.weight i : H →ₗ[ℝ] ℝ)) c hout j
    (positiveWeightRay_self _) hcj
  refine ⟨r, hr, ?_⟩
  ext w
  have hh := LinearMap.congr_fun he (cartanHeightSection T H (eW.symm w))
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, cartanHeightWeight, LinearEquiv.coe_coe] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI

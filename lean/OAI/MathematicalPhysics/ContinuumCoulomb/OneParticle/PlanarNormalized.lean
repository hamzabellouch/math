import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarResolventEquation

namespace OAI

/-! Analytic identities for the actual normalized planar mode. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_const_mul {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℝ) (e r : PlanarPosition) :
    planarPartial (fun x => c * f x) e r = c * planarPartial f e r := by
  unfold planarPartial
  rw [fderiv_const_mul (hf.differentiable (by norm_num) r) c]
  rfl

theorem planarLaplacian_const_mul {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (r : PlanarPosition) :
    planarLaplacian (fun x => c * f x) r = c * planarLaplacian f r := by
  have h (e : PlanarPosition) : planarPartial (fun x => c * f x) e =
      fun x => c * planarPartial f e x :=
    funext (planarPartial_const_mul (hf.of_le (by norm_num)) c e)
  simp only [planarLaplacian]
  simp_rw [h]
  simp_rw [planarPartial_const_mul (planarPartial_C1 hf _)]
  exact (Finset.mul_sum _ _ _).symm

theorem normalizedPlanarMode_eq_const_mul : normalizedPlanarMode =
    fun r => (Real.sqrt (∫ s, planarResolventMode s ^ 2))⁻¹ * planarResolventMode r := by
  funext r
  simp only [normalizedPlanarMode, div_eq_mul_inv, mul_comm]

theorem normalizedPlanarMode_square_integrable :
    Integrable (fun r => normalizedPlanarMode r ^ 2) := by
  simp_rw [normalizedPlanarMode, div_pow]
  exact planarResolventMode_square_integrable.div_const _

theorem normalizedPlanarMode_memLp : MemLp normalizedPlanarMode 2 :=
  (memLp_two_iff_integrable_sq normalizedPlanarMode_C7.continuous.aestronglyMeasurable).mpr
    normalizedPlanarMode_square_integrable

theorem normalizedPlanarMode_eigen_equation (r : PlanarPosition) :
    planarLaplacian normalizedPlanarMode r =
      (2 * manufacturedPlanarWell r + 1) * normalizedPlanarMode r := by
  rw [normalizedPlanarMode_eq_const_mul,
    planarLaplacian_const_mul (planarResolventMode_C7.of_le (by norm_num)),
    manufacturedPlanarWell_eigen_equation]
  ring

theorem planarPartial_translate (f : PlanarPosition → ℝ) (u e r : PlanarPosition) :
    planarPartial (fun x => f (x - u)) e r = planarPartial f e (r - u) := by
  simp only [planarPartial, fderiv_comp_sub]

theorem planarLaplacian_translate (f : PlanarPosition → ℝ) (u r : PlanarPosition) :
    planarLaplacian (fun x => f (x - u)) r = planarLaplacian f (r - u) := by
  have h (e : PlanarPosition) : planarPartial (fun x => f (x - u)) e =
      fun x => planarPartial f e (x - u) := funext (planarPartial_translate f u e)
  simp only [planarLaplacian]
  simp_rw [h, planarPartial_translate]

end ContinuumCoulomb

end

end OAI

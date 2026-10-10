import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeH1

namespace OAI

/-! The actual manufactured planar mode attains energy `-1/2`.
The integration by parts uses its proved square-integrable first and second
derivatives, rather than imposing an eigenvalue or normalization hypothesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarResolventMode_partial_memLp (e : PlanarPosition) :
    MemLp (planarPartial planarResolventMode e) 2 :=
  (memLp_two_iff_integrable_sq
    (planarPartial_continuous (planarResolventMode_C7.of_le (by norm_num)) e).aestronglyMeasurable).mpr
      (planarResolventMode_partial_square_integrable e)

theorem planarResolventMode_second_memLp (e : PlanarPosition) :
    MemLp (planarPartial (planarPartial planarResolventMode e) e) 2 :=
  (memLp_two_iff_integrable_sq
    (planarPartial_continuous (planarPartial_C1 (planarResolventMode_C7.of_le (by norm_num)) e)
      e).aestronglyMeasurable).mpr (planarResolventMode_partial_partial_square_integrable e e)

theorem planarResolventMode_energy_ibp (e : PlanarPosition) :
    (∫ x, planarResolventMode x * planarPartial (planarPartial planarResolventMode e) e x) =
      -(∫ x, planarPartial planarResolventMode e x ^ 2) := by
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (planarResolventMode_partial_memLp e |>.integrable_mul (planarResolventMode_partial_memLp e))
    (planarResolventMode_memLp.integrable_mul (planarResolventMode_second_memLp e))
    (planarResolventMode_memLp.integrable_mul (planarResolventMode_partial_memLp e))
    (fun x _ => (planarResolventMode_C7.differentiable (by norm_num)) x)
    (fun x _ => (planarPartial_C1 (planarResolventMode_C7.of_le (by norm_num)) e).differentiable
      (by norm_num) x)
  simpa only [planarPartial, pow_two] using hi

theorem planarResolventMode_energy :
    planarTestForm manufacturedPlanarWell planarResolventMode =
      -(1 / 2 : ℝ) * ∫ x, planarResolventMode x ^ 2 := by
  have hi (a : Fin 2) : Integrable (fun x => planarResolventMode x *
      planarPartial (planarPartial planarResolventMode (planarAxis a)) (planarAxis a) x) :=
    planarResolventMode_memLp.integrable_mul (planarResolventMode_second_memLp (planarAxis a))
  have hsum : (∫ x, planarResolventMode x * planarLaplacian planarResolventMode x) =
      -(∑ a : Fin 2, ∫ x, planarPartial planarResolventMode (planarAxis a) x ^ 2) := by
    simp only [planarLaplacian, Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun a _ => hi a)]
    simp only [planarResolventMode_energy_ibp, Finset.sum_neg_distrib]
  have hpot : Integrable (fun x => manufacturedPlanarWell x * planarResolventMode x ^ 2) :=
    (manufacturedPlanarWell_C7.continuous.mul (planarResolventMode_C7.continuous.pow 2)).integrable_of_hasCompactSupport
      manufacturedPlanarWell_hasCompactSupport.mul_right
  have heq : (∫ x, planarResolventMode x * planarLaplacian planarResolventMode x) =
      2 * (∫ x, manufacturedPlanarWell x * planarResolventMode x ^ 2) +
        ∫ x, planarResolventMode x ^ 2 := by
    simp_rw [manufacturedPlanarWell_eigen_equation]
    rw [show (fun x => planarResolventMode x * ((2 * manufacturedPlanarWell x + 1) * planarResolventMode x)) =
      (fun x => 2 * (manufacturedPlanarWell x * planarResolventMode x ^ 2) + planarResolventMode x ^ 2)
      from by funext x; ring]
    rw [integral_add (hpot.const_mul 2) planarResolventMode_square_integrable, integral_const_mul]
  unfold planarTestForm
  linarith

end ContinuumCoulomb

end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarTestCauchy

namespace OAI

/-! A compact-test distributional gradient is controlled by the exact
ground-state energy. This estimate survives closure of the Sobolev graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planar_ground_dual_bound (u ψ : PlanarPosition → ℝ)
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (a : Fin 2) :
    (∫ x, planarGroundQuotient u x*planarPartial ψ (planarAxis a) x)^2 ≤
      (∫ x, (ψ x/planarResolventMode x)^2)*
        (2*planarTestForm manufacturedPlanarWell u+∫ x, u x^2) := by
  let v := planarGroundQuotient u
  have hv : ContDiff ℝ 1 v := planarGroundQuotient_C1 hu
  have hvc : HasCompactSupport v := planarGroundQuotient_compact huc
  have hdc : HasCompactSupport (planarPartial v (planarAxis a)) :=
    hvc.fderiv_apply ℝ _
  have hd : Continuous (planarPartial v (planarAxis a)) := planarPartial_continuous hv _
  have hψd : Continuous (planarPartial ψ (planarAxis a)) := planarPartial_continuous hψ _
  have hiA : Integrable (fun x => planarPartial v (planarAxis a) x*ψ x) :=
    (hd.mul hψ.continuous).integrable_of_hasCompactSupport hdc.mul_right
  have hiB : Integrable (fun x => v x*planarPartial ψ (planarAxis a) x) :=
    (hv.continuous.mul hψd).integrable_of_hasCompactSupport hvc.mul_right
  have hiFG : Integrable (fun x => v x*ψ x) :=
    (hv.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hvc.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hiA hiB hiFG
    (fun x _ => hv.differentiable (by norm_num) x)
    (fun x _ => hψ.differentiable (by norm_num) x)
  change (∫ x, v x*planarPartial ψ (planarAxis a) x) =
    -(∫ x, planarPartial v (planarAxis a) x*ψ x) at hibp
  let F := fun x => planarResolventMode x*planarPartial v (planarAxis a) x
  let G := fun x => ψ x/planarResolventMode x
  have hF : Continuous F := planarResolventMode_C7.continuous.mul hd
  have hG : Continuous G := hψ.continuous.div planarResolventMode_C7.continuous
    (fun x => (planarResolventMode_positive x).ne')
  have hFc : HasCompactSupport F := hdc.mul_left
  have hGc : HasCompactSupport G := planarGroundQuotient_compact hψc
  have he (x : PlanarPosition) : F x*G x = planarPartial v (planarAxis a) x*ψ x := by
    dsimp [F,G]
    field_simp [(planarResolventMode_positive x).ne']
  have hCS := planar_test_cauchy_square F G hF hG hFc hGc
  simp_rw [he] at hCS
  have hf2 : (∫ x, F x^2) =
      ∫ x, planarResolventMode x^2*planarPartial v (planarAxis a) x^2 := by
    simp only [F,mul_pow]
  rw [hf2] at hCS
  have hsingle : (∫ x, planarResolventMode x^2*planarPartial v (planarAxis a) x^2) ≤
      2*planarTestForm manufacturedPlanarWell u+∫ x, u x^2 := by
    rw [← planarGroundQuotient_energy u hu huc]
    apply Finset.single_le_sum (f := fun b : Fin 2 => ∫ x : PlanarPosition,
      planarResolventMode x^2*planarPartial v (planarAxis b) x^2)
    · intro b _
      exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · exact Finset.mem_univ a
  have hn : 0 ≤ ∫ x, G x^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hb := hCS.trans (mul_le_mul_of_nonneg_right hsingle hn)
  change (∫ x, v x*planarPartial ψ (planarAxis a) x)^2 ≤ _
  rw [hibp,neg_sq]
  exact hb.trans_eq (mul_comm _ _)

end ContinuumCoulomb

end

end OAI

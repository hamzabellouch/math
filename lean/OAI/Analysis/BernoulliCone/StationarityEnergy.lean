import OAI.Analysis.BernoulliCone.HalfspaceUnitSlope

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Shape
variable {d : ℕ}

lemma general_energy_pullback_upper {u φ : Space d → ℝ} {L C : ℝ≥0}
    (huLip : LipschitzWith L u)
    (hφ : ContDiff ℝ ∞ φ) (hLip : LipschitzWith C φ)
    (e : Space d) (t : ℝ)
    (hdet : ∀ x, (1:ℝ)/2 ≤ 1+t*fderiv ℝ φ x e)
    (g : Space d ≃ₜ Space d) (hg : ∀ y, g y=deform φ e t y)
    (a : Space d) (R : ℝ) (hfix : ∀ x ∉ ball a R, φ x=0) :
    energy (ball a R) (fun y => u (g.symm y))
        (gradient (fun y => u (g.symm y))) ≤
      energy (ball a R) (u) (gradient (u)) +
        t*(∫ x in ball a R, stressTerm u φ e x) +
        t^2*(2*(L:ℝ)^2*‖e‖^2*C^2)*(volume (ball a R)).toReal := by
  let : IsFiniteMeasure (volume.restrict (ball a R)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
  let v := fun y => u (g.symm y)
  have him : g '' ball a R=ball a R := image_eq_of_fixed_compl g _ (by
    intro x hx
    rw [hg]
    simp [deform,hfix x hx])
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul (s:=ball a R) volume measurableSet_ball
    (f:=g) (f':=fun x => rankOneMap (fderiv ℝ φ x) e t)
    (fun x _ => (show HasFDerivAt g (rankOneMap (fderiv ℝ φ x) e t) x from by
      rw [show (g : Space d → Space d)=deform φ e t from funext hg]
      exact hasFDerivAt_deform ((hφ.differentiable (by simp)) x).hasFDerivAt e t).hasFDerivWithinAt) (g.injective.injOn) (density v)
  rw [him] at hchange
  have hdetpos (x : Space d) : 0 ≤ 1+t*fderiv ℝ φ x e := le_trans (by norm_num) (hdet x)
  simp_rw [rankOneMap_det,abs_of_nonneg (hdetpos _),smul_eq_mul] at hchange
  change energy (ball a R) v (gradient v) = _ at hchange
  rw [hchange]
  have hi : Integrable (fun x => density (u) x+t*stressTerm u φ e x+
      t^2*(2*(L:ℝ)^2*‖e‖^2*C^2)) (volume.restrict (ball a R)) := by
    convert ((density_integrable_ball huLip a R).add
    ((stressTerm_integrable_ball huLip hLip e a R).const_mul (t))).add
      (integrable_const (t^2*(2*(L:ℝ)^2*‖e‖^2*C^2))) using 1; rfl
  have hm := integral_mono_of_nonneg
    (μ:=volume.restrict (ball a R))
    (f:=fun x => (1+t*fderiv ℝ φ x e)*density v (g x))
    (g:=fun x => density (u) x+t*stressTerm u φ e x+
      t^2*(2*(L:ℝ)^2*‖e‖^2*C^2))
    (Eventually.of_forall (fun x => mul_nonneg (hdetpos x) (density_nonneg v (g x)))) hi
    (by
      filter_upwards [ae_restrict_of_ae huLip.ae_differentiableAt] with x hx
      exact stress_density_bound hx huLip ((hφ.differentiable (by simp)) x) hLip e t (hdet x) g hg)
  have hiE := density_integrable_ball huLip a R
  have hiF := (stressTerm_integrable_ball huLip hLip e a R).const_mul (t)
  have hsum : (∫ x in ball a R, density (u) x+t*stressTerm u φ e x+
      t^2*(2*(L:ℝ)^2*‖e‖^2*C^2)) =
      energy (ball a R) (u) (gradient (u)) +
        t*(∫ x in ball a R, stressTerm u φ e x) +
        t^2*(2*(L:ℝ)^2*‖e‖^2*C^2)*(volume (ball a R)).toReal := by
    have hadd := integral_add (hiE.add hiF) (integrable_const (t^2*(2*(L:ℝ)^2*‖e‖^2*C^2)))
    have hadd2 := integral_add hiE hiF
    simp only [Pi.add_apply] at hadd
    rw [hadd2,integral_const_mul,integral_const] at hadd
    convert hadd using 1; first | rfl | (simp only [Measure.restrict_apply_univ,Measure.real,smul_eq_mul]; dsimp [energy,density]; ring)
  rw [hsum] at hm
  exact hm
end Bernoulli.Shape

end
end

end OAI

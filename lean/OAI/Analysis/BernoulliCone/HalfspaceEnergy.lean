import OAI.Analysis.BernoulliCone.RankOneDeterminant

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Shape
variable {d : ℕ}

lemma inner_ne_zero_ae {e : Space d} (he : e ≠ 0) :
    ∀ᵐ x ∂volume, inner ℝ e x ≠ 0 := by
  let a := innerSL ℝ e
  have ha : a ≠ 0 := by
    intro hh
    have hx : inner ℝ e e=0 := by
      have h := congrArg (fun f : Space d →L[ℝ] ℝ => f e) hh
      simpa [a] using h
    exact he ((inner_self_eq_zero).mp hx)
  have hker : volume (LinearMap.ker a.toLinearMap : Set (Space d))=0 := by
    apply Measure.addHaar_submodule
    rw [Ne,LinearMap.ker_eq_top]
    intro hh
    exact ha (ContinuousLinearMap.coe_injective hh)
  rw [ae_iff]
  change volume {x | ¬ inner ℝ e x ≠ 0}=0
  change volume {x | inner ℝ e x=0}=0 at hker
  simpa only [not_not] using hker

lemma density_integrable_ball {u : Space d → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u)
    (a : Space d) (R : ℝ) : IntegrableOn (density u) (ball a R) := by
  let : IsFiniteMeasure (volume.restrict (ball a R)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
  have hh := LipschitzSobolev.h1_ball hu a R
  exact (hh.2.1.integrable_norm_pow (by norm_num)).add (integrable_phase hh.1.aestronglyMeasurable)

lemma firstTerm_integrable_ball {φ : Space d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e a : Space d) (R : ℝ) : IntegrableOn (firstTerm φ e) (ball a R) := by
  have hc : Continuous (fun x => fderiv ℝ φ x e) := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi : IntegrableOn (fun x => fderiv ℝ φ x e) (ball a R) volume :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall a R)).mono_set ball_subset_closedBall
  have hpos : MeasurableSet {x : Space d | 0 < inner ℝ e x} :=
    (isOpen_lt continuous_const (innerSL ℝ e).continuous).measurableSet
  exact hi.indicator hpos

lemma energy_pullback_upper {φ : Space d → ℝ} {C : ℝ≥0}
    (hφ : ContDiff ℝ ∞ φ) (hLip : LipschitzWith C φ)
    {e : Space d} (he : e ≠ 0) (t : ℝ)
    (hdet : ∀ x, (1:ℝ)/2 ≤ 1+t*fderiv ℝ φ x e)
    (g : Space d ≃ₜ Space d) (hg : ∀ y, g y=deform φ e t y)
    (a : Space d) (R : ℝ) (hfix : ∀ x ∉ ball a R, φ x=0) :
    energy (ball a R) (fun y => positiveLinear e (g.symm y))
        (gradient (fun y => positiveLinear e (g.symm y))) ≤
      energy (ball a R) (positiveLinear e) (gradient (positiveLinear e)) +
        t*(1-‖e‖^2)*(∫ x in ball a R, firstTerm φ e x) +
        t^2*(2*‖e‖^4*C^2)*(volume (ball a R)).toReal := by
  let : IsFiniteMeasure (volume.restrict (ball a R)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
  let v := fun y => positiveLinear e (g.symm y)
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
  have hi : Integrable (fun x => density (positiveLinear e) x+t*(1-‖e‖^2)*firstTerm φ e x+
      t^2*(2*‖e‖^4*C^2)) (volume.restrict (ball a R)) := by
    convert ((density_integrable_ball (positiveLinear_lipschitz e) a R).add
    ((firstTerm_integrable_ball hφ e a R).const_mul (t*(1-‖e‖^2)))).add
      (integrable_const (t^2*(2*‖e‖^4*C^2))) using 1; rfl
  have hm := integral_mono_of_nonneg
    (μ:=volume.restrict (ball a R))
    (f:=fun x => (1+t*fderiv ℝ φ x e)*density v (g x))
    (g:=fun x => density (positiveLinear e) x+t*(1-‖e‖^2)*firstTerm φ e x+
      t^2*(2*‖e‖^4*C^2))
    (Eventually.of_forall (fun x => mul_nonneg (hdetpos x) (density_nonneg v (g x)))) hi
    (by
      filter_upwards [ae_restrict_of_ae (inner_ne_zero_ae he)] with x hx
      exact density_pullback_bound ((hφ.differentiable (by simp)) x) hLip e t (hdet x) g hg hx)
  have hiE := density_integrable_ball (positiveLinear_lipschitz e) a R
  have hiF := (firstTerm_integrable_ball hφ e a R).const_mul (t*(1-‖e‖^2))
  have hsum : (∫ x in ball a R, density (positiveLinear e) x+t*(1-‖e‖^2)*firstTerm φ e x+
      t^2*(2*‖e‖^4*C^2)) =
      energy (ball a R) (positiveLinear e) (gradient (positiveLinear e)) +
        t*(1-‖e‖^2)*(∫ x in ball a R, firstTerm φ e x) +
        t^2*(2*‖e‖^4*C^2)*(volume (ball a R)).toReal := by
    have hadd := integral_add (hiE.add hiF) (integrable_const (t^2*(2*‖e‖^4*C^2)))
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

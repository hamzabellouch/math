import OAI.Analysis.CircleDomains.Sobolev.CompactWeakDerivativeIntegral
import OAI.Analysis.CircleDomains.Sobolev.SmoothExteriorReplacement

namespace OAI

/-! The genuine compact Sobolev correction has zero derivative integral.
Consequently a smooth exterior replacement preserves the finite-ball
vertical flux of the original weak coordinate. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integral_weakGradient_eq_smooth_replacement {u v e : EuclideanPlane → ℝ}
    {R : ℝ} (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball 0 R))
    (he : DeGiorgi.MemW1pWitness 2 e univ)
    (hs : HasCompactSupport e) (hsub : tsupport e ⊆ Metric.ball 0 R)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hue : ∀ x, u x = v x + e x) (i : Fin 2) :
    (∫ x in Metric.ball 0 R, hu.weakGrad x i) =
      ∫ x in Metric.ball 0 R, fderiv ℝ v x (EuclideanSpace.single i 1) := by
  let V : DeGiorgi.MemW1pWitness 2 v (Metric.ball 0 R) :=
    smoothPlaneSobolevWitness Metric.isOpen_ball (hv.of_le (by simp)).contDiffOn
      (continuous_memLp_ball hv.continuous R)
      (fun j => continuous_memLp_ball
        ((hv.continuous_fderiv (by simp)).clm_apply continuous_const) R)
  have hdiff : (fun x => u x-v x) =ᵐ[volume.restrict (Metric.ball 0 R)] e :=
    Eventually.of_forall (fun x => by change u x-v x = e x; rw [hue x]; ring)
  let W := (hu.sub V).congr_ae hdiff
  let E : DeGiorgi.MemW1pWitness 2 e (Metric.ball 0 R) :=
    he.restrict Metric.isOpen_ball (subset_univ _)
  have hg := (W.isWeakGrad i).ae_eq Metric.isOpen_ball (E.isWeakGrad i)
    ((W.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((E.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  have hg' : (fun x => hu.weakGrad x i - fderiv ℝ v x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict (Metric.ball 0 R)] fun x => he.weakGrad x i := by
    simpa [W, E, V, DeGiorgi.MemW1pWitness.sub, DeGiorgi.MemW1pWitness.congr_ae,
      DeGiorgi.MemW1pWitness.add, DeGiorgi.MemW1pWitness.smul,
      DeGiorgi.MemW1pWitness.restrict, smoothPlaneSobolevWitness, sub_eq_add_neg] using hg
  have he0 : (∫ x in Metric.ball 0 R, he.weakGrad x i) = 0 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
    · exact integral_compact_weakGradient_eq_zero he hs i
    · filter_upwards [compact_weakGradient_zero_off he i] with x hx hxB
      exact hx (fun ht => hxB (hsub ht))
  have huint : IntegrableOn (fun x => hu.weakGrad x i) (Metric.ball 0 R) := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanPlane) R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact (hu.weakGrad_component_memLp i).integrable (by norm_num)
  have hvint : IntegrableOn (fun x => fderiv ℝ v x (EuclideanSpace.single i 1))
      (Metric.ball 0 R) := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanPlane) R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact (V.weakGrad_component_memLp i).integrable (by norm_num)
  have hh := integral_congr_ae hg'
  rw [integral_sub huint hvint, he0] at hh
  linarith

end CircleDomainRigidity

end

end OAI

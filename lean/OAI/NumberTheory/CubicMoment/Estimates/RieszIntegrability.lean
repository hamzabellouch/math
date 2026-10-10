import OAI.NumberTheory.CubicGram.PeriodicPoisson
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace OAI

/-! Integrability of the two Riesz weights used in the cubic dispersion integral. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set Metric
namespace CubicFirstMoment

/-- The singularity is locally integrable in dimension two; away from
zero the weight is bounded and Schwartz integrability suffices. -/
theorem schwartz_riesz_integrable (F : 𝓢(ℂ,ℂ)) {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    Integrable (fun z : ℂ => ((‖z‖^(-a):ℝ):ℂ)*F z) := by
  let g (z : ℂ) : ℂ := ((‖z‖^(-a):ℝ):ℂ)*F z
  have hm : AEStronglyMeasurable g volume := by
    dsimp only [g]
    exact ((Complex.continuous_ofReal.measurable.comp
      (measurable_norm.pow_const (-a))).mul F.continuous.measurable).aestronglyMeasurable
  obtain ⟨C,hC,hbound⟩ := F.decay 0 0
  simp only [pow_zero,one_mul,norm_iteratedFDeriv_zero] at hbound
  have hlocal : IntegrableOn g (ball (0:ℂ) 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp) (α := a) (C := C) (by simpa using ha2) _ hm
    filter_upwards with z
    dsimp only [g]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (_root_.norm_nonneg z) _)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hbound z) (Real.rpow_nonneg (_root_.norm_nonneg z) (-a))
  have hfar : IntegrableOn g (ball (0:ℂ) 1)ᶜ := by
    apply F.integrable.norm.restrict.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
    dsimp only [g]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (_root_.norm_nonneg z) _)]
    have hz1 : 1 ≤ ‖z‖ := by simpa only [Set.mem_compl_iff,mem_ball,dist_zero_right,not_lt] using hz
    have hw : ‖z‖^(-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1 (neg_nonpos.mpr ha.le)
    exact mul_le_of_le_one_left (_root_.norm_nonneg _) hw
  have hwhole := hlocal.union hfar
  simpa only [union_compl_self,integrableOn_univ] using hwhole

end CubicFirstMoment

end

end OAI

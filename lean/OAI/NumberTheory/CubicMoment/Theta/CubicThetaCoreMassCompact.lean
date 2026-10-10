import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreBumpIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactDensityBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactDomination

namespace OAI

/-! Compactness of the genuine global core bump multipliers. The
weighted quotient norm is controlled by the proved compact local map. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment

local instance coreMassCompact_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance coreMassCompact_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

lemma cubicThetaLocalValue_norm_sq {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaLocalValue hφ hc hp F‖^2=
      ∫ y, ‖cubicThetaTestLocalization φ F y‖^2 := by
  rw [cubicThetaLocalValue_apply,cubicTheta_l2_norm_sq_measure]
  calc
    _ = ∫ u, ‖cubicThetaTestLocalization φ F (cubicThetaTangentCoordinates u)‖^2
        ∂LocalSobolev.tangentBorelVolume := by
      apply integral_congr_ae
      filter_upwards [(LocalSobolev.tangentFunction_memLp (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
        (cubicThetaTestLocalization_compact hc F)).coeFn_toLp] with u hu
      change ‖((LocalSobolev.tangentFunction_memLp (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
        (cubicThetaTestLocalization_compact hc F)).toLp _) u‖^2=_
      rw [hu]
      rfl
    _ = _ := LocalSobolev.tangentBorelVolume_integral
      (fun y => ‖cubicThetaTestLocalization φ F y‖^2)

lemma cubicThetaCoreMass_weighted_integral (c : CubicThetaQuotient) (F : cubicThetaSmoothTests) :
    ‖cubicThetaCoreMass c (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ y, ‖cubicThetaTestLocalization (cubicThetaCoreProfile c) F y‖^2/y.2^3 := by
  rw [cubicThetaCoreMass_sheet_integral]
  have hi := cubicThetaPointIntegral_density (cubicThetaCorePointSupport_compact c).measurableSet
    (fun y => ‖cubicThetaTestLocalization (cubicThetaCoreProfile c) F y‖^2)
  change (∫ p in cubicThetaCorePointSupport c,
    ‖cubicThetaTestLocalization (cubicThetaCoreProfile c) F (cubicThetaPointCoordinates p)‖^2
      ∂cubicThetaPointMeasure)=_ 
  rw [hi]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have ht : y∉tsupport (cubicThetaTestLocalization (cubicThetaCoreProfile c) F) :=
    fun h => hy (cubicThetaCoreProfile_support_coordinates c (tsupport_mul_subset_left h))
  rw [image_eq_zero_of_notMem_tsupport ht,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_div]

lemma cubicThetaCoreMass_norm_domination (c : CubicThetaQuotient) :
    ∃ C, ∀ u : cubicThetaGlobalEnergySpace,
      ‖cubicThetaCoreMass c u‖≤C*‖cubicThetaCoreLocalInclusion c u‖ := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompactDensity_bound
    (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
  refine ⟨Real.sqrt C,?_⟩
  apply isClosed_property cubicThetaGlobalEnergyTestLinear_dense
    (isClosed_le (cubicThetaCoreMass c).continuous.norm
      (continuous_const.mul (cubicThetaCoreLocalInclusion c).continuous.norm))
  intro F
  have h := hbound (cubicThetaTestLocalization (cubicThetaCoreProfile c) F)
    (cubicThetaTestLocalization_smooth (cubicThetaCoreProfile_contDiff c)
      (cubicThetaCoreProfile_support_positive c) F).continuous
    (cubicThetaTestLocalization_compact (cubicThetaCoreProfile_compact c) F)
    tsupport_mul_subset_left
  rw [← cubicThetaCoreMass_weighted_integral,← cubicThetaLocalValue_norm_sq
    (cubicThetaCoreProfile_contDiff c) (cubicThetaCoreProfile_compact c)
      (cubicThetaCoreProfile_support_positive c),← cubicThetaCoreLocalInclusion_test] at h
  have he : (Real.sqrt C*‖cubicThetaCoreLocalInclusion c (cubicThetaGlobalEnergyTest F)‖)^2=
      C*‖cubicThetaCoreLocalInclusion c (cubicThetaGlobalEnergyTest F)‖^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
  exact _root_.le_of_sq_le_sq (h.trans_eq he.symm)
    (mul_nonneg (Real.sqrt_nonneg C) (_root_.norm_nonneg _))

theorem cubicThetaCoreMass_compact (c : CubicThetaQuotient) :
    IsCompactOperator (cubicThetaCoreMass c) :=
  cubicThetaCompact_of_norm_domination (cubicThetaCoreMass c) (cubicThetaCoreLocalInclusion c)
    (cubicThetaCoreLocalInclusion_compact c) (cubicThetaCoreMass_norm_domination c)

end CubicFirstMoment

end

end OAI

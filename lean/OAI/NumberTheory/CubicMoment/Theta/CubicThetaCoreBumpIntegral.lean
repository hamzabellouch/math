import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreLocalRellich
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreSections
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalMultiplier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaChartRestrictedIntegral

namespace OAI

/-! The norm of a global core cutoff equals the scalar integral over
its actual covering sheet. This retains the cubic section's unit twist. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCoreBump_support_image (c : CubicThetaQuotient) :
    Function.support (cubicThetaCoreBump c)⊆
      cubicThetaQuotientMap '' cubicThetaCorePointSupport c := by
  intro q hq
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift c)
  have ht : q∈e.target := ((cubicThetaCoreBump c).support_subset_source hq).1
  let p := e.symm q
  have hp : p∈e.source := e.map_target ht
  have hqp : cubicThetaQuotientMap p=q := by
    rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift c)]
    exact e.right_inv ht
  have hv := cubicThetaCoreSeed_eq_bump c hp
  rw [hqp] at hv
  have hprof : cubicThetaCoreProfile c p.val≠0 := by
    rw [hv]
    exact_mod_cast hq
  refine ⟨p,?_,hqp⟩
  refine ⟨p.val,subset_tsupport _ hprof,?_⟩
  exact cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)

lemma cubicThetaCoreBump_complex_bound (c q : CubicThetaQuotient) :
    ‖(cubicThetaCoreBump c q : ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cubicThetaCoreBump c).nonneg]
  exact (cubicThetaCoreBump c).le_one

def cubicThetaCoreMultiplier (c : CubicThetaQuotient) : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaGlobalMultiplier
    (Complex.continuous_ofReal.comp (cubicThetaCoreBump c).continuous).aestronglyMeasurable
    (cubicThetaCoreBump_complex_bound c)

lemma cubicThetaCoreMultiplier_ae (c : CubicThetaQuotient) (u : CubicThetaGlobalL2) :
    (cubicThetaCoreMultiplier c u : CubicThetaQuotient → ℂ)=ᵐ[cubicThetaQuotientMeasure]
      fun q => (cubicThetaCoreBump c q:ℂ)*u q :=
  cubicThetaGlobalMultiplier_ae _ _ u

def cubicThetaCoreMass (c : CubicThetaQuotient) : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaGlobalL2 :=
  (cubicThetaCoreMultiplier c).comp cubicThetaGlobalInclusion

lemma cubicThetaCoreMass_test_norm_sq (c : CubicThetaQuotient) (F : cubicThetaSmoothTests) :
    ‖cubicThetaCoreMass c (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ q, (cubicThetaCoreBump c q)^2*cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [cubicThetaCoreMultiplier_ae c (cubicThetaGlobalMass F),
    (cubicThetaSectionRepresentative_memLp F).coeFn_toLp] with q hq hF
  change ‖cubicThetaCoreMultiplier c (cubicThetaGlobalMass F) q‖^2=_
  rw [hq]
  change ‖(cubicThetaCoreBump c q:ℂ)*((cubicThetaSectionRepresentative_memLp F).toLp _) q‖^2=_
  rw [hF,norm_mul,mul_pow,cubicThetaSectionRepresentative_norm,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cubicThetaCoreMass_sheet_integral (c : CubicThetaQuotient) (F : cubicThetaSmoothTests) :
    ‖cubicThetaCoreMass c (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ p in cubicThetaCorePointSupport c,
        ‖cubicThetaTestLocalization (cubicThetaCoreProfile c) F (cubicThetaPointCoordinates p)‖^2
          ∂cubicThetaPointMeasure := by
  rw [cubicThetaCoreMass_test_norm_sq]
  let S := cubicThetaCorePointSupport c
  have hzero : ∀ q, q∉cubicThetaQuotientMap '' S →
      (cubicThetaCoreBump c q)^2*cubicThetaSectionNorm F q^2=0 := by
    intro q hq
    have hz : cubicThetaCoreBump c q=0 :=
      Function.notMem_support.mp (fun h => hq (cubicThetaCoreBump_support_image c h))
    rw [hz,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hcont : Continuous (fun q => (cubicThetaCoreBump c q)^2*cubicThetaSectionNorm F q^2) :=
    ((cubicThetaCoreBump c).continuous.pow 2).mul ((cubicThetaSectionNorm_continuous F).pow 2)
  rw [cubicThetaChart_integral (cubicThetaCoveringChart (cubicThetaQuotientLift c))
    (cubicThetaCoveringChart_coe _) (cubicThetaCorePointSupport_compact c).measurableSet
    (cubicThetaCorePointSupport_sheet c)
    (fun q => (cubicThetaCoreBump c q)^2*cubicThetaSectionNorm F q^2) hcont.stronglyMeasurable]
  apply setIntegral_congr_fun (cubicThetaCorePointSupport_compact c).measurableSet
  intro p hp
  have he := cubicThetaCoreSeed_eq_bump c (cubicThetaCorePointSupport_sheet c hp)
  have hi : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaPointCoordinates,cubicThetaTestLocalization,hi,norm_mul,mul_pow,he,
    cubicThetaSectionNorm_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]

end CubicFirstMoment

end

end OAI

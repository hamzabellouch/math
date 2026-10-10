import OAI.NumberTheory.CubicMoment.Theta.CubicThetaChartEnergyDomination
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionCutoffEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalEnergyGraph

namespace OAI

/-! Boundedness of each actual compact chart localization from the
global energy graph to its weighted local energy graph. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaIntrinsicCoordinateEnergy (F : cubicThetaSmoothTests) (y : ℂ × ℝ) : ℝ :=
  let q := cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)
  cubicThetaSectionNorm F q^2+cubicThetaQuotientEnergy F q

lemma cubicThetaIntrinsicCoordinateEnergy_apply (F : cubicThetaSmoothTests)
    (p : CubicThetaPoint) :
    cubicThetaIntrinsicCoordinateEnergy F (cubicThetaPointCoordinates p)=
      cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+cubicThetaSectionEnergy F p := by
  have he : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaIntrinsicCoordinateEnergy,cubicThetaPointCoordinates,he,
    cubicThetaQuotientEnergy_apply]

lemma cubicThetaIntrinsicCoordinateEnergy_continuousOn (F : cubicThetaSmoothTests) :
    ContinuousOn (fun y => cubicThetaIntrinsicCoordinateEnergy F y/y.2^3)
      {y : ℂ × ℝ | 0<y.2} := by
  have hinc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hq := cubicThetaQuotientMap_open.continuous.comp_continuousOn hinc
  have hcont := ((cubicThetaSectionNorm_continuous F).pow 2).add
    (cubicThetaQuotientEnergy_continuous F)
  exact (hcont.comp_continuousOn hq).div (continuous_snd.pow 3).continuousOn
    (fun y hy => pow_ne_zero 3 hy.ne')

lemma cubicThetaLocalEnergyJet_zero {f : ℂ × ℝ → ℂ} {y : ℂ × ℝ}
    (hy : y∉tsupport f) : cubicThetaLocalEnergyJet f y=0 := by
  have hz := image_eq_zero_of_notMem_tsupport hy
  have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hy
  ext i
  fin_cases i <;> simp [cubicThetaLocalEnergyJet,hz,hd]

theorem cubicThetaGlobalLocalization_bound {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : IsCompact S) (hSe : S⊆e.source)
    (hsupp : tsupport φ⊆cubicThetaPointCoordinates '' S) :
    ∃ C≥0, ∀ F : cubicThetaSmoothTests,
      ‖cubicThetaLocalEnergyGraph hφ hc hp F‖^2≤C*‖cubicThetaGlobalEnergyTest F‖^2 := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaSectionCutoffEnergy_bound hφ hc
  refine ⟨C,hC,fun F => ?_⟩
  let K := cubicThetaPointCoordinates '' S
  have hK : IsCompact K := hS.image continuous_subtype_val
  have hKpos : K⊆{y : ℂ × ℝ | 0<y.2} := by
    rintro _ ⟨p,_,rfl⟩
    exact p.property
  have hr : IntegrableOn (fun y => cubicThetaIntrinsicCoordinateEnergy F y/y.2^3) K :=
    ((cubicThetaIntrinsicCoordinateEnergy_continuousOn F).mono hKpos).integrableOn_compact hK
  have hj := (cubicThetaLocalSectionJet_memLp hφ hc hp F).integrable_norm_pow (by norm_num)
  have hmono : (∫ y in K, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2)≤
      C*(∫ y in K, cubicThetaIntrinsicCoordinateEnergy F y/y.2^3) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hj.integrableOn (hr.const_mul C) hK.measurableSet
    rintro _ ⟨p,hpS,rfl⟩
    rw [cubicThetaIntrinsicCoordinateEnergy_apply]
    simpa only [mul_div_assoc,cubicThetaQuotientEnergy_apply,cubicThetaPointCoordinates] using hbound F p
  have hint : (∫ y in K, cubicThetaIntrinsicCoordinateEnergy F y/y.2^3)≤
      ‖cubicThetaGlobalEnergyTest F‖^2 := by
    rw [← cubicThetaPointIntegral_density hS.measurableSet]
    have heq : (∫ p in S, cubicThetaIntrinsicCoordinateEnergy F (cubicThetaPointCoordinates p)
        ∂cubicThetaPointMeasure)=
        ∫ p in S, cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+
          cubicThetaSectionEnergy F p ∂cubicThetaPointMeasure := by
      apply setIntegral_congr_fun hS.measurableSet
      intro p _
      exact cubicThetaIntrinsicCoordinateEnergy_apply F p
    rw [heq]
    exact cubicThetaChart_energy_le e he hS.measurableSet hSe F
  have hfull : (∫ y in K, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2)=
      ∫ y, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have ht : y∉tsupport (cubicThetaTestLocalization φ F) :=
      fun h => hy (hsupp (tsupport_mul_subset_left h))
    rw [cubicThetaLocalEnergyJet_zero ht,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
  have hn : ‖cubicThetaLocalEnergyGraph hφ hc hp F‖^2=
      ∫ y, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2 := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaLocalSectionJet_memLp hφ hc hp F).coeFn_toLp] with y hy
    change ‖((cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _) y‖^2=_
    rw [hy]
  rw [hn,← hfull]
  exact hmono.trans (mul_le_mul_of_nonneg_left hint hC)

end CubicFirstMoment

end

end OAI

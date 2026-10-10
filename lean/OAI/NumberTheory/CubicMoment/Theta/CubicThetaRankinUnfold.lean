import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarSeedPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveUnfold

namespace OAI

/-! The sharp Rankin kernel unfolds against the actual L2 model. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaScalarEnergyDensity_integrable
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure)
    {σ K : ℝ} (hσ : 0<σ)
    (hb : ∀ q,‖(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)‖≤K) :
    Integrable (cubicThetaScalarEnergyDensity F σ) cubicThetaQuotientMeasure := by
  have hnorm : Integrable (fun q => ‖cubicThetaSectionRepresentative F q‖^2)
      cubicThetaQuotientMeasure := hF.integrable_norm_pow (by norm_num)
  apply (hnorm.const_mul (K/σ)).mono'
    (cubicThetaScalarEnergyDensity_measurable F σ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun q => by
    have hk := hb q
    have hn := cubicThetaScalarRankinKernel_nonneg σ q
    rw [←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hσ.le hn)] at hk
    have hdiv : cubicThetaScalarRankinKernel σ q≤K/σ := by
      apply (le_div_iff₀ hσ).mpr
      simpa only [mul_comm] using hk
    rw [Real.norm_of_nonneg (cubicThetaScalarEnergyDensity_nonneg F σ q)]
    exact mul_le_mul_of_nonneg_right hdiv (sq_nonneg _))

lemma cubicThetaScalarEnergySeed_unfold
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure)
    {σ K : ℝ} (hσ : 0<σ)
    (hb : ∀ q,‖(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)‖≤K) :
    Integrable (cubicThetaScalarEnergySeed F σ) cubicThetaPointMeasure ∧
      (∫ p,cubicThetaScalarEnergySeed F σ p ∂cubicThetaPointMeasure)=
        ∫ q,cubicThetaScalarEnergyDensity F σ q ∂cubicThetaQuotientMeasure :=
  cubicThetaPositive_unfold _ (cubicThetaScalarEnergySeed_measurable F σ)
    (cubicThetaScalarEnergySeed_nonneg F σ) _ (cubicThetaScalarEnergyDensity_measurable F σ)
    (cubicThetaScalarEnergyDensity_nonneg F σ)
    (cubicThetaScalarEnergyDensity_integrable F hF hσ hb)
    (cubicThetaScalarEnergySeed_group_summable F hσ)
    (cubicThetaScalarEnergySeed_group_sum F hσ)

theorem cubicThetaArithmeticRankinMass_unfold :
    ∀ᶠ σ : ℝ in 𝓝[>] 0,
      Integrable (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ)
        cubicThetaPointMeasure ∧
      cubicThetaArithmeticRankinMass σ=
        ∫ p,(cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)
          ∂cubicThetaPointMeasure := by
  obtain ⟨K,_hK,hbound⟩ := cubicThetaScalarRankinKernel_uniform
  filter_upwards [hbound,self_mem_nhdsWithin] with σ hb hσ
  change 0<σ at hσ
  have hu := cubicThetaScalarEnergySeed_unfold cubicThetaArithmeticModelSection
    cubicThetaArithmeticModelGlobal_memLp hσ hb
  refine ⟨hu.1,?_⟩
  have hc := congrArg Complex.ofReal hu.2
  rw [←integral_complex_ofReal,←integral_complex_ofReal] at hc
  rw [hc,cubicThetaArithmeticRankinMass]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => by
    dsimp only
    rw [cubicThetaArithmeticModelPairing_eq]
    simp only [cubicThetaScalarEnergyDensity,Complex.ofReal_mul,Complex.ofReal_pow])

end CubicFirstMoment

end

end OAI

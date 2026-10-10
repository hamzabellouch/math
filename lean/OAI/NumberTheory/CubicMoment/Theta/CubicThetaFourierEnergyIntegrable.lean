import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyMellin

namespace OAI

/-! Absolute integrability of the actual Fourier-energy Mellin transform. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance : Countable Eisenstein := coordinatesEquiv.symm.injective.countable

lemma cubicThetaArithmeticFourierEnergy_nonneg (v : ℝ) :
    0≤cubicThetaArithmeticFourierEnergy v := tsum_nonneg (fun _ => sq_nonneg _)

theorem cubicThetaArithmeticFourierEnergy_mellin_integrable {σ : ℝ} (hσ : 0<σ) :
    IntegrableOn (fun v : ℝ => v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v) (Ioi 0) := by
  let F := cubicThetaEnergyMellinTerm σ
  have hi (n : Eisenstein) : IntegrableOn (F n) (Ioi 0) :=
    cubicThetaEnergyMellinTerm_integrable hσ.le n
  have hs : Summable (fun n : Eisenstein => ∫ v in Ioi (0:ℝ),‖F n v‖) := by
    simpa only [F,cubicThetaEnergyMellinTerm_norm_integral] using
      (cubicThetaCoefficientMassTerm_summable hσ).mul_left (81^σ*cubicWhittakerEnergyMass σ)
  have hm : AEMeasurable (fun v => ∑' n : Eisenstein,F n v) (volume.restrict (Ioi 0)) :=
    AEMeasurable.tsum (fun n => (hi n).aestronglyMeasurable.aemeasurable)
  have hsum : IntegrableOn (fun v => ∑' n : Eisenstein,F n v) (Ioi 0) := by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    change (∫⁻ v,‖∑' n : Eisenstein,F n v‖ₑ ∂volume.restrict (Ioi 0)) < ⊤
    have he : (fun v => ‖∑' n : Eisenstein,F n v‖ₑ)=ᵐ[volume.restrict (Ioi 0)]
        (fun v => ∑' n : Eisenstein,‖F n v‖ₑ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hn (n : Eisenstein) : 0≤F n v := cubicThetaEnergyMellinTerm_nonneg σ n hv
      have hbase := (cubicThetaArithmetic_summable hv 0).norm
      have hprod := summable_mul_of_summable_norm hbase.norm hbase.norm
      have hsq : Summable (fun n : Eisenstein =>
          ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖^2) := by
        have hd := hprod.comp_injective (show Function.Injective (fun n : Eisenstein => (n,n))
          from fun _ _ h => congrArg Prod.fst h)
        change Summable (fun n : Eisenstein =>
          ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖*
            ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖) at hd
        simpa only [pow_two] using hd
      have hsn : Summable (fun n : Eisenstein => F n v) := hsq.mul_left _

      rw [Real.enorm_of_nonneg (tsum_nonneg hn),ENNReal.ofReal_tsum_of_nonneg hn hsn]
      apply tsum_congr
      intro n
      exact (Real.enorm_of_nonneg (hn n)).symm
    rw [lintegral_congr_ae he,lintegral_tsum (fun n => (hi n).aestronglyMeasurable.enorm)]
    simp_rw [←ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun _ => _root_.norm_nonneg _)) hs]
    exact ENNReal.ofReal_lt_top
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _hv
  dsimp only [F,cubicThetaEnergyMellinTerm]
  rw [cubicThetaArithmeticFourierEnergy_all,tsum_mul_left]

end CubicFirstMoment

end

end OAI

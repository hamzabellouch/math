import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCutoffEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientEnergy

namespace OAI

/-! The local cutoff estimate in intrinsic quotient variables. This is
the pointwise bridge from the actual local graph to the global energy. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaSectionFunction_energy_density (F : cubicThetaSmoothTests)
    (p : CubicThetaPoint) :
    ‖cubicThetaLocalEnergyJet (cubicThetaSectionFunction F) p.val‖^2=
      (cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+
        cubicThetaQuotientEnergy F (cubicThetaQuotientMap p))/p.val.2^3 := by
  rw [cubicThetaLocalEnergyJet_density _ p.property,cubicThetaSectionNorm_apply,
    cubicThetaQuotientEnergy_apply]
  congr 1
  rw [cubicThetaSectionFunction_apply F p.property]
  rfl

theorem cubicThetaSectionCutoffEnergy_bound {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ C≥0, ∀ (F : cubicThetaSmoothTests) (p : CubicThetaPoint),
      ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) p.val‖^2≤
        C*((cubicThetaSectionNorm F (cubicThetaQuotientMap p))^2+
          cubicThetaQuotientEnergy F (cubicThetaQuotientMap p))/p.val.2^3 := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCutoffEnergyCoefficient_bounded
    (hφ.of_le (by simp)) hc
  refine ⟨C,hC,fun F p => ?_⟩
  have he := cubicThetaLocalEnergyJet_cutoff_le p.property
    (hφ.differentiable (by simp) p.val)
    (cubicThetaSectionFunction_differentiable F p.property)
  change ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) p.val‖^2≤_ at he
  have hmul := mul_le_mul_of_nonneg_right (hbound p.val)
    (sq_nonneg ‖cubicThetaLocalEnergyJet (cubicThetaSectionFunction F) p.val‖)
  have h := he.trans hmul
  rw [cubicThetaSectionFunction_energy_density F p] at h
  simpa only [mul_div_assoc] using h

end CubicFirstMoment

end

end OAI

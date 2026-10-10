import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBorelRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripReduction

namespace OAI

/-! Null sets on the arithmetic quotient lift to null sets upstairs.
The countable translates of positive strips supply the required exhaustion. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
local instance : Countable Eisenstein := coordinatesEquiv.symm.injective.countable

theorem cubicThetaQuotient_pull_ae {P : CubicThetaQuotient → Prop}
    (hP : ∀ᵐ q ∂cubicThetaQuotientMeasure,P q) :
    ∀ᵐ p ∂cubicThetaPointMeasure,P (cubicThetaQuotientMap p) := by
  have hs (n : ℕ) : ∀ᵐ p ∂cubicThetaPointMeasure,
      p∈cubicThetaCuspStrip (1/(n+1:ℝ)) → P (cubicThetaQuotientMap p) :=
    (ae_restrict_iff' (cubicThetaCuspStrip_measurable _)).mp
      (cubicThetaPositiveStrip_pull_ae (by positivity) hP)
  have hall : ∀ᵐ p ∂cubicThetaPointMeasure,∀ w : Eisenstein,∀ n : ℕ,
      cubicThetaPrincipalTranslation w • p∈cubicThetaCuspStrip (1/(n+1:ℝ)) →
        P (cubicThetaQuotientMap (cubicThetaPrincipalTranslation w • p)) :=
    ae_all_iff.mpr (fun w => ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (cubicThetaPrincipalTranslation w)
        cubicThetaPointMeasure).quasiMeasurePreserving.ae (hs n)))
  filter_upwards [hall] with p hp
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt p.property
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction p hn
  simpa only [cubicThetaQuotient_covering.map_smul] using hp w n hw

end CubicFirstMoment

end

end OAI

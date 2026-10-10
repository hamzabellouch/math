import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFMassFinite
import OAI.Probability.SKBarriers.Parisi.CDFVariationContinuity
import OAI.Probability.SKBarriers.Parisi.CDFParisiContinuity

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFParisi_mass_remainder (β : ℝ) (α γ : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hg : ∀ z, γ z∈Icc (0:ℝ) 1) (hγ1 : γ 1=1) {h : ℝ} (hh : 0<h) :
    |scalarCDFParisi β γ-scalarCDFParisi β α-
      (β^2/2)*∫ s in Icc (0:ℝ) 1, (γ s-α s)*(scalarCDFOverlap β α s-s)|≤
      (β^2/2)*cdfDistance γ α*scalarOverlapModulus β (cdfDistance γ α) h := by
  let A := fun n => uniformCDFQuantiles n α
  let B := fun n => uniformCDFQuantiles n γ
  have HA := uniformCDFQuantiles_L1_tendsto α ha hα1
  have HB := uniformCDFQuantiles_L1_tendsto γ hg hγ1
  have HD := cdfDistance_tendsto γ.mono α.mono
    (fun n => quantileCDF_monotone n (B n)) (fun n => quantileCDF_monotone n (A n)) HB HA
  have HPA := scalarCDFParisi_tendsto_of_L1 β ha α.mono
    (fun n => quantileCDF_bounds n (A n)) (fun n => quantileCDF_monotone n (A n)) HA
  have HPB := scalarCDFParisi_tendsto_of_L1 β hg γ.mono
    (fun n => quantileCDF_bounds n (B n)) (fun n => quantileCDF_monotone n (B n)) HB
  have HI := scalarCDFVariation_quantile_integral_tendsto β α γ ha hα1 hg hγ1
  exact le_of_tendsto_of_tendsto ((HPB.sub HPA).sub (tendsto_const_nhds.mul HI)).abs
    ((tendsto_const_nhds.mul HD).mul ((scalarOverlapModulus_continuous β h).tendsto _ |>.comp HD))
    (Eventually.of_forall (fun n => scalarCDFParisi_mass_remainder_quantile β (A n) (B n)
      (uniformCDFQuantiles_admissible n α hα1) (uniformCDFQuantiles_admissible n γ hγ1) hh))

end SK.Analytic

end
end

end OAI

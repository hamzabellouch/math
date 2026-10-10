import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Absolute horizontal unfolding for the actual level-three lattice cell. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology Pointwise
namespace CubicFirstMoment

lemma cubicThetaHorizontal_translates_summable {f : ℂ → ℂ} (hf : Integrable f) :
    Summable (fun g : CubicThetaPeriodGroup =>
      ∫ z in cubicThetaHorizontalCell,‖f (g • z)‖) := by
  have hD := cubicThetaHorizontalCell_fundamental volume
  have hsum : Integrable f (Measure.sum (fun g : CubicThetaPeriodGroup =>
      volume.restrict (g • cubicThetaHorizontalCell))) := by
    rwa [hD.sum_restrict]
  apply hsum.summable_integral.congr
  intro g
  exact (measurePreserving_smul g volume).setIntegral_image_emb
    (measurableEmbedding_const_smul g) (fun z => ‖f z‖) cubicThetaHorizontalCell

lemma cubicThetaHorizontal_integral_tsum {f : ℂ → ℂ} (hf : Integrable f) :
    (∫ z in cubicThetaHorizontalCell,∑' g : CubicThetaPeriodGroup,f (g • z))=
      ∫ z,f z := by
  have hgi (g : CubicThetaPeriodGroup) :
      IntegrableOn (fun z => f (g • z)) cubicThetaHorizontalCell :=
    ((measurePreserving_smul g volume).integrable_comp_of_integrable hf).integrableOn
  calc
    _ = ∑' g : CubicThetaPeriodGroup,∫ z in cubicThetaHorizontalCell,f (g • z) :=
      (integral_tsum_of_summable_integral_norm hgi
        (cubicThetaHorizontal_translates_summable hf)).symm
    _ = _ := (cubicThetaHorizontalCell_fundamental volume).integral_eq_tsum'' f hf |>.symm

lemma cubicThetaHorizontal_periodized_integrable {f : ℂ → ℂ}
    (hfc : Continuous f) (hf : Integrable f)
    (hs : ∀ z,Summable (fun g : CubicThetaPeriodGroup => f (g • z))) :
    IntegrableOn (fun z => ∑' g : CubicThetaPeriodGroup,f (g • z))
      cubicThetaHorizontalCell := by
  have hgi (g : CubicThetaPeriodGroup) :
      IntegrableOn (fun z => f (g • z)) cubicThetaHorizontalCell :=
    ((measurePreserving_smul g volume).integrable_comp_of_integrable hf).integrableOn
  have hm : StronglyMeasurable (fun z => ∑' g : CubicThetaPeriodGroup,f (g • z)) := by
    apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset CubicThetaPeriodGroup))
      (f:=fun s z => ∑ g∈s,f (g • z))
    · intro s
      exact (continuous_finsetSum s (fun g _ => hfc.comp (continuous_const_smul g))).stronglyMeasurable
    · exact tendsto_pi_nhds.mpr (fun z => (hs z).hasSum)
  refine ⟨hm.aestronglyMeasurable,?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun z => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun g => (hgi g).aestronglyMeasurable.enorm)]
  simp_rw [←ofReal_integral_norm_eq_lintegral_enorm (hgi _)]
  exact (cubicThetaHorizontal_translates_summable hf).tsum_ofReal_lt_top

end CubicFirstMoment

end

end OAI

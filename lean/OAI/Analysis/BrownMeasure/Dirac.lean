import Mathlib
import OAI.Analysis.BrownMeasure.Model

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FiniteFactor
lemma expLogPotential_dirac_zero (z : ℂ) :
    expLogPotential (Measure.dirac (0:ℂ)) z=ENNReal.ofReal ‖z‖ := by
  have he (n : ℕ) : ENNReal.ofReal (Real.exp (∫ w,logarithmCutoff n ‖z-w‖ ∂Measure.dirac (0:ℂ)))=
      ENNReal.ofReal (max (Real.exp (-(n:ℝ))) ‖z‖) := by
    rw [integral_dirac]
    simp only [sub_zero]
    change ENNReal.ofReal (Real.exp (Real.log (max (Real.exp (-(n:ℝ))) ‖z‖)))=_
    rw [Real.exp_log ((Real.exp_pos _).trans_le (le_max_left _ _))]
  unfold expLogPotential
  simp_rw [he]
  apply le_antisymm
  · have ht : Tendsto (fun n:ℕ=>ENNReal.ofReal (max (Real.exp (-(n:ℝ))) ‖z‖)) atTop (𝓝 (ENNReal.ofReal ‖z‖)) := by
      have hmax : Tendsto (fun index : ℕ => max (Real.exp (-(index : ℝ))) ‖z‖)
          atTop (𝓝 (max 0 ‖z‖)) :=
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).max
          (tendsto_const_nhds (x := ‖z‖))
      simpa only [max_eq_right (norm_nonneg z)] using ENNReal.tendsto_ofReal hmax
    exact ge_of_tendsto ht (Eventually.of_forall (iInf_le _))
  · exact le_iInf (fun n=>ENNReal.ofReal_le_ofReal (le_max_right _ _))
lemma dirac_zero_support_compact : IsCompact (Measure.dirac (0:ℂ)).support := by
  have hs : (Measure.dirac (0:ℂ)).support⊆{0} := by
    apply Measure.support_subset_of_isClosed isClosed_singleton
    simp
  exact isCompact_singleton.of_isClosed_subset Measure.isClosed_support hs
end FiniteFactor
end

end OAI

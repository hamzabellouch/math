import Mathlib
import OAI.Analysis.BrownMeasure.Model

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace FiniteFactor
lemma spectrum_eq_zero_of_root_norm_tendsto {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] (T : A)
    (hT : Tendsto (fun n:ℕ=>‖T^n‖^(1/(n:ℝ))) atTop (𝓝 0)) : spectrum ℂ T={0} := by
  have hr : spectralRadius ℂ T=0 := by
    apply tendsto_nhds_unique (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius T)
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hT
  have hsub : spectrum ℂ T⊆{0} := by
    intro z hz
    have hle : (‖z‖₊:ℝ≥0∞)≤ spectralRadius ℂ T := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)
    rw [hr] at hle
    have hz0 : ‖z‖₊=0 := by exact_mod_cast (le_zero_iff.mp hle)
    simpa only [Set.mem_singleton_iff,nnnorm_eq_zero] using hz0
  apply Set.Subset.antisymm hsub
  rw [Set.singleton_subset_iff]
  obtain ⟨z,hz⟩ := spectrum.nonempty T
  have hz0 : z=0 := hsub hz
  simpa only [hz0] using hz
end FiniteFactor
end

end OAI

import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.OuterTemplatePrimitive

namespace OAI


noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma exists_outerTemplate_deriv_bound {M0 K eta:ℝ} (heta:0 < eta) (heta1:eta ≤ 1/128) :
    ∃C:ℝ,0 ≤ C ∧ ∀s,|deriv (outerTemplate M0 K eta) s| ≤ C := by
  have hc:Continuous (deriv (outerTemplate M0 K eta)) :=
    (outerTemplate_smooth M0 K eta).continuous_deriv (by simp)
  obtain ⟨C,hC⟩:= (isCompact_Icc : IsCompact (Icc (-1) (2:ℝ))).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s
  by_cases hs:s∈Icc (-1) (2:ℝ)
  · exact (hC s hs).trans (le_max_left _ _)
  have hd:deriv (outerTemplate M0 K eta) s=0 := by
    have hh:s < -1 ∨ 2 < s := by simpa only [mem_Icc,not_and_or,not_le] using hs
    rcases hh with h | h
    · have he:outerTemplate M0 K eta =ᶠ[𝓝 s] outerPrimitive M0 K eta := by
        filter_upwards [eventually_lt_nhds (show s<1-eta by linarith only [h,heta1])] with t ht
        exact outerTemplate_eq_primitive heta ht.le
      rw [he.deriv_eq,(hasDerivAt_outerPrimitive M0 K eta s).deriv]
      exact outerVelocity_zero_left heta (by linarith only [h,heta1])
    · have he:outerTemplate M0 K eta =ᶠ[𝓝 s] (fun _=>0) := by
        filter_upwards [eventually_gt_nhds (show 1<s by linarith only [h])] with t ht
        exact outerTemplate_zero heta ht.le
      rw [he.deriv_eq,deriv_const]
  rw [hd,abs_zero]
  exact le_max_right _ _

end WeakMTWTransport

end

end OAI

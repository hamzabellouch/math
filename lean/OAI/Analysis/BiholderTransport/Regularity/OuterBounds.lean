import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.OuterTemplate

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma outerJ_add_integral (K M η a b:ℝ) :
    outerJ K M η a + ∫q in a..b,outerW K M η q = outerJ K M η b := by
  have hc := (outerW_contDiff K M η).continuous
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  unfold outerJ
  linarith only [hh]
end WeakMTWTransport

end

end OAI

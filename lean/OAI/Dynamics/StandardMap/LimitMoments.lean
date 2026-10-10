import OAI.Dynamics.StandardMap.VagueBounds

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma test_integrable_multi (j : ArrayTestIndex) :
    Integrable (fun d : NonAffineArray => arrayTest j d.val) L.multi := by
  obtain ⟨C,hC⟩ := S.multiLaw_test_bound j
  exact (vague_integrable_bound L.filter (fun i => nonaffinePart (S.multiLaw i)) L.multi L.multi_converges
    _ ((continuous_arrayTest j).comp continuous_subtype_val) (fun d => arrayTest_nonneg j d.val)
    (max C 0) (le_max_right _ _) (fun i => integrable_nonaffinePart _ _ (continuous_arrayTest j))
    (by filter_upwards [L.refines hC] with i hi
        exact (integral_nonaffinePart_le _ _ (continuous_arrayTest j) (arrayTest_nonneg j)).trans
          (hi.trans (le_max_left _ _)))).1
lemma test_integrable_terminal (j : ArrayTestIndex) :
    Integrable (fun d : NonAffineArray => arrayTest j d.val) L.terminal := by
  obtain ⟨C,hC⟩ := S.terminalLaw_test_bound j
  exact (vague_integrable_bound L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    _ ((continuous_arrayTest j).comp continuous_subtype_val) (fun d => arrayTest_nonneg j d.val)
    (max C 0) (le_max_right _ _) (fun i => integrable_nonaffinePart _ _ (continuous_arrayTest j))
    (by filter_upwards [L.refines hC] with i hi
        exact (integral_nonaffinePart_le _ _ (continuous_arrayTest j) (arrayTest_nonneg j)).trans
          (hi.trans (le_max_left _ _)))).1
end CriticalScaleSequence
end StandardMapEntropy

end OAI

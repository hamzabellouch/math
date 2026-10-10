import OAI.Dynamics.StandardMap.ShapeClassification

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma shape_aemulti : ∀ᵐd ∂L.multi,SlowShape (realArray d.val) (999/1000) := by
  filter_upwards [S.unit_aemulti L,S.tree_aemulti L,S.slowPair_aemulti L,S.noCancellation_aemulti L] with d hu ht hp hf
  exact slowShape_of_exclusions (realArray_treeLine d.val hu ht) (continuous_realArray d.val hu)
    (nonaffine_realArray d hu) hp (by norm_num) (by norm_num) hf
lemma shape_aeterminal : ∀ᵐd ∂L.terminal,SlowShape (realArray d.val) (999/1000) := by
  filter_upwards [S.unit_aeterminal L,S.tree_aeterminal L,S.slowPair_aeterminal L,S.noCancellation_aeterminal L] with d hu ht hp hf
  exact slowShape_of_exclusions (realArray_treeLine d.val hu ht) (continuous_realArray d.val hu)
    (nonaffine_realArray d hu) hp (by norm_num) (by norm_num) hf
end CriticalScaleSequence
end StandardMapEntropy

end OAI

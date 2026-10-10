import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by700_702 : By passesAt 700 702 := by
  apply byRun passesAt 700 2 702
  · rfl
  decide +kernel
lemma by702_705 : By passesAt 702 705 := by
  apply byRun passesAt 702 3 705
  · rfl
  decide +kernel
lemma by700_705 : By passesAt 700 705 := byJoin by700_702 by702_705
lemma by705_707 : By passesAt 705 707 := by
  apply byRun passesAt 705 2 707
  · rfl
  decide +kernel
lemma by707_710 : By passesAt 707 710 := by
  apply byRun passesAt 707 3 710
  · rfl
  decide +kernel
lemma by705_710 : By passesAt 705 710 := byJoin by705_707 by707_710
lemma by700_710 : By passesAt 700 710 := byJoin by700_705 by705_710
lemma by710_712 : By passesAt 710 712 := by
  apply byRun passesAt 710 2 712
  · rfl
  decide +kernel
lemma by712_715 : By passesAt 712 715 := by
  apply byRun passesAt 712 3 715
  · rfl
  decide +kernel
lemma by710_715 : By passesAt 710 715 := byJoin by710_712 by712_715
lemma by715_717 : By passesAt 715 717 := by
  apply byRun passesAt 715 2 717
  · rfl
  decide +kernel
lemma by717_720 : By passesAt 717 720 := by
  apply byRun passesAt 717 3 720
  · rfl
  decide +kernel
lemma by715_720 : By passesAt 715 720 := byJoin by715_717 by717_720
lemma by710_720 : By passesAt 710 720 := byJoin by710_715 by715_720
lemma by700_720 : By passesAt 700 720 := byJoin by700_710 by710_720
end GeneralMahler.SCal.Grid.Nodes

end OAI

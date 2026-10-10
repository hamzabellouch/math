import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by680_682 : By passesAt 680 682 := by
  apply byRun passesAt 680 2 682
  · rfl
  decide +kernel
lemma by682_685 : By passesAt 682 685 := by
  apply byRun passesAt 682 3 685
  · rfl
  decide +kernel
lemma by680_685 : By passesAt 680 685 := byJoin by680_682 by682_685
lemma by685_687 : By passesAt 685 687 := by
  apply byRun passesAt 685 2 687
  · rfl
  decide +kernel
lemma by687_690 : By passesAt 687 690 := by
  apply byRun passesAt 687 3 690
  · rfl
  decide +kernel
lemma by685_690 : By passesAt 685 690 := byJoin by685_687 by687_690
lemma by680_690 : By passesAt 680 690 := byJoin by680_685 by685_690
lemma by690_692 : By passesAt 690 692 := by
  apply byRun passesAt 690 2 692
  · rfl
  decide +kernel
lemma by692_695 : By passesAt 692 695 := by
  apply byRun passesAt 692 3 695
  · rfl
  decide +kernel
lemma by690_695 : By passesAt 690 695 := byJoin by690_692 by692_695
lemma by695_697 : By passesAt 695 697 := by
  apply byRun passesAt 695 2 697
  · rfl
  decide +kernel
lemma by697_700 : By passesAt 697 700 := by
  apply byRun passesAt 697 3 700
  · rfl
  decide +kernel
lemma by695_700 : By passesAt 695 700 := byJoin by695_697 by697_700
lemma by690_700 : By passesAt 690 700 := byJoin by690_695 by695_700
lemma by680_700 : By passesAt 680 700 := byJoin by680_690 by690_700
end GeneralMahler.SCal.Grid.Nodes

end OAI

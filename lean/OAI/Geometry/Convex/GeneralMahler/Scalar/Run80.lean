import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by80_82 : By passesAt 80 82 := by
  apply byRun passesAt 80 2 82
  · rfl
  decide +kernel
lemma by82_85 : By passesAt 82 85 := by
  apply byRun passesAt 82 3 85
  · rfl
  decide +kernel
lemma by80_85 : By passesAt 80 85 := byJoin by80_82 by82_85
lemma by85_87 : By passesAt 85 87 := by
  apply byRun passesAt 85 2 87
  · rfl
  decide +kernel
lemma by87_90 : By passesAt 87 90 := by
  apply byRun passesAt 87 3 90
  · rfl
  decide +kernel
lemma by85_90 : By passesAt 85 90 := byJoin by85_87 by87_90
lemma by80_90 : By passesAt 80 90 := byJoin by80_85 by85_90
lemma by90_92 : By passesAt 90 92 := by
  apply byRun passesAt 90 2 92
  · rfl
  decide +kernel
lemma by92_95 : By passesAt 92 95 := by
  apply byRun passesAt 92 3 95
  · rfl
  decide +kernel
lemma by90_95 : By passesAt 90 95 := byJoin by90_92 by92_95
lemma by95_97 : By passesAt 95 97 := by
  apply byRun passesAt 95 2 97
  · rfl
  decide +kernel
lemma by97_100 : By passesAt 97 100 := by
  apply byRun passesAt 97 3 100
  · rfl
  decide +kernel
lemma by95_100 : By passesAt 95 100 := byJoin by95_97 by97_100
lemma by90_100 : By passesAt 90 100 := byJoin by90_95 by95_100
lemma by80_100 : By passesAt 80 100 := byJoin by80_90 by90_100
end GeneralMahler.SCal.Grid.Nodes

end OAI

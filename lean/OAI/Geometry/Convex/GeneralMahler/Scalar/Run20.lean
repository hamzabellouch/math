import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by20_22 : By passesAt 20 22 := by
  apply byRun passesAt 20 2 22
  · rfl
  decide +kernel
lemma by22_25 : By passesAt 22 25 := by
  apply byRun passesAt 22 3 25
  · rfl
  decide +kernel
lemma by20_25 : By passesAt 20 25 := byJoin by20_22 by22_25
lemma by25_27 : By passesAt 25 27 := by
  apply byRun passesAt 25 2 27
  · rfl
  decide +kernel
lemma by27_30 : By passesAt 27 30 := by
  apply byRun passesAt 27 3 30
  · rfl
  decide +kernel
lemma by25_30 : By passesAt 25 30 := byJoin by25_27 by27_30
lemma by20_30 : By passesAt 20 30 := byJoin by20_25 by25_30
lemma by30_32 : By passesAt 30 32 := by
  apply byRun passesAt 30 2 32
  · rfl
  decide +kernel
lemma by32_35 : By passesAt 32 35 := by
  apply byRun passesAt 32 3 35
  · rfl
  decide +kernel
lemma by30_35 : By passesAt 30 35 := byJoin by30_32 by32_35
lemma by35_37 : By passesAt 35 37 := by
  apply byRun passesAt 35 2 37
  · rfl
  decide +kernel
lemma by37_40 : By passesAt 37 40 := by
  apply byRun passesAt 37 3 40
  · rfl
  decide +kernel
lemma by35_40 : By passesAt 35 40 := byJoin by35_37 by37_40
lemma by30_40 : By passesAt 30 40 := byJoin by30_35 by35_40
lemma by20_40 : By passesAt 20 40 := byJoin by20_30 by30_40
end GeneralMahler.SCal.Grid.Nodes

end OAI

import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by60_62 : By passesAt 60 62 := by
  apply byRun passesAt 60 2 62
  · rfl
  decide +kernel
lemma by62_65 : By passesAt 62 65 := by
  apply byRun passesAt 62 3 65
  · rfl
  decide +kernel
lemma by60_65 : By passesAt 60 65 := byJoin by60_62 by62_65
lemma by65_67 : By passesAt 65 67 := by
  apply byRun passesAt 65 2 67
  · rfl
  decide +kernel
lemma by67_70 : By passesAt 67 70 := by
  apply byRun passesAt 67 3 70
  · rfl
  decide +kernel
lemma by65_70 : By passesAt 65 70 := byJoin by65_67 by67_70
lemma by60_70 : By passesAt 60 70 := byJoin by60_65 by65_70
lemma by70_72 : By passesAt 70 72 := by
  apply byRun passesAt 70 2 72
  · rfl
  decide +kernel
lemma by72_75 : By passesAt 72 75 := by
  apply byRun passesAt 72 3 75
  · rfl
  decide +kernel
lemma by70_75 : By passesAt 70 75 := byJoin by70_72 by72_75
lemma by75_77 : By passesAt 75 77 := by
  apply byRun passesAt 75 2 77
  · rfl
  decide +kernel
lemma by77_80 : By passesAt 77 80 := by
  apply byRun passesAt 77 3 80
  · rfl
  decide +kernel
lemma by75_80 : By passesAt 75 80 := byJoin by75_77 by77_80
lemma by70_80 : By passesAt 70 80 := byJoin by70_75 by75_80
lemma by60_80 : By passesAt 60 80 := byJoin by60_70 by70_80
end GeneralMahler.SCal.Grid.Nodes

end OAI

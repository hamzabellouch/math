import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by40_42 : By passesAt 40 42 := by
  apply byRun passesAt 40 2 42
  · rfl
  decide +kernel
lemma by42_45 : By passesAt 42 45 := by
  apply byRun passesAt 42 3 45
  · rfl
  decide +kernel
lemma by40_45 : By passesAt 40 45 := byJoin by40_42 by42_45
lemma by45_47 : By passesAt 45 47 := by
  apply byRun passesAt 45 2 47
  · rfl
  decide +kernel
lemma by47_50 : By passesAt 47 50 := by
  apply byRun passesAt 47 3 50
  · rfl
  decide +kernel
lemma by45_50 : By passesAt 45 50 := byJoin by45_47 by47_50
lemma by40_50 : By passesAt 40 50 := byJoin by40_45 by45_50
lemma by50_52 : By passesAt 50 52 := by
  apply byRun passesAt 50 2 52
  · rfl
  decide +kernel
lemma by52_55 : By passesAt 52 55 := by
  apply byRun passesAt 52 3 55
  · rfl
  decide +kernel
lemma by50_55 : By passesAt 50 55 := byJoin by50_52 by52_55
lemma by55_57 : By passesAt 55 57 := by
  apply byRun passesAt 55 2 57
  · rfl
  decide +kernel
lemma by57_60 : By passesAt 57 60 := by
  apply byRun passesAt 57 3 60
  · rfl
  decide +kernel
lemma by55_60 : By passesAt 55 60 := byJoin by55_57 by57_60
lemma by50_60 : By passesAt 50 60 := byJoin by50_55 by55_60
lemma by40_60 : By passesAt 40 60 := byJoin by40_50 by50_60
end GeneralMahler.SCal.Grid.Nodes

end OAI

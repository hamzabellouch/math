import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by340_342 : By passesAt 340 342 := by
  apply byRun passesAt 340 2 342
  · rfl
  decide +kernel
lemma by342_345 : By passesAt 342 345 := by
  apply byRun passesAt 342 3 345
  · rfl
  decide +kernel
lemma by340_345 : By passesAt 340 345 := byJoin by340_342 by342_345
lemma by345_347 : By passesAt 345 347 := by
  apply byRun passesAt 345 2 347
  · rfl
  decide +kernel
lemma by347_350 : By passesAt 347 350 := by
  apply byRun passesAt 347 3 350
  · rfl
  decide +kernel
lemma by345_350 : By passesAt 345 350 := byJoin by345_347 by347_350
lemma by340_350 : By passesAt 340 350 := byJoin by340_345 by345_350
lemma by350_352 : By passesAt 350 352 := by
  apply byRun passesAt 350 2 352
  · rfl
  decide +kernel
lemma by352_355 : By passesAt 352 355 := by
  apply byRun passesAt 352 3 355
  · rfl
  decide +kernel
lemma by350_355 : By passesAt 350 355 := byJoin by350_352 by352_355
lemma by355_357 : By passesAt 355 357 := by
  apply byRun passesAt 355 2 357
  · rfl
  decide +kernel
lemma by357_360 : By passesAt 357 360 := by
  apply byRun passesAt 357 3 360
  · rfl
  decide +kernel
lemma by355_360 : By passesAt 355 360 := byJoin by355_357 by357_360
lemma by350_360 : By passesAt 350 360 := byJoin by350_355 by355_360
lemma by340_360 : By passesAt 340 360 := byJoin by340_350 by350_360
end GeneralMahler.SCal.Grid.Nodes

end OAI

import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by360_362 : By passesAt 360 362 := by
  apply byRun passesAt 360 2 362
  · rfl
  decide +kernel
lemma by362_365 : By passesAt 362 365 := by
  apply byRun passesAt 362 3 365
  · rfl
  decide +kernel
lemma by360_365 : By passesAt 360 365 := byJoin by360_362 by362_365
lemma by365_367 : By passesAt 365 367 := by
  apply byRun passesAt 365 2 367
  · rfl
  decide +kernel
lemma by367_370 : By passesAt 367 370 := by
  apply byRun passesAt 367 3 370
  · rfl
  decide +kernel
lemma by365_370 : By passesAt 365 370 := byJoin by365_367 by367_370
lemma by360_370 : By passesAt 360 370 := byJoin by360_365 by365_370
lemma by370_372 : By passesAt 370 372 := by
  apply byRun passesAt 370 2 372
  · rfl
  decide +kernel
lemma by372_375 : By passesAt 372 375 := by
  apply byRun passesAt 372 3 375
  · rfl
  decide +kernel
lemma by370_375 : By passesAt 370 375 := byJoin by370_372 by372_375
lemma by375_377 : By passesAt 375 377 := by
  apply byRun passesAt 375 2 377
  · rfl
  decide +kernel
lemma by377_380 : By passesAt 377 380 := by
  apply byRun passesAt 377 3 380
  · rfl
  decide +kernel
lemma by375_380 : By passesAt 375 380 := byJoin by375_377 by377_380
lemma by370_380 : By passesAt 370 380 := byJoin by370_375 by375_380
lemma by360_380 : By passesAt 360 380 := byJoin by360_370 by370_380
end GeneralMahler.SCal.Grid.Nodes

end OAI

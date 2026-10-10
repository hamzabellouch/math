import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by380_382 : By passesAt 380 382 := by
  apply byRun passesAt 380 2 382
  · rfl
  decide +kernel
lemma by382_385 : By passesAt 382 385 := by
  apply byRun passesAt 382 3 385
  · rfl
  decide +kernel
lemma by380_385 : By passesAt 380 385 := byJoin by380_382 by382_385
lemma by385_387 : By passesAt 385 387 := by
  apply byRun passesAt 385 2 387
  · rfl
  decide +kernel
lemma by387_390 : By passesAt 387 390 := by
  apply byRun passesAt 387 3 390
  · rfl
  decide +kernel
lemma by385_390 : By passesAt 385 390 := byJoin by385_387 by387_390
lemma by380_390 : By passesAt 380 390 := byJoin by380_385 by385_390
lemma by390_392 : By passesAt 390 392 := by
  apply byRun passesAt 390 2 392
  · rfl
  decide +kernel
lemma by392_395 : By passesAt 392 395 := by
  apply byRun passesAt 392 3 395
  · rfl
  decide +kernel
lemma by390_395 : By passesAt 390 395 := byJoin by390_392 by392_395
lemma by395_397 : By passesAt 395 397 := by
  apply byRun passesAt 395 2 397
  · rfl
  decide +kernel
lemma by397_400 : By passesAt 397 400 := by
  apply byRun passesAt 397 3 400
  · rfl
  decide +kernel
lemma by395_400 : By passesAt 395 400 := byJoin by395_397 by397_400
lemma by390_400 : By passesAt 390 400 := byJoin by390_395 by395_400
lemma by380_400 : By passesAt 380 400 := byJoin by380_390 by390_400
end GeneralMahler.SCal.Grid.Nodes

end OAI

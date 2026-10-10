import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by320_322 : By passesAt 320 322 := by
  apply byRun passesAt 320 2 322
  · rfl
  decide +kernel
lemma by322_325 : By passesAt 322 325 := by
  apply byRun passesAt 322 3 325
  · rfl
  decide +kernel
lemma by320_325 : By passesAt 320 325 := byJoin by320_322 by322_325
lemma by325_327 : By passesAt 325 327 := by
  apply byRun passesAt 325 2 327
  · rfl
  decide +kernel
lemma by327_330 : By passesAt 327 330 := by
  apply byRun passesAt 327 3 330
  · rfl
  decide +kernel
lemma by325_330 : By passesAt 325 330 := byJoin by325_327 by327_330
lemma by320_330 : By passesAt 320 330 := byJoin by320_325 by325_330
lemma by330_332 : By passesAt 330 332 := by
  apply byRun passesAt 330 2 332
  · rfl
  decide +kernel
lemma by332_335 : By passesAt 332 335 := by
  apply byRun passesAt 332 3 335
  · rfl
  decide +kernel
lemma by330_335 : By passesAt 330 335 := byJoin by330_332 by332_335
lemma by335_337 : By passesAt 335 337 := by
  apply byRun passesAt 335 2 337
  · rfl
  decide +kernel
lemma by337_340 : By passesAt 337 340 := by
  apply byRun passesAt 337 3 340
  · rfl
  decide +kernel
lemma by335_340 : By passesAt 335 340 := byJoin by335_337 by337_340
lemma by330_340 : By passesAt 330 340 := byJoin by330_335 by335_340
lemma by320_340 : By passesAt 320 340 := byJoin by320_330 by330_340
end GeneralMahler.SCal.Grid.Nodes

end OAI

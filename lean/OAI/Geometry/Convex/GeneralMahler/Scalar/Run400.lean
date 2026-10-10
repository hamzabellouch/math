import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by400_402 : By passesAt 400 402 := by
  apply byRun passesAt 400 2 402
  · rfl
  decide +kernel
lemma by402_405 : By passesAt 402 405 := by
  apply byRun passesAt 402 3 405
  · rfl
  decide +kernel
lemma by400_405 : By passesAt 400 405 := byJoin by400_402 by402_405
lemma by405_407 : By passesAt 405 407 := by
  apply byRun passesAt 405 2 407
  · rfl
  decide +kernel
lemma by407_410 : By passesAt 407 410 := by
  apply byRun passesAt 407 3 410
  · rfl
  decide +kernel
lemma by405_410 : By passesAt 405 410 := byJoin by405_407 by407_410
lemma by400_410 : By passesAt 400 410 := byJoin by400_405 by405_410
lemma by410_412 : By passesAt 410 412 := by
  apply byRun passesAt 410 2 412
  · rfl
  decide +kernel
lemma by412_415 : By passesAt 412 415 := by
  apply byRun passesAt 412 3 415
  · rfl
  decide +kernel
lemma by410_415 : By passesAt 410 415 := byJoin by410_412 by412_415
lemma by415_417 : By passesAt 415 417 := by
  apply byRun passesAt 415 2 417
  · rfl
  decide +kernel
lemma by417_420 : By passesAt 417 420 := by
  apply byRun passesAt 417 3 420
  · rfl
  decide +kernel
lemma by415_420 : By passesAt 415 420 := byJoin by415_417 by417_420
lemma by410_420 : By passesAt 410 420 := byJoin by410_415 by415_420
lemma by400_420 : By passesAt 400 420 := byJoin by400_410 by410_420
end GeneralMahler.SCal.Grid.Nodes

end OAI

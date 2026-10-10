import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by460_462 : By passesAt 460 462 := by
  apply byRun passesAt 460 2 462
  · rfl
  decide +kernel
lemma by462_465 : By passesAt 462 465 := by
  apply byRun passesAt 462 3 465
  · rfl
  decide +kernel
lemma by460_465 : By passesAt 460 465 := byJoin by460_462 by462_465
lemma by465_467 : By passesAt 465 467 := by
  apply byRun passesAt 465 2 467
  · rfl
  decide +kernel
lemma by467_470 : By passesAt 467 470 := by
  apply byRun passesAt 467 3 470
  · rfl
  decide +kernel
lemma by465_470 : By passesAt 465 470 := byJoin by465_467 by467_470
lemma by460_470 : By passesAt 460 470 := byJoin by460_465 by465_470
lemma by470_472 : By passesAt 470 472 := by
  apply byRun passesAt 470 2 472
  · rfl
  decide +kernel
lemma by472_475 : By passesAt 472 475 := by
  apply byRun passesAt 472 3 475
  · rfl
  decide +kernel
lemma by470_475 : By passesAt 470 475 := byJoin by470_472 by472_475
lemma by475_477 : By passesAt 475 477 := by
  apply byRun passesAt 475 2 477
  · rfl
  decide +kernel
lemma by477_480 : By passesAt 477 480 := by
  apply byRun passesAt 477 3 480
  · rfl
  decide +kernel
lemma by475_480 : By passesAt 475 480 := byJoin by475_477 by477_480
lemma by470_480 : By passesAt 470 480 := byJoin by470_475 by475_480
lemma by460_480 : By passesAt 460 480 := byJoin by460_470 by470_480
end GeneralMahler.SCal.Grid.Nodes

end OAI

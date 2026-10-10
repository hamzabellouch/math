import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by420_422 : By passesAt 420 422 := by
  apply byRun passesAt 420 2 422
  · rfl
  decide +kernel
lemma by422_425 : By passesAt 422 425 := by
  apply byRun passesAt 422 3 425
  · rfl
  decide +kernel
lemma by420_425 : By passesAt 420 425 := byJoin by420_422 by422_425
lemma by425_427 : By passesAt 425 427 := by
  apply byRun passesAt 425 2 427
  · rfl
  decide +kernel
lemma by427_430 : By passesAt 427 430 := by
  apply byRun passesAt 427 3 430
  · rfl
  decide +kernel
lemma by425_430 : By passesAt 425 430 := byJoin by425_427 by427_430
lemma by420_430 : By passesAt 420 430 := byJoin by420_425 by425_430
lemma by430_432 : By passesAt 430 432 := by
  apply byRun passesAt 430 2 432
  · rfl
  decide +kernel
lemma by432_435 : By passesAt 432 435 := by
  apply byRun passesAt 432 3 435
  · rfl
  decide +kernel
lemma by430_435 : By passesAt 430 435 := byJoin by430_432 by432_435
lemma by435_437 : By passesAt 435 437 := by
  apply byRun passesAt 435 2 437
  · rfl
  decide +kernel
lemma by437_440 : By passesAt 437 440 := by
  apply byRun passesAt 437 3 440
  · rfl
  decide +kernel
lemma by435_440 : By passesAt 435 440 := byJoin by435_437 by437_440
lemma by430_440 : By passesAt 430 440 := byJoin by430_435 by435_440
lemma by420_440 : By passesAt 420 440 := byJoin by420_430 by430_440
end GeneralMahler.SCal.Grid.Nodes

end OAI

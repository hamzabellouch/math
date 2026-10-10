import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by580_582 : By passesAt 580 582 := by
  apply byRun passesAt 580 2 582
  · rfl
  decide +kernel
lemma by582_585 : By passesAt 582 585 := by
  apply byRun passesAt 582 3 585
  · rfl
  decide +kernel
lemma by580_585 : By passesAt 580 585 := byJoin by580_582 by582_585
lemma by585_587 : By passesAt 585 587 := by
  apply byRun passesAt 585 2 587
  · rfl
  decide +kernel
lemma by587_590 : By passesAt 587 590 := by
  apply byRun passesAt 587 3 590
  · rfl
  decide +kernel
lemma by585_590 : By passesAt 585 590 := byJoin by585_587 by587_590
lemma by580_590 : By passesAt 580 590 := byJoin by580_585 by585_590
lemma by590_592 : By passesAt 590 592 := by
  apply byRun passesAt 590 2 592
  · rfl
  decide +kernel
lemma by592_595 : By passesAt 592 595 := by
  apply byRun passesAt 592 3 595
  · rfl
  decide +kernel
lemma by590_595 : By passesAt 590 595 := byJoin by590_592 by592_595
lemma by595_597 : By passesAt 595 597 := by
  apply byRun passesAt 595 2 597
  · rfl
  decide +kernel
lemma by597_600 : By passesAt 597 600 := by
  apply byRun passesAt 597 3 600
  · rfl
  decide +kernel
lemma by595_600 : By passesAt 595 600 := byJoin by595_597 by597_600
lemma by590_600 : By passesAt 590 600 := byJoin by590_595 by595_600
lemma by580_600 : By passesAt 580 600 := byJoin by580_590 by590_600
end GeneralMahler.SCal.Grid.Nodes

end OAI

import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by500_502 : By passesAt 500 502 := by
  apply byRun passesAt 500 2 502
  · rfl
  decide +kernel
lemma by502_505 : By passesAt 502 505 := by
  apply byRun passesAt 502 3 505
  · rfl
  decide +kernel
lemma by500_505 : By passesAt 500 505 := byJoin by500_502 by502_505
lemma by505_507 : By passesAt 505 507 := by
  apply byRun passesAt 505 2 507
  · rfl
  decide +kernel
lemma by507_510 : By passesAt 507 510 := by
  apply byRun passesAt 507 3 510
  · rfl
  decide +kernel
lemma by505_510 : By passesAt 505 510 := byJoin by505_507 by507_510
lemma by500_510 : By passesAt 500 510 := byJoin by500_505 by505_510
lemma by510_512 : By passesAt 510 512 := by
  apply byRun passesAt 510 2 512
  · rfl
  decide +kernel
lemma by512_515 : By passesAt 512 515 := by
  apply byRun passesAt 512 3 515
  · rfl
  decide +kernel
lemma by510_515 : By passesAt 510 515 := byJoin by510_512 by512_515
lemma by515_517 : By passesAt 515 517 := by
  apply byRun passesAt 515 2 517
  · rfl
  decide +kernel
lemma by517_520 : By passesAt 517 520 := by
  apply byRun passesAt 517 3 520
  · rfl
  decide +kernel
lemma by515_520 : By passesAt 515 520 := byJoin by515_517 by517_520
lemma by510_520 : By passesAt 510 520 := byJoin by510_515 by515_520
lemma by500_520 : By passesAt 500 520 := byJoin by500_510 by510_520
end GeneralMahler.SCal.Grid.Nodes

end OAI

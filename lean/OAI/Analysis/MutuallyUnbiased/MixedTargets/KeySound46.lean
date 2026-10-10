import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical319

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1472) =
      Integer.Sparse.eval keyMomentRow1472 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1472).leftCharge (GramAssembly.key 1472).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2094) := by
    have ha : gramCharges (GramAssembly.key 1472).leftCharge (GramAssembly.key 1472).rightCharge = raw40890 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40890Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40890 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1472).leftCharge (GramAssembly.key 1472).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1472, Integer.Sparse.eval]

theorem keyMoment1473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1473) =
      Integer.Sparse.eval keyMomentRow1473 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1473).leftCharge (GramAssembly.key 1473).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1816) := by
    have ha : gramCharges (GramAssembly.key 1473).leftCharge (GramAssembly.key 1473).rightCharge = raw40891 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40891Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40891 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1473).leftCharge (GramAssembly.key 1473).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1473, Integer.Sparse.eval]

theorem keyMoment1474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1474) =
      Integer.Sparse.eval keyMomentRow1474 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1474).leftCharge (GramAssembly.key 1474).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1977) := by
    have ha : gramCharges (GramAssembly.key 1474).leftCharge (GramAssembly.key 1474).rightCharge = raw40892 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40892Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40892 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1474).leftCharge (GramAssembly.key 1474).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1474, Integer.Sparse.eval]

theorem keyMoment1475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1475) =
      Integer.Sparse.eval keyMomentRow1475 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1475).leftCharge (GramAssembly.key 1475).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1794) := by
    have ha : gramCharges (GramAssembly.key 1475).leftCharge (GramAssembly.key 1475).rightCharge = raw40893 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40893Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40893 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1475).leftCharge (GramAssembly.key 1475).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1475, Integer.Sparse.eval]

theorem keyMoment1476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1476) =
      Integer.Sparse.eval keyMomentRow1476 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1476).leftCharge (GramAssembly.key 1476).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2758) := by
    have ha : gramCharges (GramAssembly.key 1476).leftCharge (GramAssembly.key 1476).rightCharge = raw40894 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40894Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40894 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1476).leftCharge (GramAssembly.key 1476).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1476, Integer.Sparse.eval]

theorem keyMoment1477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1477) =
      Integer.Sparse.eval keyMomentRow1477 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1477).leftCharge (GramAssembly.key 1477).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3083) := by
    have ha : gramCharges (GramAssembly.key 1477).leftCharge (GramAssembly.key 1477).rightCharge = raw40895 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40895Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40895 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1477).leftCharge (GramAssembly.key 1477).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1477, Integer.Sparse.eval]

theorem keyMoment1478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1478) =
      Integer.Sparse.eval keyMomentRow1478 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1478).leftCharge (GramAssembly.key 1478).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3780) := by
    have ha : gramCharges (GramAssembly.key 1478).leftCharge (GramAssembly.key 1478).rightCharge = raw40896 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40896Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40896 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1478).leftCharge (GramAssembly.key 1478).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1478, Integer.Sparse.eval]

theorem keyMoment1479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1479) =
      Integer.Sparse.eval keyMomentRow1479 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1479).leftCharge (GramAssembly.key 1479).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3783) := by
    have ha : gramCharges (GramAssembly.key 1479).leftCharge (GramAssembly.key 1479).rightCharge = raw40897 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40897Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40897 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1479).leftCharge (GramAssembly.key 1479).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1479, Integer.Sparse.eval]

theorem keyMoment1480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1480) =
      Integer.Sparse.eval keyMomentRow1480 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1480).leftCharge (GramAssembly.key 1480).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3710) := by
    have ha : gramCharges (GramAssembly.key 1480).leftCharge (GramAssembly.key 1480).rightCharge = raw40898 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40898Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40898 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1480).leftCharge (GramAssembly.key 1480).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1480, Integer.Sparse.eval]

theorem keyMoment1481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1481) =
      Integer.Sparse.eval keyMomentRow1481 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1481).leftCharge (GramAssembly.key 1481).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3699) := by
    have ha : gramCharges (GramAssembly.key 1481).leftCharge (GramAssembly.key 1481).rightCharge = raw40899 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40899Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40899 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1481).leftCharge (GramAssembly.key 1481).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1481, Integer.Sparse.eval]

theorem keyMoment1482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1482) =
      Integer.Sparse.eval keyMomentRow1482 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1482).leftCharge (GramAssembly.key 1482).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2819) := by
    have ha : gramCharges (GramAssembly.key 1482).leftCharge (GramAssembly.key 1482).rightCharge = raw40900 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40900Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40900 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1482).leftCharge (GramAssembly.key 1482).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1482, Integer.Sparse.eval]

theorem keyMoment1483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1483) =
      Integer.Sparse.eval keyMomentRow1483 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1483).leftCharge (GramAssembly.key 1483).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3676) := by
    have ha : gramCharges (GramAssembly.key 1483).leftCharge (GramAssembly.key 1483).rightCharge = raw40901 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40901Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40901 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1483).leftCharge (GramAssembly.key 1483).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1483, Integer.Sparse.eval]

theorem keyMoment1484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1484) =
      Integer.Sparse.eval keyMomentRow1484 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1484).leftCharge (GramAssembly.key 1484).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2801) := by
    have ha : gramCharges (GramAssembly.key 1484).leftCharge (GramAssembly.key 1484).rightCharge = raw40902 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40902Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40902 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1484).leftCharge (GramAssembly.key 1484).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1484, Integer.Sparse.eval]

theorem keyMoment1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1485) =
      Integer.Sparse.eval keyMomentRow1485 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1485).leftCharge (GramAssembly.key 1485).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3673) := by
    have ha : gramCharges (GramAssembly.key 1485).leftCharge (GramAssembly.key 1485).rightCharge = raw40903 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40903Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40903 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1485).leftCharge (GramAssembly.key 1485).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1485, Integer.Sparse.eval]

theorem keyMoment1486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1486) =
      Integer.Sparse.eval keyMomentRow1486 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1486).leftCharge (GramAssembly.key 1486).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3685) := by
    have ha : gramCharges (GramAssembly.key 1486).leftCharge (GramAssembly.key 1486).rightCharge = raw40904 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40904Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40904 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1486).leftCharge (GramAssembly.key 1486).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1486, Integer.Sparse.eval]

theorem keyMoment1487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1487) =
      Integer.Sparse.eval keyMomentRow1487 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1487).leftCharge (GramAssembly.key 1487).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2745) := by
    have ha : gramCharges (GramAssembly.key 1487).leftCharge (GramAssembly.key 1487).rightCharge = raw40905 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40905Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40905 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1487).leftCharge (GramAssembly.key 1487).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1487, Integer.Sparse.eval]

theorem keyMoment1488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1488) =
      Integer.Sparse.eval keyMomentRow1488 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1488).leftCharge (GramAssembly.key 1488).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2898) := by
    have ha : gramCharges (GramAssembly.key 1488).leftCharge (GramAssembly.key 1488).rightCharge = raw40906 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40906Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40906 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1488).leftCharge (GramAssembly.key 1488).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1488, Integer.Sparse.eval]

theorem keyMoment1489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1489) =
      Integer.Sparse.eval keyMomentRow1489 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1489).leftCharge (GramAssembly.key 1489).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2499) := by
    have ha : gramCharges (GramAssembly.key 1489).leftCharge (GramAssembly.key 1489).rightCharge = raw40907 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40907Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40907 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1489).leftCharge (GramAssembly.key 1489).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1489, Integer.Sparse.eval]

theorem keyMoment1490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1490) =
      Integer.Sparse.eval keyMomentRow1490 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1490).leftCharge (GramAssembly.key 1490).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1141) := by
    have ha : gramCharges (GramAssembly.key 1490).leftCharge (GramAssembly.key 1490).rightCharge = raw40908 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40908Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40908 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1490).leftCharge (GramAssembly.key 1490).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1490, Integer.Sparse.eval]

theorem keyMoment1491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1491) =
      Integer.Sparse.eval keyMomentRow1491 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1491).leftCharge (GramAssembly.key 1491).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2441) := by
    have ha : gramCharges (GramAssembly.key 1491).leftCharge (GramAssembly.key 1491).rightCharge = raw40909 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40909Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40909 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1491).leftCharge (GramAssembly.key 1491).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1491, Integer.Sparse.eval]

theorem keyMoment1492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1492) =
      Integer.Sparse.eval keyMomentRow1492 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1492).leftCharge (GramAssembly.key 1492).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1117) := by
    have ha : gramCharges (GramAssembly.key 1492).leftCharge (GramAssembly.key 1492).rightCharge = raw40910 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40910Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40910 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1492).leftCharge (GramAssembly.key 1492).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1492, Integer.Sparse.eval]

theorem keyMoment1493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1493) =
      Integer.Sparse.eval keyMomentRow1493 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1493).leftCharge (GramAssembly.key 1493).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2433) := by
    have ha : gramCharges (GramAssembly.key 1493).leftCharge (GramAssembly.key 1493).rightCharge = raw40911 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40911Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40911 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1493).leftCharge (GramAssembly.key 1493).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1493, Integer.Sparse.eval]

theorem keyMoment1494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1494) =
      Integer.Sparse.eval keyMomentRow1494 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1494).leftCharge (GramAssembly.key 1494).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2473) := by
    have ha : gramCharges (GramAssembly.key 1494).leftCharge (GramAssembly.key 1494).rightCharge = raw40912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40912 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1494).leftCharge (GramAssembly.key 1494).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1494, Integer.Sparse.eval]

theorem keyMoment1495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1495) =
      Integer.Sparse.eval keyMomentRow1495 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1495).leftCharge (GramAssembly.key 1495).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1063) := by
    have ha : gramCharges (GramAssembly.key 1495).leftCharge (GramAssembly.key 1495).rightCharge = raw40913 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40913Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40913 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1495).leftCharge (GramAssembly.key 1495).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1495, Integer.Sparse.eval]

theorem keyMoment1496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1496) =
      Integer.Sparse.eval keyMomentRow1496 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1496).leftCharge (GramAssembly.key 1496).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 616) := by
    have ha : gramCharges (GramAssembly.key 1496).leftCharge (GramAssembly.key 1496).rightCharge = raw40914 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40914Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40914 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1496).leftCharge (GramAssembly.key 1496).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1496, Integer.Sparse.eval]

theorem keyMoment1497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1497) =
      Integer.Sparse.eval keyMomentRow1497 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1497).leftCharge (GramAssembly.key 1497).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 950) := by
    have ha : gramCharges (GramAssembly.key 1497).leftCharge (GramAssembly.key 1497).rightCharge = raw40915 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40915Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40915 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1497).leftCharge (GramAssembly.key 1497).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1497, Integer.Sparse.eval]

theorem keyMoment1498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1498) =
      Integer.Sparse.eval keyMomentRow1498 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1498).leftCharge (GramAssembly.key 1498).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 586) := by
    have ha : gramCharges (GramAssembly.key 1498).leftCharge (GramAssembly.key 1498).rightCharge = raw40916 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40916Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40916 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1498).leftCharge (GramAssembly.key 1498).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1498, Integer.Sparse.eval]

theorem keyMoment1499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1499) =
      Integer.Sparse.eval keyMomentRow1499 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1499).leftCharge (GramAssembly.key 1499).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1830) := by
    have ha : gramCharges (GramAssembly.key 1499).leftCharge (GramAssembly.key 1499).rightCharge = raw40917 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40917Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40917 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1499).leftCharge (GramAssembly.key 1499).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1499, Integer.Sparse.eval]

theorem keyMoment1500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1500) =
      Integer.Sparse.eval keyMomentRow1500 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1500).leftCharge (GramAssembly.key 1500).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1978) := by
    have ha : gramCharges (GramAssembly.key 1500).leftCharge (GramAssembly.key 1500).rightCharge = raw40918 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40918Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40918 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1500).leftCharge (GramAssembly.key 1500).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1500, Integer.Sparse.eval]

theorem keyMoment1501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1501) =
      Integer.Sparse.eval keyMomentRow1501 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1501).leftCharge (GramAssembly.key 1501).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1795) := by
    have ha : gramCharges (GramAssembly.key 1501).leftCharge (GramAssembly.key 1501).rightCharge = raw40919 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40919Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40919 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1501).leftCharge (GramAssembly.key 1501).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1501, Integer.Sparse.eval]

theorem keyMoment1502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1502) =
      Integer.Sparse.eval keyMomentRow1502 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1502).leftCharge (GramAssembly.key 1502).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2362) := by
    have ha : gramCharges (GramAssembly.key 1502).leftCharge (GramAssembly.key 1502).rightCharge = raw40920 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40920Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40920 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1502).leftCharge (GramAssembly.key 1502).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1502, Integer.Sparse.eval]

theorem keyMoment1503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1503) =
      Integer.Sparse.eval keyMomentRow1503 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1503).leftCharge (GramAssembly.key 1503).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2353) := by
    have ha : gramCharges (GramAssembly.key 1503).leftCharge (GramAssembly.key 1503).rightCharge = raw40921 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40921Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40921 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1503).leftCharge (GramAssembly.key 1503).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1503, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

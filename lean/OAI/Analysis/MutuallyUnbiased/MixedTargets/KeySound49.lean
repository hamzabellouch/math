import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical320

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1568) =
      Integer.Sparse.eval keyMomentRow1568 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1568).leftCharge (GramAssembly.key 1568).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 618) := by
    have ha : gramCharges (GramAssembly.key 1568).leftCharge (GramAssembly.key 1568).rightCharge = raw40986 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40986Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40986 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1568).leftCharge (GramAssembly.key 1568).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1568, Integer.Sparse.eval]

theorem keyMoment1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1569) =
      Integer.Sparse.eval keyMomentRow1569 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1569).leftCharge (GramAssembly.key 1569).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 613) := by
    have ha : gramCharges (GramAssembly.key 1569).leftCharge (GramAssembly.key 1569).rightCharge = raw40987 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40987Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40987 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1569).leftCharge (GramAssembly.key 1569).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1569, Integer.Sparse.eval]

theorem keyMoment1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1570) =
      Integer.Sparse.eval keyMomentRow1570 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1570).leftCharge (GramAssembly.key 1570).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1087) := by
    have ha : gramCharges (GramAssembly.key 1570).leftCharge (GramAssembly.key 1570).rightCharge = raw40988 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40988Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40988 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1570).leftCharge (GramAssembly.key 1570).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1570, Integer.Sparse.eval]

theorem keyMoment1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1571) =
      Integer.Sparse.eval keyMomentRow1571 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1571).leftCharge (GramAssembly.key 1571).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1049) := by
    have ha : gramCharges (GramAssembly.key 1571).leftCharge (GramAssembly.key 1571).rightCharge = raw40989 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40989Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40989 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1571).leftCharge (GramAssembly.key 1571).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1571, Integer.Sparse.eval]

theorem keyMoment1572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1572) =
      Integer.Sparse.eval keyMomentRow1572 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1572).leftCharge (GramAssembly.key 1572).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 937) := by
    have ha : gramCharges (GramAssembly.key 1572).leftCharge (GramAssembly.key 1572).rightCharge = raw40990 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40990Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40990 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1572).leftCharge (GramAssembly.key 1572).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1572, Integer.Sparse.eval]

theorem keyMoment1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1573) =
      Integer.Sparse.eval keyMomentRow1573 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1573).leftCharge (GramAssembly.key 1573).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1818) := by
    have ha : gramCharges (GramAssembly.key 1573).leftCharge (GramAssembly.key 1573).rightCharge = raw40991 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40991Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40991 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1573).leftCharge (GramAssembly.key 1573).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1573, Integer.Sparse.eval]

theorem keyMoment1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1574) =
      Integer.Sparse.eval keyMomentRow1574 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1574).leftCharge (GramAssembly.key 1574).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 610) := by
    have ha : gramCharges (GramAssembly.key 1574).leftCharge (GramAssembly.key 1574).rightCharge = raw40992 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40992Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40992 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1574).leftCharge (GramAssembly.key 1574).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1574, Integer.Sparse.eval]

theorem keyMoment1575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1575) =
      Integer.Sparse.eval keyMomentRow1575 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1575).leftCharge (GramAssembly.key 1575).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1044) := by
    have ha : gramCharges (GramAssembly.key 1575).leftCharge (GramAssembly.key 1575).rightCharge = raw40993 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40993Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40993 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1575).leftCharge (GramAssembly.key 1575).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1575, Integer.Sparse.eval]

theorem keyMoment1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1576) =
      Integer.Sparse.eval keyMomentRow1576 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1576).leftCharge (GramAssembly.key 1576).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 932) := by
    have ha : gramCharges (GramAssembly.key 1576).leftCharge (GramAssembly.key 1576).rightCharge = raw40994 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40994Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40994 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1576).leftCharge (GramAssembly.key 1576).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1576, Integer.Sparse.eval]

theorem keyMoment1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1577) =
      Integer.Sparse.eval keyMomentRow1577 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1577).leftCharge (GramAssembly.key 1577).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2341) := by
    have ha : gramCharges (GramAssembly.key 1577).leftCharge (GramAssembly.key 1577).rightCharge = raw40995 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40995Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40995 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1577).leftCharge (GramAssembly.key 1577).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1577, Integer.Sparse.eval]

theorem keyMoment1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1578) =
      Integer.Sparse.eval keyMomentRow1578 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1578).leftCharge (GramAssembly.key 1578).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 929) := by
    have ha : gramCharges (GramAssembly.key 1578).leftCharge (GramAssembly.key 1578).rightCharge = raw40996 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40996Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40996 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1578).leftCharge (GramAssembly.key 1578).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1578, Integer.Sparse.eval]

theorem keyMoment1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1579) =
      Integer.Sparse.eval keyMomentRow1579 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1579).leftCharge (GramAssembly.key 1579).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2338) := by
    have ha : gramCharges (GramAssembly.key 1579).leftCharge (GramAssembly.key 1579).rightCharge = raw40997 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40997Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40997 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1579).leftCharge (GramAssembly.key 1579).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1579, Integer.Sparse.eval]

theorem keyMoment1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1580) =
      Integer.Sparse.eval keyMomentRow1580 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1580).leftCharge (GramAssembly.key 1580).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 1580).leftCharge (GramAssembly.key 1580).rightCharge = raw40998 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40998Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40998 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1580).leftCharge (GramAssembly.key 1580).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1580, Integer.Sparse.eval]

theorem keyMoment1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1581) =
      Integer.Sparse.eval keyMomentRow1581 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1581).leftCharge (GramAssembly.key 1581).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2967) := by
    have ha : gramCharges (GramAssembly.key 1581).leftCharge (GramAssembly.key 1581).rightCharge = raw40999 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40999Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40999 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1581).leftCharge (GramAssembly.key 1581).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1581, Integer.Sparse.eval]

theorem keyMoment1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1582) =
      Integer.Sparse.eval keyMomentRow1582 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1582).leftCharge (GramAssembly.key 1582).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 1582).leftCharge (GramAssembly.key 1582).rightCharge = raw10829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw10829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical10829 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1582).leftCharge (GramAssembly.key 1582).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1582, Integer.Sparse.eval]

theorem keyMoment1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1583) =
      Integer.Sparse.eval keyMomentRow1583 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1583).leftCharge (GramAssembly.key 1583).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2888) := by
    have ha : gramCharges (GramAssembly.key 1583).leftCharge (GramAssembly.key 1583).rightCharge = raw41000 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41000Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41000 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1583).leftCharge (GramAssembly.key 1583).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1583, Integer.Sparse.eval]

theorem keyMoment1584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1584) =
      Integer.Sparse.eval keyMomentRow1584 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1584).leftCharge (GramAssembly.key 1584).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2952) := by
    have ha : gramCharges (GramAssembly.key 1584).leftCharge (GramAssembly.key 1584).rightCharge = raw41001 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41001Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41001 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1584).leftCharge (GramAssembly.key 1584).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1584, Integer.Sparse.eval]

theorem keyMoment1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1585) =
      Integer.Sparse.eval keyMomentRow1585 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1585).leftCharge (GramAssembly.key 1585).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2930) := by
    have ha : gramCharges (GramAssembly.key 1585).leftCharge (GramAssembly.key 1585).rightCharge = raw41002 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41002Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41002 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1585).leftCharge (GramAssembly.key 1585).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1585, Integer.Sparse.eval]

theorem keyMoment1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1586) =
      Integer.Sparse.eval keyMomentRow1586 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1586).leftCharge (GramAssembly.key 1586).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 1586).leftCharge (GramAssembly.key 1586).rightCharge = raw41003 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41003Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41003 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1586).leftCharge (GramAssembly.key 1586).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1586, Integer.Sparse.eval]

theorem keyMoment1587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1587) =
      Integer.Sparse.eval keyMomentRow1587 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1587).leftCharge (GramAssembly.key 1587).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2964) := by
    have ha : gramCharges (GramAssembly.key 1587).leftCharge (GramAssembly.key 1587).rightCharge = raw41004 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41004Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41004 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1587).leftCharge (GramAssembly.key 1587).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1587, Integer.Sparse.eval]

theorem keyMoment1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1588) =
      Integer.Sparse.eval keyMomentRow1588 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1588).leftCharge (GramAssembly.key 1588).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 1588).leftCharge (GramAssembly.key 1588).rightCharge = raw41005 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41005Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41005 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1588).leftCharge (GramAssembly.key 1588).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1588, Integer.Sparse.eval]

theorem keyMoment1589 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1589) =
      Integer.Sparse.eval keyMomentRow1589 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1589).leftCharge (GramAssembly.key 1589).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 1589).leftCharge (GramAssembly.key 1589).rightCharge = raw11232 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw11232Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical11232 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1589).leftCharge (GramAssembly.key 1589).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1589, Integer.Sparse.eval]

theorem keyMoment1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1590) =
      Integer.Sparse.eval keyMomentRow1590 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1590).leftCharge (GramAssembly.key 1590).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2885) := by
    have ha : gramCharges (GramAssembly.key 1590).leftCharge (GramAssembly.key 1590).rightCharge = raw41006 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41006Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41006 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1590).leftCharge (GramAssembly.key 1590).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1590, Integer.Sparse.eval]

theorem keyMoment1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1591) =
      Integer.Sparse.eval keyMomentRow1591 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1591).leftCharge (GramAssembly.key 1591).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2951) := by
    have ha : gramCharges (GramAssembly.key 1591).leftCharge (GramAssembly.key 1591).rightCharge = raw41007 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41007Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41007 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1591).leftCharge (GramAssembly.key 1591).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1591, Integer.Sparse.eval]

theorem keyMoment1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1592) =
      Integer.Sparse.eval keyMomentRow1592 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1592).leftCharge (GramAssembly.key 1592).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2928) := by
    have ha : gramCharges (GramAssembly.key 1592).leftCharge (GramAssembly.key 1592).rightCharge = raw41008 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41008Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41008 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1592).leftCharge (GramAssembly.key 1592).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1592, Integer.Sparse.eval]

theorem keyMoment1593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1593) =
      Integer.Sparse.eval keyMomentRow1593 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1593).leftCharge (GramAssembly.key 1593).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2878) := by
    have ha : gramCharges (GramAssembly.key 1593).leftCharge (GramAssembly.key 1593).rightCharge = raw41009 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41009Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41009 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1593).leftCharge (GramAssembly.key 1593).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1593, Integer.Sparse.eval]

theorem keyMoment1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1594) =
      Integer.Sparse.eval keyMomentRow1594 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1594).leftCharge (GramAssembly.key 1594).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 1594).leftCharge (GramAssembly.key 1594).rightCharge = raw41010 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41010Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41010 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1594).leftCharge (GramAssembly.key 1594).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1594, Integer.Sparse.eval]

theorem keyMoment1595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1595) =
      Integer.Sparse.eval keyMomentRow1595 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1595).leftCharge (GramAssembly.key 1595).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 1595).leftCharge (GramAssembly.key 1595).rightCharge = raw30961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw30961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical30961 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1595).leftCharge (GramAssembly.key 1595).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1595, Integer.Sparse.eval]

theorem keyMoment1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1596) =
      Integer.Sparse.eval keyMomentRow1596 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1596).leftCharge (GramAssembly.key 1596).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2886) := by
    have ha : gramCharges (GramAssembly.key 1596).leftCharge (GramAssembly.key 1596).rightCharge = raw41011 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41011Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41011 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1596).leftCharge (GramAssembly.key 1596).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1596, Integer.Sparse.eval]

theorem keyMoment1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1597) =
      Integer.Sparse.eval keyMomentRow1597 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1597).leftCharge (GramAssembly.key 1597).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2955) := by
    have ha : gramCharges (GramAssembly.key 1597).leftCharge (GramAssembly.key 1597).rightCharge = raw41012 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41012Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41012 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1597).leftCharge (GramAssembly.key 1597).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1597, Integer.Sparse.eval]

theorem keyMoment1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1598) =
      Integer.Sparse.eval keyMomentRow1598 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1598).leftCharge (GramAssembly.key 1598).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2865) := by
    have ha : gramCharges (GramAssembly.key 1598).leftCharge (GramAssembly.key 1598).rightCharge = raw41013 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41013Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41013 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1598).leftCharge (GramAssembly.key 1598).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1598, Integer.Sparse.eval]

theorem keyMoment1599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1599) =
      Integer.Sparse.eval keyMomentRow1599 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1599).leftCharge (GramAssembly.key 1599).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2882) := by
    have ha : gramCharges (GramAssembly.key 1599).leftCharge (GramAssembly.key 1599).rightCharge = raw41014 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41014Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41014 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1599).leftCharge (GramAssembly.key 1599).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1599, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

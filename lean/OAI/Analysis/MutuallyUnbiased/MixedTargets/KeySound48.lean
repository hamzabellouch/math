import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical319
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical320

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1536) =
      Integer.Sparse.eval keyMomentRow1536 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1536).leftCharge (GramAssembly.key 1536).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3782) := by
    have ha : gramCharges (GramAssembly.key 1536).leftCharge (GramAssembly.key 1536).rightCharge = raw40954 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40954Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40954 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1536).leftCharge (GramAssembly.key 1536).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1536, Integer.Sparse.eval]

theorem keyMoment1537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1537) =
      Integer.Sparse.eval keyMomentRow1537 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1537).leftCharge (GramAssembly.key 1537).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3801) := by
    have ha : gramCharges (GramAssembly.key 1537).leftCharge (GramAssembly.key 1537).rightCharge = raw40955 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40955Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40955 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1537).leftCharge (GramAssembly.key 1537).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1537, Integer.Sparse.eval]

theorem keyMoment1538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1538) =
      Integer.Sparse.eval keyMomentRow1538 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1538).leftCharge (GramAssembly.key 1538).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3719) := by
    have ha : gramCharges (GramAssembly.key 1538).leftCharge (GramAssembly.key 1538).rightCharge = raw40956 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40956Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40956 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1538).leftCharge (GramAssembly.key 1538).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1538, Integer.Sparse.eval]

theorem keyMoment1539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1539) =
      Integer.Sparse.eval keyMomentRow1539 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1539).leftCharge (GramAssembly.key 1539).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1802) := by
    have ha : gramCharges (GramAssembly.key 1539).leftCharge (GramAssembly.key 1539).rightCharge = raw40957 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40957Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40957 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1539).leftCharge (GramAssembly.key 1539).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1539, Integer.Sparse.eval]

theorem keyMoment1540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1540) =
      Integer.Sparse.eval keyMomentRow1540 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1540).leftCharge (GramAssembly.key 1540).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1819) := by
    have ha : gramCharges (GramAssembly.key 1540).leftCharge (GramAssembly.key 1540).rightCharge = raw40958 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40958Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40958 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1540).leftCharge (GramAssembly.key 1540).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1540, Integer.Sparse.eval]

theorem keyMoment1541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1541) =
      Integer.Sparse.eval keyMomentRow1541 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1541).leftCharge (GramAssembly.key 1541).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3397) := by
    have ha : gramCharges (GramAssembly.key 1541).leftCharge (GramAssembly.key 1541).rightCharge = raw40959 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40959Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40959 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1541).leftCharge (GramAssembly.key 1541).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1541, Integer.Sparse.eval]

theorem keyMoment1542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1542) =
      Integer.Sparse.eval keyMomentRow1542 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1542).leftCharge (GramAssembly.key 1542).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2817) := by
    have ha : gramCharges (GramAssembly.key 1542).leftCharge (GramAssembly.key 1542).rightCharge = raw40960 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40960Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40960 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1542).leftCharge (GramAssembly.key 1542).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1542, Integer.Sparse.eval]

theorem keyMoment1543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1543) =
      Integer.Sparse.eval keyMomentRow1543 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1543).leftCharge (GramAssembly.key 1543).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3706) := by
    have ha : gramCharges (GramAssembly.key 1543).leftCharge (GramAssembly.key 1543).rightCharge = raw40961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40961 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1543).leftCharge (GramAssembly.key 1543).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1543, Integer.Sparse.eval]

theorem keyMoment1544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1544) =
      Integer.Sparse.eval keyMomentRow1544 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1544).leftCharge (GramAssembly.key 1544).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3693) := by
    have ha : gramCharges (GramAssembly.key 1544).leftCharge (GramAssembly.key 1544).rightCharge = raw40962 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40962Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40962 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1544).leftCharge (GramAssembly.key 1544).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1544, Integer.Sparse.eval]

theorem keyMoment1545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1545) =
      Integer.Sparse.eval keyMomentRow1545 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1545).leftCharge (GramAssembly.key 1545).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1810) := by
    have ha : gramCharges (GramAssembly.key 1545).leftCharge (GramAssembly.key 1545).rightCharge = raw40963 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40963Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40963 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1545).leftCharge (GramAssembly.key 1545).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1545, Integer.Sparse.eval]

theorem keyMoment1546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1546) =
      Integer.Sparse.eval keyMomentRow1546 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1546).leftCharge (GramAssembly.key 1546).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2814) := by
    have ha : gramCharges (GramAssembly.key 1546).leftCharge (GramAssembly.key 1546).rightCharge = raw40964 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40964Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40964 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1546).leftCharge (GramAssembly.key 1546).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1546, Integer.Sparse.eval]

theorem keyMoment1547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1547) =
      Integer.Sparse.eval keyMomentRow1547 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1547).leftCharge (GramAssembly.key 1547).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3692) := by
    have ha : gramCharges (GramAssembly.key 1547).leftCharge (GramAssembly.key 1547).rightCharge = raw40965 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40965Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40965 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1547).leftCharge (GramAssembly.key 1547).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1547, Integer.Sparse.eval]

theorem keyMoment1548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1548) =
      Integer.Sparse.eval keyMomentRow1548 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1548).leftCharge (GramAssembly.key 1548).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3671) := by
    have ha : gramCharges (GramAssembly.key 1548).leftCharge (GramAssembly.key 1548).rightCharge = raw40966 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40966Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40966 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1548).leftCharge (GramAssembly.key 1548).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1548, Integer.Sparse.eval]

theorem keyMoment1549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1549) =
      Integer.Sparse.eval keyMomentRow1549 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1549).leftCharge (GramAssembly.key 1549).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3619) := by
    have ha : gramCharges (GramAssembly.key 1549).leftCharge (GramAssembly.key 1549).rightCharge = raw40967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40967 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1549).leftCharge (GramAssembly.key 1549).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1549, Integer.Sparse.eval]

theorem keyMoment1550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1550) =
      Integer.Sparse.eval keyMomentRow1550 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1550).leftCharge (GramAssembly.key 1550).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3899) := by
    have ha : gramCharges (GramAssembly.key 1550).leftCharge (GramAssembly.key 1550).rightCharge = raw40968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40968 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1550).leftCharge (GramAssembly.key 1550).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1550, Integer.Sparse.eval]

theorem keyMoment1551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1551) =
      Integer.Sparse.eval keyMomentRow1551 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1551).leftCharge (GramAssembly.key 1551).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3731) := by
    have ha : gramCharges (GramAssembly.key 1551).leftCharge (GramAssembly.key 1551).rightCharge = raw40969 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40969Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40969 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1551).leftCharge (GramAssembly.key 1551).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1551, Integer.Sparse.eval]

theorem keyMoment1552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1552) =
      Integer.Sparse.eval keyMomentRow1552 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1552).leftCharge (GramAssembly.key 1552).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1811) := by
    have ha : gramCharges (GramAssembly.key 1552).leftCharge (GramAssembly.key 1552).rightCharge = raw40970 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40970Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40970 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1552).leftCharge (GramAssembly.key 1552).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1552, Integer.Sparse.eval]

theorem keyMoment1553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1553) =
      Integer.Sparse.eval keyMomentRow1553 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1553).leftCharge (GramAssembly.key 1553).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4025) := by
    have ha : gramCharges (GramAssembly.key 1553).leftCharge (GramAssembly.key 1553).rightCharge = raw40971 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40971Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40971 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1553).leftCharge (GramAssembly.key 1553).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1553, Integer.Sparse.eval]

theorem keyMoment1554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1554) =
      Integer.Sparse.eval keyMomentRow1554 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1554).leftCharge (GramAssembly.key 1554).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1812) := by
    have ha : gramCharges (GramAssembly.key 1554).leftCharge (GramAssembly.key 1554).rightCharge = raw40972 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40972Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40972 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1554).leftCharge (GramAssembly.key 1554).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1554, Integer.Sparse.eval]

theorem keyMoment1555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1555) =
      Integer.Sparse.eval keyMomentRow1555 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1555).leftCharge (GramAssembly.key 1555).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2896) := by
    have ha : gramCharges (GramAssembly.key 1555).leftCharge (GramAssembly.key 1555).rightCharge = raw40973 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40973Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40973 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1555).leftCharge (GramAssembly.key 1555).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1555, Integer.Sparse.eval]

theorem keyMoment1556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1556) =
      Integer.Sparse.eval keyMomentRow1556 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1556).leftCharge (GramAssembly.key 1556).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3721) := by
    have ha : gramCharges (GramAssembly.key 1556).leftCharge (GramAssembly.key 1556).rightCharge = raw40974 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40974Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40974 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1556).leftCharge (GramAssembly.key 1556).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1556, Integer.Sparse.eval]

theorem keyMoment1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1557) =
      Integer.Sparse.eval keyMomentRow1557 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1557).leftCharge (GramAssembly.key 1557).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1805) := by
    have ha : gramCharges (GramAssembly.key 1557).leftCharge (GramAssembly.key 1557).rightCharge = raw40975 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40975Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40975 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1557).leftCharge (GramAssembly.key 1557).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1557, Integer.Sparse.eval]

theorem keyMoment1558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1558) =
      Integer.Sparse.eval keyMomentRow1558 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1558).leftCharge (GramAssembly.key 1558).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1143) := by
    have ha : gramCharges (GramAssembly.key 1558).leftCharge (GramAssembly.key 1558).rightCharge = raw40976 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40976Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40976 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1558).leftCharge (GramAssembly.key 1558).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1558, Integer.Sparse.eval]

theorem keyMoment1559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1559) =
      Integer.Sparse.eval keyMomentRow1559 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1559).leftCharge (GramAssembly.key 1559).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2522) := by
    have ha : gramCharges (GramAssembly.key 1559).leftCharge (GramAssembly.key 1559).rightCharge = raw40977 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40977Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40977 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1559).leftCharge (GramAssembly.key 1559).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1559, Integer.Sparse.eval]

theorem keyMoment1560 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1560) =
      Integer.Sparse.eval keyMomentRow1560 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1560).leftCharge (GramAssembly.key 1560).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1138) := by
    have ha : gramCharges (GramAssembly.key 1560).leftCharge (GramAssembly.key 1560).rightCharge = raw40978 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40978Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40978 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1560).leftCharge (GramAssembly.key 1560).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1560, Integer.Sparse.eval]

theorem keyMoment1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1561) =
      Integer.Sparse.eval keyMomentRow1561 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1561).leftCharge (GramAssembly.key 1561).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2515) := by
    have ha : gramCharges (GramAssembly.key 1561).leftCharge (GramAssembly.key 1561).rightCharge = raw40979 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40979Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40979 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1561).leftCharge (GramAssembly.key 1561).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1561, Integer.Sparse.eval]

theorem keyMoment1562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1562) =
      Integer.Sparse.eval keyMomentRow1562 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1562).leftCharge (GramAssembly.key 1562).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2488) := by
    have ha : gramCharges (GramAssembly.key 1562).leftCharge (GramAssembly.key 1562).rightCharge = raw40980 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40980Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40980 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1562).leftCharge (GramAssembly.key 1562).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1562, Integer.Sparse.eval]

theorem keyMoment1563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1563) =
      Integer.Sparse.eval keyMomentRow1563 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1563).leftCharge (GramAssembly.key 1563).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1807) := by
    have ha : gramCharges (GramAssembly.key 1563).leftCharge (GramAssembly.key 1563).rightCharge = raw40981 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40981Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40981 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1563).leftCharge (GramAssembly.key 1563).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1563, Integer.Sparse.eval]

theorem keyMoment1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1564) =
      Integer.Sparse.eval keyMomentRow1564 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1564).leftCharge (GramAssembly.key 1564).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1815) := by
    have ha : gramCharges (GramAssembly.key 1564).leftCharge (GramAssembly.key 1564).rightCharge = raw40982 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40982Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40982 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1564).leftCharge (GramAssembly.key 1564).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1564, Integer.Sparse.eval]

theorem keyMoment1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1565) =
      Integer.Sparse.eval keyMomentRow1565 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1565).leftCharge (GramAssembly.key 1565).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2483) := by
    have ha : gramCharges (GramAssembly.key 1565).leftCharge (GramAssembly.key 1565).rightCharge = raw40983 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40983Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40983 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1565).leftCharge (GramAssembly.key 1565).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1565, Integer.Sparse.eval]

theorem keyMoment1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1566) =
      Integer.Sparse.eval keyMomentRow1566 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1566).leftCharge (GramAssembly.key 1566).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2431) := by
    have ha : gramCharges (GramAssembly.key 1566).leftCharge (GramAssembly.key 1566).rightCharge = raw40984 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40984Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40984 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1566).leftCharge (GramAssembly.key 1566).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1566, Integer.Sparse.eval]

theorem keyMoment1567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1567) =
      Integer.Sparse.eval keyMomentRow1567 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1567).leftCharge (GramAssembly.key 1567).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3709) := by
    have ha : gramCharges (GramAssembly.key 1567).leftCharge (GramAssembly.key 1567).rightCharge = raw40985 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40985Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40985 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1567).leftCharge (GramAssembly.key 1567).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1567, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

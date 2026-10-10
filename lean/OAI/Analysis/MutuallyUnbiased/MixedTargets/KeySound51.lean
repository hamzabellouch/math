import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical320

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1632) =
      Integer.Sparse.eval keyMomentRow1632 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1632).leftCharge (GramAssembly.key 1632).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2846) := by
    have ha : gramCharges (GramAssembly.key 1632).leftCharge (GramAssembly.key 1632).rightCharge = raw41046 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41046Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41046 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1632).leftCharge (GramAssembly.key 1632).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1632, Integer.Sparse.eval]

theorem keyMoment1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1633) =
      Integer.Sparse.eval keyMomentRow1633 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1633).leftCharge (GramAssembly.key 1633).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2981) := by
    have ha : gramCharges (GramAssembly.key 1633).leftCharge (GramAssembly.key 1633).rightCharge = raw41047 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41047Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41047 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1633).leftCharge (GramAssembly.key 1633).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1633, Integer.Sparse.eval]

theorem keyMoment1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1634) =
      Integer.Sparse.eval keyMomentRow1634 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1634).leftCharge (GramAssembly.key 1634).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2746) := by
    have ha : gramCharges (GramAssembly.key 1634).leftCharge (GramAssembly.key 1634).rightCharge = raw41048 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41048Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41048 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1634).leftCharge (GramAssembly.key 1634).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1634, Integer.Sparse.eval]

theorem keyMoment1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1635) =
      Integer.Sparse.eval keyMomentRow1635 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1635).leftCharge (GramAssembly.key 1635).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2847) := by
    have ha : gramCharges (GramAssembly.key 1635).leftCharge (GramAssembly.key 1635).rightCharge = raw41049 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41049Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41049 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1635).leftCharge (GramAssembly.key 1635).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1635, Integer.Sparse.eval]

theorem keyMoment1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1636) =
      Integer.Sparse.eval keyMomentRow1636 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1636).leftCharge (GramAssembly.key 1636).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2495) := by
    have ha : gramCharges (GramAssembly.key 1636).leftCharge (GramAssembly.key 1636).rightCharge = raw41050 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41050Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41050 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1636).leftCharge (GramAssembly.key 1636).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1636, Integer.Sparse.eval]

theorem keyMoment1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1637) =
      Integer.Sparse.eval keyMomentRow1637 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1637).leftCharge (GramAssembly.key 1637).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1132) := by
    have ha : gramCharges (GramAssembly.key 1637).leftCharge (GramAssembly.key 1637).rightCharge = raw41051 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41051Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41051 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1637).leftCharge (GramAssembly.key 1637).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1637, Integer.Sparse.eval]

theorem keyMoment1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1638) =
      Integer.Sparse.eval keyMomentRow1638 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1638).leftCharge (GramAssembly.key 1638).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2437) := by
    have ha : gramCharges (GramAssembly.key 1638).leftCharge (GramAssembly.key 1638).rightCharge = raw41052 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41052Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41052 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1638).leftCharge (GramAssembly.key 1638).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1638, Integer.Sparse.eval]

theorem keyMoment1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1639) =
      Integer.Sparse.eval keyMomentRow1639 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1639).leftCharge (GramAssembly.key 1639).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1112) := by
    have ha : gramCharges (GramAssembly.key 1639).leftCharge (GramAssembly.key 1639).rightCharge = raw41053 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41053Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41053 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1639).leftCharge (GramAssembly.key 1639).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1639, Integer.Sparse.eval]

theorem keyMoment1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1640) =
      Integer.Sparse.eval keyMomentRow1640 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1640).leftCharge (GramAssembly.key 1640).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2426) := by
    have ha : gramCharges (GramAssembly.key 1640).leftCharge (GramAssembly.key 1640).rightCharge = raw41054 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41054Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41054 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1640).leftCharge (GramAssembly.key 1640).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1640, Integer.Sparse.eval]

theorem keyMoment1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1641) =
      Integer.Sparse.eval keyMomentRow1641 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1641).leftCharge (GramAssembly.key 1641).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2470) := by
    have ha : gramCharges (GramAssembly.key 1641).leftCharge (GramAssembly.key 1641).rightCharge = raw41055 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41055Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41055 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1641).leftCharge (GramAssembly.key 1641).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1641, Integer.Sparse.eval]

theorem keyMoment1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1642) =
      Integer.Sparse.eval keyMomentRow1642 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1642).leftCharge (GramAssembly.key 1642).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 606) := by
    have ha : gramCharges (GramAssembly.key 1642).leftCharge (GramAssembly.key 1642).rightCharge = raw41056 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41056Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41056 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1642).leftCharge (GramAssembly.key 1642).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1642, Integer.Sparse.eval]

theorem keyMoment1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1643) =
      Integer.Sparse.eval keyMomentRow1643 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1643).leftCharge (GramAssembly.key 1643).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 945) := by
    have ha : gramCharges (GramAssembly.key 1643).leftCharge (GramAssembly.key 1643).rightCharge = raw41057 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41057Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41057 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1643).leftCharge (GramAssembly.key 1643).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1643, Integer.Sparse.eval]

theorem keyMoment1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1644) =
      Integer.Sparse.eval keyMomentRow1644 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1644).leftCharge (GramAssembly.key 1644).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 581) := by
    have ha : gramCharges (GramAssembly.key 1644).leftCharge (GramAssembly.key 1644).rightCharge = raw41058 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41058Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41058 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1644).leftCharge (GramAssembly.key 1644).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1644, Integer.Sparse.eval]

theorem keyMoment1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1645) =
      Integer.Sparse.eval keyMomentRow1645 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1645).leftCharge (GramAssembly.key 1645).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1831) := by
    have ha : gramCharges (GramAssembly.key 1645).leftCharge (GramAssembly.key 1645).rightCharge = raw41059 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41059Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41059 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1645).leftCharge (GramAssembly.key 1645).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1645, Integer.Sparse.eval]

theorem keyMoment1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1646) =
      Integer.Sparse.eval keyMomentRow1646 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1646).leftCharge (GramAssembly.key 1646).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1979) := by
    have ha : gramCharges (GramAssembly.key 1646).leftCharge (GramAssembly.key 1646).rightCharge = raw41060 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41060Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41060 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1646).leftCharge (GramAssembly.key 1646).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1646, Integer.Sparse.eval]

theorem keyMoment1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1647) =
      Integer.Sparse.eval keyMomentRow1647 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1647).leftCharge (GramAssembly.key 1647).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1796) := by
    have ha : gramCharges (GramAssembly.key 1647).leftCharge (GramAssembly.key 1647).rightCharge = raw41061 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41061Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41061 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1647).leftCharge (GramAssembly.key 1647).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1647, Integer.Sparse.eval]

theorem keyMoment1648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1648) =
      Integer.Sparse.eval keyMomentRow1648 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1648).leftCharge (GramAssembly.key 1648).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2826) := by
    have ha : gramCharges (GramAssembly.key 1648).leftCharge (GramAssembly.key 1648).rightCharge = raw41062 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41062Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41062 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1648).leftCharge (GramAssembly.key 1648).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1648, Integer.Sparse.eval]

theorem keyMoment1649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1649) =
      Integer.Sparse.eval keyMomentRow1649 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1649).leftCharge (GramAssembly.key 1649).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2824) := by
    have ha : gramCharges (GramAssembly.key 1649).leftCharge (GramAssembly.key 1649).rightCharge = raw41063 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41063Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41063 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1649).leftCharge (GramAssembly.key 1649).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1649, Integer.Sparse.eval]

theorem keyMoment1650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1650) =
      Integer.Sparse.eval keyMomentRow1650 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1650).leftCharge (GramAssembly.key 1650).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2827) := by
    have ha : gramCharges (GramAssembly.key 1650).leftCharge (GramAssembly.key 1650).rightCharge = raw41064 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41064Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41064 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1650).leftCharge (GramAssembly.key 1650).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1650, Integer.Sparse.eval]

theorem keyMoment1651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1651) =
      Integer.Sparse.eval keyMomentRow1651 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1651).leftCharge (GramAssembly.key 1651).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2802) := by
    have ha : gramCharges (GramAssembly.key 1651).leftCharge (GramAssembly.key 1651).rightCharge = raw41065 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41065Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41065 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1651).leftCharge (GramAssembly.key 1651).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1651, Integer.Sparse.eval]

theorem keyMoment1652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1652) =
      Integer.Sparse.eval keyMomentRow1652 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1652).leftCharge (GramAssembly.key 1652).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2442) := by
    have ha : gramCharges (GramAssembly.key 1652).leftCharge (GramAssembly.key 1652).rightCharge = raw41066 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41066Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41066 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1652).leftCharge (GramAssembly.key 1652).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1652, Integer.Sparse.eval]

theorem keyMoment1653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1653) =
      Integer.Sparse.eval keyMomentRow1653 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1653).leftCharge (GramAssembly.key 1653).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1120) := by
    have ha : gramCharges (GramAssembly.key 1653).leftCharge (GramAssembly.key 1653).rightCharge = raw41067 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41067Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41067 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1653).leftCharge (GramAssembly.key 1653).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1653, Integer.Sparse.eval]

theorem keyMoment1654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1654) =
      Integer.Sparse.eval keyMomentRow1654 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1654).leftCharge (GramAssembly.key 1654).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 953) := by
    have ha : gramCharges (GramAssembly.key 1654).leftCharge (GramAssembly.key 1654).rightCharge = raw41068 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41068Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41068 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1654).leftCharge (GramAssembly.key 1654).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1654, Integer.Sparse.eval]

theorem keyMoment1655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1655) =
      Integer.Sparse.eval keyMomentRow1655 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1655).leftCharge (GramAssembly.key 1655).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 589) := by
    have ha : gramCharges (GramAssembly.key 1655).leftCharge (GramAssembly.key 1655).rightCharge = raw41069 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41069Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41069 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1655).leftCharge (GramAssembly.key 1655).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1655, Integer.Sparse.eval]

theorem keyMoment1656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1656) =
      Integer.Sparse.eval keyMomentRow1656 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1656).leftCharge (GramAssembly.key 1656).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2281) := by
    have ha : gramCharges (GramAssembly.key 1656).leftCharge (GramAssembly.key 1656).rightCharge = raw41070 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41070Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41070 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1656).leftCharge (GramAssembly.key 1656).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1656, Integer.Sparse.eval]

theorem keyMoment1657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1657) =
      Integer.Sparse.eval keyMomentRow1657 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1657).leftCharge (GramAssembly.key 1657).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2112) := by
    have ha : gramCharges (GramAssembly.key 1657).leftCharge (GramAssembly.key 1657).rightCharge = raw41071 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41071Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41071 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1657).leftCharge (GramAssembly.key 1657).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1657, Integer.Sparse.eval]

theorem keyMoment1658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1658) =
      Integer.Sparse.eval keyMomentRow1658 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1658).leftCharge (GramAssembly.key 1658).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1819) := by
    have ha : gramCharges (GramAssembly.key 1658).leftCharge (GramAssembly.key 1658).rightCharge = raw41072 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41072Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41072 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1658).leftCharge (GramAssembly.key 1658).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1658, Integer.Sparse.eval]

theorem keyMoment1659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1659) =
      Integer.Sparse.eval keyMomentRow1659 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1659).leftCharge (GramAssembly.key 1659).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2062) := by
    have ha : gramCharges (GramAssembly.key 1659).leftCharge (GramAssembly.key 1659).rightCharge = raw41073 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41073Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41073 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1659).leftCharge (GramAssembly.key 1659).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1659, Integer.Sparse.eval]

theorem keyMoment1660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1660) =
      Integer.Sparse.eval keyMomentRow1660 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1660).leftCharge (GramAssembly.key 1660).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2247) := by
    have ha : gramCharges (GramAssembly.key 1660).leftCharge (GramAssembly.key 1660).rightCharge = raw41074 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41074Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41074 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1660).leftCharge (GramAssembly.key 1660).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1660, Integer.Sparse.eval]

theorem keyMoment1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1661) =
      Integer.Sparse.eval keyMomentRow1661 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1661).leftCharge (GramAssembly.key 1661).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1812) := by
    have ha : gramCharges (GramAssembly.key 1661).leftCharge (GramAssembly.key 1661).rightCharge = raw41075 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41075Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41075 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1661).leftCharge (GramAssembly.key 1661).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1661, Integer.Sparse.eval]

theorem keyMoment1662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1662) =
      Integer.Sparse.eval keyMomentRow1662 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1662).leftCharge (GramAssembly.key 1662).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2025) := by
    have ha : gramCharges (GramAssembly.key 1662).leftCharge (GramAssembly.key 1662).rightCharge = raw41076 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41076Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41076 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1662).leftCharge (GramAssembly.key 1662).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1662, Integer.Sparse.eval]

theorem keyMoment1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1663) =
      Integer.Sparse.eval keyMomentRow1663 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1663).leftCharge (GramAssembly.key 1663).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1970) := by
    have ha : gramCharges (GramAssembly.key 1663).leftCharge (GramAssembly.key 1663).rightCharge = raw41077 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41077Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41077 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1663).leftCharge (GramAssembly.key 1663).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1663, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical321

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1696) =
      Integer.Sparse.eval keyMomentRow1696 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1696).leftCharge (GramAssembly.key 1696).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2339) := by
    have ha : gramCharges (GramAssembly.key 1696).leftCharge (GramAssembly.key 1696).rightCharge = raw41109 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41109Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41109 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1696).leftCharge (GramAssembly.key 1696).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1696, Integer.Sparse.eval]

theorem keyMoment1697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1697) =
      Integer.Sparse.eval keyMomentRow1697 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1697).leftCharge (GramAssembly.key 1697).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1310) := by
    have ha : gramCharges (GramAssembly.key 1697).leftCharge (GramAssembly.key 1697).rightCharge = raw41110 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41110Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41110 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1697).leftCharge (GramAssembly.key 1697).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1697, Integer.Sparse.eval]

theorem keyMoment1698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1698) =
      Integer.Sparse.eval keyMomentRow1698 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1698).leftCharge (GramAssembly.key 1698).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1245) := by
    have ha : gramCharges (GramAssembly.key 1698).leftCharge (GramAssembly.key 1698).rightCharge = raw41111 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41111Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41111 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1698).leftCharge (GramAssembly.key 1698).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1698, Integer.Sparse.eval]

theorem keyMoment1699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1699) =
      Integer.Sparse.eval keyMomentRow1699 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1699).leftCharge (GramAssembly.key 1699).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1306) := by
    have ha : gramCharges (GramAssembly.key 1699).leftCharge (GramAssembly.key 1699).rightCharge = raw41112 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41112Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41112 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1699).leftCharge (GramAssembly.key 1699).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1699, Integer.Sparse.eval]

theorem keyMoment1700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1700) =
      Integer.Sparse.eval keyMomentRow1700 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1700).leftCharge (GramAssembly.key 1700).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1291) := by
    have ha : gramCharges (GramAssembly.key 1700).leftCharge (GramAssembly.key 1700).rightCharge = raw41113 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41113Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41113 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1700).leftCharge (GramAssembly.key 1700).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1700, Integer.Sparse.eval]

theorem keyMoment1701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1701) =
      Integer.Sparse.eval keyMomentRow1701 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1701).leftCharge (GramAssembly.key 1701).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1241) := by
    have ha : gramCharges (GramAssembly.key 1701).leftCharge (GramAssembly.key 1701).rightCharge = raw41114 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41114Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41114 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1701).leftCharge (GramAssembly.key 1701).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1701, Integer.Sparse.eval]

theorem keyMoment1702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1702) =
      Integer.Sparse.eval keyMomentRow1702 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1702).leftCharge (GramAssembly.key 1702).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1233) := by
    have ha : gramCharges (GramAssembly.key 1702).leftCharge (GramAssembly.key 1702).rightCharge = raw41115 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41115Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41115 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1702).leftCharge (GramAssembly.key 1702).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1702, Integer.Sparse.eval]

theorem keyMoment1703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1703) =
      Integer.Sparse.eval keyMomentRow1703 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1703).leftCharge (GramAssembly.key 1703).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1295) := by
    have ha : gramCharges (GramAssembly.key 1703).leftCharge (GramAssembly.key 1703).rightCharge = raw41116 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41116Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41116 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1703).leftCharge (GramAssembly.key 1703).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1703, Integer.Sparse.eval]

theorem keyMoment1704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1704) =
      Integer.Sparse.eval keyMomentRow1704 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1704).leftCharge (GramAssembly.key 1704).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1243) := by
    have ha : gramCharges (GramAssembly.key 1704).leftCharge (GramAssembly.key 1704).rightCharge = raw41117 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41117Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41117 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1704).leftCharge (GramAssembly.key 1704).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1704, Integer.Sparse.eval]

theorem keyMoment1705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1705) =
      Integer.Sparse.eval keyMomentRow1705 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1705).leftCharge (GramAssembly.key 1705).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1237) := by
    have ha : gramCharges (GramAssembly.key 1705).leftCharge (GramAssembly.key 1705).rightCharge = raw41118 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41118Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41118 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1705).leftCharge (GramAssembly.key 1705).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1705, Integer.Sparse.eval]

theorem keyMoment1706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1706) =
      Integer.Sparse.eval keyMomentRow1706 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1706).leftCharge (GramAssembly.key 1706).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1273) := by
    have ha : gramCharges (GramAssembly.key 1706).leftCharge (GramAssembly.key 1706).rightCharge = raw41119 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41119Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41119 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1706).leftCharge (GramAssembly.key 1706).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1706, Integer.Sparse.eval]

theorem keyMoment1707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1707) =
      Integer.Sparse.eval keyMomentRow1707 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1707).leftCharge (GramAssembly.key 1707).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1261) := by
    have ha : gramCharges (GramAssembly.key 1707).leftCharge (GramAssembly.key 1707).rightCharge = raw41120 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41120Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41120 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1707).leftCharge (GramAssembly.key 1707).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1707, Integer.Sparse.eval]

theorem keyMoment1708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1708) =
      Integer.Sparse.eval keyMomentRow1708 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1708).leftCharge (GramAssembly.key 1708).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1219) := by
    have ha : gramCharges (GramAssembly.key 1708).leftCharge (GramAssembly.key 1708).rightCharge = raw41121 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41121Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41121 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1708).leftCharge (GramAssembly.key 1708).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1708, Integer.Sparse.eval]

theorem keyMoment1709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1709) =
      Integer.Sparse.eval keyMomentRow1709 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1709).leftCharge (GramAssembly.key 1709).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1212) := by
    have ha : gramCharges (GramAssembly.key 1709).leftCharge (GramAssembly.key 1709).rightCharge = raw41122 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41122Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41122 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1709).leftCharge (GramAssembly.key 1709).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1709, Integer.Sparse.eval]

theorem keyMoment1710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1710) =
      Integer.Sparse.eval keyMomentRow1710 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1710).leftCharge (GramAssembly.key 1710).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1270) := by
    have ha : gramCharges (GramAssembly.key 1710).leftCharge (GramAssembly.key 1710).rightCharge = raw41123 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41123Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41123 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1710).leftCharge (GramAssembly.key 1710).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1710, Integer.Sparse.eval]

theorem keyMoment1711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1711) =
      Integer.Sparse.eval keyMomentRow1711 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1711).leftCharge (GramAssembly.key 1711).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1217) := by
    have ha : gramCharges (GramAssembly.key 1711).leftCharge (GramAssembly.key 1711).rightCharge = raw41124 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41124Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41124 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1711).leftCharge (GramAssembly.key 1711).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1711, Integer.Sparse.eval]

theorem keyMoment1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1712) =
      Integer.Sparse.eval keyMomentRow1712 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1712).leftCharge (GramAssembly.key 1712).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1264) := by
    have ha : gramCharges (GramAssembly.key 1712).leftCharge (GramAssembly.key 1712).rightCharge = raw41125 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41125Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41125 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1712).leftCharge (GramAssembly.key 1712).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1712, Integer.Sparse.eval]

theorem keyMoment1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1713) =
      Integer.Sparse.eval keyMomentRow1713 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1713).leftCharge (GramAssembly.key 1713).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1221) := by
    have ha : gramCharges (GramAssembly.key 1713).leftCharge (GramAssembly.key 1713).rightCharge = raw41126 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41126Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41126 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1713).leftCharge (GramAssembly.key 1713).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1713, Integer.Sparse.eval]

theorem keyMoment1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1714) =
      Integer.Sparse.eval keyMomentRow1714 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1714).leftCharge (GramAssembly.key 1714).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1215) := by
    have ha : gramCharges (GramAssembly.key 1714).leftCharge (GramAssembly.key 1714).rightCharge = raw41127 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41127Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41127 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1714).leftCharge (GramAssembly.key 1714).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1714, Integer.Sparse.eval]

theorem keyMoment1715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1715) =
      Integer.Sparse.eval keyMomentRow1715 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1715).leftCharge (GramAssembly.key 1715).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1174) := by
    have ha : gramCharges (GramAssembly.key 1715).leftCharge (GramAssembly.key 1715).rightCharge = raw41128 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41128Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41128 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1715).leftCharge (GramAssembly.key 1715).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1715, Integer.Sparse.eval]

theorem keyMoment1716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1716) =
      Integer.Sparse.eval keyMomentRow1716 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1716).leftCharge (GramAssembly.key 1716).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1153) := by
    have ha : gramCharges (GramAssembly.key 1716).leftCharge (GramAssembly.key 1716).rightCharge = raw41129 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41129Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41129 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1716).leftCharge (GramAssembly.key 1716).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1716, Integer.Sparse.eval]

theorem keyMoment1717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1717) =
      Integer.Sparse.eval keyMomentRow1717 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1717).leftCharge (GramAssembly.key 1717).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1171) := by
    have ha : gramCharges (GramAssembly.key 1717).leftCharge (GramAssembly.key 1717).rightCharge = raw41130 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41130Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41130 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1717).leftCharge (GramAssembly.key 1717).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1717, Integer.Sparse.eval]

theorem keyMoment1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1718) =
      Integer.Sparse.eval keyMomentRow1718 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1718).leftCharge (GramAssembly.key 1718).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1156) := by
    have ha : gramCharges (GramAssembly.key 1718).leftCharge (GramAssembly.key 1718).rightCharge = raw41131 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41131Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41131 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1718).leftCharge (GramAssembly.key 1718).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1718, Integer.Sparse.eval]

theorem keyMoment1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1719) =
      Integer.Sparse.eval keyMomentRow1719 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1719).leftCharge (GramAssembly.key 1719).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1151) := by
    have ha : gramCharges (GramAssembly.key 1719).leftCharge (GramAssembly.key 1719).rightCharge = raw41132 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41132Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41132 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1719).leftCharge (GramAssembly.key 1719).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1719, Integer.Sparse.eval]

theorem keyMoment1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1720) =
      Integer.Sparse.eval keyMomentRow1720 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1720).leftCharge (GramAssembly.key 1720).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1160) := by
    have ha : gramCharges (GramAssembly.key 1720).leftCharge (GramAssembly.key 1720).rightCharge = raw41133 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41133Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41133 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1720).leftCharge (GramAssembly.key 1720).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1720, Integer.Sparse.eval]

theorem keyMoment1721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1721) =
      Integer.Sparse.eval keyMomentRow1721 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1721).leftCharge (GramAssembly.key 1721).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1155) := by
    have ha : gramCharges (GramAssembly.key 1721).leftCharge (GramAssembly.key 1721).rightCharge = raw41134 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41134Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41134 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1721).leftCharge (GramAssembly.key 1721).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1721, Integer.Sparse.eval]

theorem keyMoment1722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1722) =
      Integer.Sparse.eval keyMomentRow1722 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1722).leftCharge (GramAssembly.key 1722).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1149) := by
    have ha : gramCharges (GramAssembly.key 1722).leftCharge (GramAssembly.key 1722).rightCharge = raw41135 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41135Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41135 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1722).leftCharge (GramAssembly.key 1722).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1722, Integer.Sparse.eval]

theorem keyMoment1723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1723) =
      Integer.Sparse.eval keyMomentRow1723 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1723).leftCharge (GramAssembly.key 1723).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1169) := by
    have ha : gramCharges (GramAssembly.key 1723).leftCharge (GramAssembly.key 1723).rightCharge = raw41136 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41136Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41136 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1723).leftCharge (GramAssembly.key 1723).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1723, Integer.Sparse.eval]

theorem keyMoment1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1724) =
      Integer.Sparse.eval keyMomentRow1724 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1724).leftCharge (GramAssembly.key 1724).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1150) := by
    have ha : gramCharges (GramAssembly.key 1724).leftCharge (GramAssembly.key 1724).rightCharge = raw41137 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41137Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41137 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1724).leftCharge (GramAssembly.key 1724).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1724, Integer.Sparse.eval]

theorem keyMoment1725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1725) =
      Integer.Sparse.eval keyMomentRow1725 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1725).leftCharge (GramAssembly.key 1725).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1159) := by
    have ha : gramCharges (GramAssembly.key 1725).leftCharge (GramAssembly.key 1725).rightCharge = raw41138 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41138Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41138 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1725).leftCharge (GramAssembly.key 1725).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1725, Integer.Sparse.eval]

theorem keyMoment1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1726) =
      Integer.Sparse.eval keyMomentRow1726 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1726).leftCharge (GramAssembly.key 1726).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1115) := by
    have ha : gramCharges (GramAssembly.key 1726).leftCharge (GramAssembly.key 1726).rightCharge = raw41139 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41139Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41139 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1726).leftCharge (GramAssembly.key 1726).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1726, Integer.Sparse.eval]

theorem keyMoment1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1727) =
      Integer.Sparse.eval keyMomentRow1727 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1727).leftCharge (GramAssembly.key 1727).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1148) := by
    have ha : gramCharges (GramAssembly.key 1727).leftCharge (GramAssembly.key 1727).rightCharge = raw41140 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41140Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41140 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1727).leftCharge (GramAssembly.key 1727).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1727, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

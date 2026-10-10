import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical321

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1728) =
      Integer.Sparse.eval keyMomentRow1728 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1728).leftCharge (GramAssembly.key 1728).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 584) := by
    have ha : gramCharges (GramAssembly.key 1728).leftCharge (GramAssembly.key 1728).rightCharge = raw41141 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41141Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41141 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1728).leftCharge (GramAssembly.key 1728).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1728, Integer.Sparse.eval]

theorem keyMoment1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1729) =
      Integer.Sparse.eval keyMomentRow1729 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1729).leftCharge (GramAssembly.key 1729).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1297) := by
    have ha : gramCharges (GramAssembly.key 1729).leftCharge (GramAssembly.key 1729).rightCharge = raw41142 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41142Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41142 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1729).leftCharge (GramAssembly.key 1729).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1729, Integer.Sparse.eval]

theorem keyMoment1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1730) =
      Integer.Sparse.eval keyMomentRow1730 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1730).leftCharge (GramAssembly.key 1730).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1143) := by
    have ha : gramCharges (GramAssembly.key 1730).leftCharge (GramAssembly.key 1730).rightCharge = raw41143 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41143Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41143 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1730).leftCharge (GramAssembly.key 1730).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1730, Integer.Sparse.eval]

theorem keyMoment1731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1731) =
      Integer.Sparse.eval keyMomentRow1731 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1731).leftCharge (GramAssembly.key 1731).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1239) := by
    have ha : gramCharges (GramAssembly.key 1731).leftCharge (GramAssembly.key 1731).rightCharge = raw41144 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41144Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41144 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1731).leftCharge (GramAssembly.key 1731).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1731, Integer.Sparse.eval]

theorem keyMoment1732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1732) =
      Integer.Sparse.eval keyMomentRow1732 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1732).leftCharge (GramAssembly.key 1732).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1128) := by
    have ha : gramCharges (GramAssembly.key 1732).leftCharge (GramAssembly.key 1732).rightCharge = raw41145 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41145Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41145 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1732).leftCharge (GramAssembly.key 1732).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1732, Integer.Sparse.eval]

theorem keyMoment1733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1733) =
      Integer.Sparse.eval keyMomentRow1733 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1733).leftCharge (GramAssembly.key 1733).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1294) := by
    have ha : gramCharges (GramAssembly.key 1733).leftCharge (GramAssembly.key 1733).rightCharge = raw41146 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41146Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41146 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1733).leftCharge (GramAssembly.key 1733).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1733, Integer.Sparse.eval]

theorem keyMoment1734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1734) =
      Integer.Sparse.eval keyMomentRow1734 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1734).leftCharge (GramAssembly.key 1734).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1138) := by
    have ha : gramCharges (GramAssembly.key 1734).leftCharge (GramAssembly.key 1734).rightCharge = raw41147 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41147Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41147 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1734).leftCharge (GramAssembly.key 1734).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1734, Integer.Sparse.eval]

theorem keyMoment1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1735) =
      Integer.Sparse.eval keyMomentRow1735 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1735).leftCharge (GramAssembly.key 1735).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1236) := by
    have ha : gramCharges (GramAssembly.key 1735).leftCharge (GramAssembly.key 1735).rightCharge = raw41148 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41148Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41148 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1735).leftCharge (GramAssembly.key 1735).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1735, Integer.Sparse.eval]

theorem keyMoment1736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1736) =
      Integer.Sparse.eval keyMomentRow1736 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1736).leftCharge (GramAssembly.key 1736).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1126) := by
    have ha : gramCharges (GramAssembly.key 1736).leftCharge (GramAssembly.key 1736).rightCharge = raw41149 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41149Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41149 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1736).leftCharge (GramAssembly.key 1736).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1736, Integer.Sparse.eval]

theorem keyMoment1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1737) =
      Integer.Sparse.eval keyMomentRow1737 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1737).leftCharge (GramAssembly.key 1737).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1145) := by
    have ha : gramCharges (GramAssembly.key 1737).leftCharge (GramAssembly.key 1737).rightCharge = raw41150 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41150Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41150 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1737).leftCharge (GramAssembly.key 1737).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1737, Integer.Sparse.eval]

theorem keyMoment1738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1738) =
      Integer.Sparse.eval keyMomentRow1738 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1738).leftCharge (GramAssembly.key 1738).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1246) := by
    have ha : gramCharges (GramAssembly.key 1738).leftCharge (GramAssembly.key 1738).rightCharge = raw41151 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41151Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41151 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1738).leftCharge (GramAssembly.key 1738).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1738, Integer.Sparse.eval]

theorem keyMoment1739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1739) =
      Integer.Sparse.eval keyMomentRow1739 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1739).leftCharge (GramAssembly.key 1739).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1134) := by
    have ha : gramCharges (GramAssembly.key 1739).leftCharge (GramAssembly.key 1739).rightCharge = raw41152 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41152Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41152 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1739).leftCharge (GramAssembly.key 1739).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1739, Integer.Sparse.eval]

theorem keyMoment1740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1740) =
      Integer.Sparse.eval keyMomentRow1740 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1740).leftCharge (GramAssembly.key 1740).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1293) := by
    have ha : gramCharges (GramAssembly.key 1740).leftCharge (GramAssembly.key 1740).rightCharge = raw41153 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41153Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41153 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1740).leftCharge (GramAssembly.key 1740).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1740, Integer.Sparse.eval]

theorem keyMoment1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1741) =
      Integer.Sparse.eval keyMomentRow1741 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1741).leftCharge (GramAssembly.key 1741).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1135) := by
    have ha : gramCharges (GramAssembly.key 1741).leftCharge (GramAssembly.key 1741).rightCharge = raw41154 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41154Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41154 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1741).leftCharge (GramAssembly.key 1741).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1741, Integer.Sparse.eval]

theorem keyMoment1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1742) =
      Integer.Sparse.eval keyMomentRow1742 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1742).leftCharge (GramAssembly.key 1742).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1235) := by
    have ha : gramCharges (GramAssembly.key 1742).leftCharge (GramAssembly.key 1742).rightCharge = raw41155 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41155Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41155 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1742).leftCharge (GramAssembly.key 1742).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1742, Integer.Sparse.eval]

theorem keyMoment1743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1743) =
      Integer.Sparse.eval keyMomentRow1743 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1743).leftCharge (GramAssembly.key 1743).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1240) := by
    have ha : gramCharges (GramAssembly.key 1743).leftCharge (GramAssembly.key 1743).rightCharge = raw41156 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41156Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41156 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1743).leftCharge (GramAssembly.key 1743).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1743, Integer.Sparse.eval]

theorem keyMoment1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1744) =
      Integer.Sparse.eval keyMomentRow1744 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1744).leftCharge (GramAssembly.key 1744).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1129) := by
    have ha : gramCharges (GramAssembly.key 1744).leftCharge (GramAssembly.key 1744).rightCharge = raw41157 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41157Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41157 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1744).leftCharge (GramAssembly.key 1744).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1744, Integer.Sparse.eval]

theorem keyMoment1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1745) =
      Integer.Sparse.eval keyMomentRow1745 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1745).leftCharge (GramAssembly.key 1745).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1140) := by
    have ha : gramCharges (GramAssembly.key 1745).leftCharge (GramAssembly.key 1745).rightCharge = raw41158 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41158Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41158 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1745).leftCharge (GramAssembly.key 1745).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1745, Integer.Sparse.eval]

theorem keyMoment1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1746) =
      Integer.Sparse.eval keyMomentRow1746 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1746).leftCharge (GramAssembly.key 1746).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1242) := by
    have ha : gramCharges (GramAssembly.key 1746).leftCharge (GramAssembly.key 1746).rightCharge = raw41159 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41159Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41159 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1746).leftCharge (GramAssembly.key 1746).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1746, Integer.Sparse.eval]

theorem keyMoment1747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1747) =
      Integer.Sparse.eval keyMomentRow1747 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1747).leftCharge (GramAssembly.key 1747).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1131) := by
    have ha : gramCharges (GramAssembly.key 1747).leftCharge (GramAssembly.key 1747).rightCharge = raw41160 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41160Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41160 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1747).leftCharge (GramAssembly.key 1747).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1747, Integer.Sparse.eval]

theorem keyMoment1748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1748) =
      Integer.Sparse.eval keyMomentRow1748 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1748).leftCharge (GramAssembly.key 1748).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1139) := by
    have ha : gramCharges (GramAssembly.key 1748).leftCharge (GramAssembly.key 1748).rightCharge = raw41161 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41161Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41161 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1748).leftCharge (GramAssembly.key 1748).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1748, Integer.Sparse.eval]

theorem keyMoment1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1749) =
      Integer.Sparse.eval keyMomentRow1749 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1749).leftCharge (GramAssembly.key 1749).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 615) := by
    have ha : gramCharges (GramAssembly.key 1749).leftCharge (GramAssembly.key 1749).rightCharge = raw41162 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41162Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41162 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1749).leftCharge (GramAssembly.key 1749).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1749, Integer.Sparse.eval]

theorem keyMoment1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1750) =
      Integer.Sparse.eval keyMomentRow1750 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1750).leftCharge (GramAssembly.key 1750).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1051) := by
    have ha : gramCharges (GramAssembly.key 1750).leftCharge (GramAssembly.key 1750).rightCharge = raw41163 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41163Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41163 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1750).leftCharge (GramAssembly.key 1750).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1750, Integer.Sparse.eval]

theorem keyMoment1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1751) =
      Integer.Sparse.eval keyMomentRow1751 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1751).leftCharge (GramAssembly.key 1751).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 934) := by
    have ha : gramCharges (GramAssembly.key 1751).leftCharge (GramAssembly.key 1751).rightCharge = raw41164 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41164Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41164 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1751).leftCharge (GramAssembly.key 1751).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1751, Integer.Sparse.eval]

theorem keyMoment1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1752) =
      Integer.Sparse.eval keyMomentRow1752 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1752).leftCharge (GramAssembly.key 1752).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1144) := by
    have ha : gramCharges (GramAssembly.key 1752).leftCharge (GramAssembly.key 1752).rightCharge = raw41165 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41165Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41165 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1752).leftCharge (GramAssembly.key 1752).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1752, Integer.Sparse.eval]

theorem keyMoment1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1753) =
      Integer.Sparse.eval keyMomentRow1753 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1753).leftCharge (GramAssembly.key 1753).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 618) := by
    have ha : gramCharges (GramAssembly.key 1753).leftCharge (GramAssembly.key 1753).rightCharge = raw41166 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41166Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41166 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1753).leftCharge (GramAssembly.key 1753).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1753, Integer.Sparse.eval]

theorem keyMoment1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1754) =
      Integer.Sparse.eval keyMomentRow1754 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1754).leftCharge (GramAssembly.key 1754).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 613) := by
    have ha : gramCharges (GramAssembly.key 1754).leftCharge (GramAssembly.key 1754).rightCharge = raw41167 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41167Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41167 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1754).leftCharge (GramAssembly.key 1754).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1754, Integer.Sparse.eval]

theorem keyMoment1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1755) =
      Integer.Sparse.eval keyMomentRow1755 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1755).leftCharge (GramAssembly.key 1755).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 600) := by
    have ha : gramCharges (GramAssembly.key 1755).leftCharge (GramAssembly.key 1755).rightCharge = raw41168 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41168Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41168 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1755).leftCharge (GramAssembly.key 1755).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1755, Integer.Sparse.eval]

theorem keyMoment1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1756) =
      Integer.Sparse.eval keyMomentRow1756 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1756).leftCharge (GramAssembly.key 1756).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 620) := by
    have ha : gramCharges (GramAssembly.key 1756).leftCharge (GramAssembly.key 1756).rightCharge = raw41169 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41169Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41169 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1756).leftCharge (GramAssembly.key 1756).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1756, Integer.Sparse.eval]

theorem keyMoment1757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1757) =
      Integer.Sparse.eval keyMomentRow1757 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1757).leftCharge (GramAssembly.key 1757).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 608) := by
    have ha : gramCharges (GramAssembly.key 1757).leftCharge (GramAssembly.key 1757).rightCharge = raw41170 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41170Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41170 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1757).leftCharge (GramAssembly.key 1757).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1757, Integer.Sparse.eval]

theorem keyMoment1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1758) =
      Integer.Sparse.eval keyMomentRow1758 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1758).leftCharge (GramAssembly.key 1758).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 610) := by
    have ha : gramCharges (GramAssembly.key 1758).leftCharge (GramAssembly.key 1758).rightCharge = raw41171 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41171Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41171 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1758).leftCharge (GramAssembly.key 1758).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1758, Integer.Sparse.eval]

theorem keyMoment1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1759) =
      Integer.Sparse.eval keyMomentRow1759 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1759).leftCharge (GramAssembly.key 1759).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 599) := by
    have ha : gramCharges (GramAssembly.key 1759).leftCharge (GramAssembly.key 1759).rightCharge = raw41172 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41172Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41172 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1759).leftCharge (GramAssembly.key 1759).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1759, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

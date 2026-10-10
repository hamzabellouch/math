import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical247
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical320

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1600) =
      Integer.Sparse.eval keyMomentRow1600 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1600).leftCharge (GramAssembly.key 1600).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 1600).leftCharge (GramAssembly.key 1600).rightCharge = raw41015 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41015Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41015 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1600).leftCharge (GramAssembly.key 1600).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1600, Integer.Sparse.eval]

theorem keyMoment1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1601) =
      Integer.Sparse.eval keyMomentRow1601 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1601).leftCharge (GramAssembly.key 1601).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 1601).leftCharge (GramAssembly.key 1601).rightCharge = raw41016 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41016Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41016 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1601).leftCharge (GramAssembly.key 1601).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1601, Integer.Sparse.eval]

theorem keyMoment1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1602) =
      Integer.Sparse.eval keyMomentRow1602 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1602).leftCharge (GramAssembly.key 1602).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2942) := by
    have ha : gramCharges (GramAssembly.key 1602).leftCharge (GramAssembly.key 1602).rightCharge = raw41017 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41017Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41017 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1602).leftCharge (GramAssembly.key 1602).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1602, Integer.Sparse.eval]

theorem keyMoment1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1603) =
      Integer.Sparse.eval keyMomentRow1603 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1603).leftCharge (GramAssembly.key 1603).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 1603).leftCharge (GramAssembly.key 1603).rightCharge = raw41018 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41018Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41018 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1603).leftCharge (GramAssembly.key 1603).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1603, Integer.Sparse.eval]

theorem keyMoment1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1604) =
      Integer.Sparse.eval keyMomentRow1604 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1604).leftCharge (GramAssembly.key 1604).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 1604).leftCharge (GramAssembly.key 1604).rightCharge = raw41019 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41019Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41019 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1604).leftCharge (GramAssembly.key 1604).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1604, Integer.Sparse.eval]

theorem keyMoment1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1605) =
      Integer.Sparse.eval keyMomentRow1605 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1605).leftCharge (GramAssembly.key 1605).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2867) := by
    have ha : gramCharges (GramAssembly.key 1605).leftCharge (GramAssembly.key 1605).rightCharge = raw41020 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41020Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41020 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1605).leftCharge (GramAssembly.key 1605).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1605, Integer.Sparse.eval]

theorem keyMoment1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1606) =
      Integer.Sparse.eval keyMomentRow1606 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1606).leftCharge (GramAssembly.key 1606).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2933) := by
    have ha : gramCharges (GramAssembly.key 1606).leftCharge (GramAssembly.key 1606).rightCharge = raw41021 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41021Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41021 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1606).leftCharge (GramAssembly.key 1606).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1606, Integer.Sparse.eval]

theorem keyMoment1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1607) =
      Integer.Sparse.eval keyMomentRow1607 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1607).leftCharge (GramAssembly.key 1607).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2916) := by
    have ha : gramCharges (GramAssembly.key 1607).leftCharge (GramAssembly.key 1607).rightCharge = raw41022 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41022Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41022 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1607).leftCharge (GramAssembly.key 1607).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1607, Integer.Sparse.eval]

theorem keyMoment1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1608) =
      Integer.Sparse.eval keyMomentRow1608 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1608).leftCharge (GramAssembly.key 1608).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2861) := by
    have ha : gramCharges (GramAssembly.key 1608).leftCharge (GramAssembly.key 1608).rightCharge = raw41023 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41023Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41023 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1608).leftCharge (GramAssembly.key 1608).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1608, Integer.Sparse.eval]

theorem keyMoment1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1609) =
      Integer.Sparse.eval keyMomentRow1609 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1609).leftCharge (GramAssembly.key 1609).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 1609).leftCharge (GramAssembly.key 1609).rightCharge = raw41024 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41024Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41024 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1609).leftCharge (GramAssembly.key 1609).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1609, Integer.Sparse.eval]

theorem keyMoment1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1610) =
      Integer.Sparse.eval keyMomentRow1610 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1610).leftCharge (GramAssembly.key 1610).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 1610).leftCharge (GramAssembly.key 1610).rightCharge = raw41025 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41025Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41025 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1610).leftCharge (GramAssembly.key 1610).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1610, Integer.Sparse.eval]

theorem keyMoment1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1611) =
      Integer.Sparse.eval keyMomentRow1611 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1611).leftCharge (GramAssembly.key 1611).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2865) := by
    have ha : gramCharges (GramAssembly.key 1611).leftCharge (GramAssembly.key 1611).rightCharge = raw41026 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41026Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41026 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1611).leftCharge (GramAssembly.key 1611).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1611, Integer.Sparse.eval]

theorem keyMoment1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1612) =
      Integer.Sparse.eval keyMomentRow1612 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1612).leftCharge (GramAssembly.key 1612).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 1612).leftCharge (GramAssembly.key 1612).rightCharge = raw31649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw31649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical31649 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1612).leftCharge (GramAssembly.key 1612).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1612, Integer.Sparse.eval]

theorem keyMoment1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1613) =
      Integer.Sparse.eval keyMomentRow1613 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1613).leftCharge (GramAssembly.key 1613).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1243) := by
    have ha : gramCharges (GramAssembly.key 1613).leftCharge (GramAssembly.key 1613).rightCharge = raw41027 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41027Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41027 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1613).leftCharge (GramAssembly.key 1613).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1613, Integer.Sparse.eval]

theorem keyMoment1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1614) =
      Integer.Sparse.eval keyMomentRow1614 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1614).leftCharge (GramAssembly.key 1614).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2618) := by
    have ha : gramCharges (GramAssembly.key 1614).leftCharge (GramAssembly.key 1614).rightCharge = raw41028 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41028Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41028 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1614).leftCharge (GramAssembly.key 1614).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1614, Integer.Sparse.eval]

theorem keyMoment1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1615) =
      Integer.Sparse.eval keyMomentRow1615 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1615).leftCharge (GramAssembly.key 1615).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1217) := by
    have ha : gramCharges (GramAssembly.key 1615).leftCharge (GramAssembly.key 1615).rightCharge = raw41029 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41029Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41029 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1615).leftCharge (GramAssembly.key 1615).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1615, Integer.Sparse.eval]

theorem keyMoment1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1616) =
      Integer.Sparse.eval keyMomentRow1616 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1616).leftCharge (GramAssembly.key 1616).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2558) := by
    have ha : gramCharges (GramAssembly.key 1616).leftCharge (GramAssembly.key 1616).rightCharge = raw41030 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41030Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41030 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1616).leftCharge (GramAssembly.key 1616).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1616, Integer.Sparse.eval]

theorem keyMoment1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1617) =
      Integer.Sparse.eval keyMomentRow1617 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1617).leftCharge (GramAssembly.key 1617).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2712) := by
    have ha : gramCharges (GramAssembly.key 1617).leftCharge (GramAssembly.key 1617).rightCharge = raw41031 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41031Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41031 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1617).leftCharge (GramAssembly.key 1617).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1617, Integer.Sparse.eval]

theorem keyMoment1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1618) =
      Integer.Sparse.eval keyMomentRow1618 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1618).leftCharge (GramAssembly.key 1618).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2134) := by
    have ha : gramCharges (GramAssembly.key 1618).leftCharge (GramAssembly.key 1618).rightCharge = raw41032 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41032Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41032 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1618).leftCharge (GramAssembly.key 1618).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1618, Integer.Sparse.eval]

theorem keyMoment1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1619) =
      Integer.Sparse.eval keyMomentRow1619 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1619).leftCharge (GramAssembly.key 1619).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1825) := by
    have ha : gramCharges (GramAssembly.key 1619).leftCharge (GramAssembly.key 1619).rightCharge = raw41033 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41033Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41033 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1619).leftCharge (GramAssembly.key 1619).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1619, Integer.Sparse.eval]

theorem keyMoment1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1620) =
      Integer.Sparse.eval keyMomentRow1620 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1620).leftCharge (GramAssembly.key 1620).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2090) := by
    have ha : gramCharges (GramAssembly.key 1620).leftCharge (GramAssembly.key 1620).rightCharge = raw41034 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41034Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41034 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1620).leftCharge (GramAssembly.key 1620).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1620, Integer.Sparse.eval]

theorem keyMoment1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1621) =
      Integer.Sparse.eval keyMomentRow1621 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1621).leftCharge (GramAssembly.key 1621).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1808) := by
    have ha : gramCharges (GramAssembly.key 1621).leftCharge (GramAssembly.key 1621).rightCharge = raw41035 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41035Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41035 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1621).leftCharge (GramAssembly.key 1621).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1621, Integer.Sparse.eval]

theorem keyMoment1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1622) =
      Integer.Sparse.eval keyMomentRow1622 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1622).leftCharge (GramAssembly.key 1622).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1973) := by
    have ha : gramCharges (GramAssembly.key 1622).leftCharge (GramAssembly.key 1622).rightCharge = raw41036 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41036Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41036 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1622).leftCharge (GramAssembly.key 1622).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1622, Integer.Sparse.eval]

theorem keyMoment1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1623) =
      Integer.Sparse.eval keyMomentRow1623 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1623).leftCharge (GramAssembly.key 1623).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1790) := by
    have ha : gramCharges (GramAssembly.key 1623).leftCharge (GramAssembly.key 1623).rightCharge = raw41037 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41037Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41037 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1623).leftCharge (GramAssembly.key 1623).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1623, Integer.Sparse.eval]

theorem keyMoment1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1624) =
      Integer.Sparse.eval keyMomentRow1624 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1624).leftCharge (GramAssembly.key 1624).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2759) := by
    have ha : gramCharges (GramAssembly.key 1624).leftCharge (GramAssembly.key 1624).rightCharge = raw41038 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41038Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41038 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1624).leftCharge (GramAssembly.key 1624).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1624, Integer.Sparse.eval]

theorem keyMoment1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1625) =
      Integer.Sparse.eval keyMomentRow1625 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1625).leftCharge (GramAssembly.key 1625).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2902) := by
    have ha : gramCharges (GramAssembly.key 1625).leftCharge (GramAssembly.key 1625).rightCharge = raw41039 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41039Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41039 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1625).leftCharge (GramAssembly.key 1625).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1625, Integer.Sparse.eval]

theorem keyMoment1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1626) =
      Integer.Sparse.eval keyMomentRow1626 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1626).leftCharge (GramAssembly.key 1626).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2984) := by
    have ha : gramCharges (GramAssembly.key 1626).leftCharge (GramAssembly.key 1626).rightCharge = raw41040 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41040Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41040 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1626).leftCharge (GramAssembly.key 1626).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1626, Integer.Sparse.eval]

theorem keyMoment1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1627) =
      Integer.Sparse.eval keyMomentRow1627 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1627).leftCharge (GramAssembly.key 1627).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2848) := by
    have ha : gramCharges (GramAssembly.key 1627).leftCharge (GramAssembly.key 1627).rightCharge = raw41041 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41041Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41041 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1627).leftCharge (GramAssembly.key 1627).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1627, Integer.Sparse.eval]

theorem keyMoment1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1628) =
      Integer.Sparse.eval keyMomentRow1628 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1628).leftCharge (GramAssembly.key 1628).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2979) := by
    have ha : gramCharges (GramAssembly.key 1628).leftCharge (GramAssembly.key 1628).rightCharge = raw41042 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41042Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41042 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1628).leftCharge (GramAssembly.key 1628).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1628, Integer.Sparse.eval]

theorem keyMoment1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1629) =
      Integer.Sparse.eval keyMomentRow1629 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1629).leftCharge (GramAssembly.key 1629).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2811) := by
    have ha : gramCharges (GramAssembly.key 1629).leftCharge (GramAssembly.key 1629).rightCharge = raw41043 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41043Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41043 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1629).leftCharge (GramAssembly.key 1629).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1629, Integer.Sparse.eval]

theorem keyMoment1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1630) =
      Integer.Sparse.eval keyMomentRow1630 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1630).leftCharge (GramAssembly.key 1630).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2900) := by
    have ha : gramCharges (GramAssembly.key 1630).leftCharge (GramAssembly.key 1630).rightCharge = raw41044 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41044Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41044 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1630).leftCharge (GramAssembly.key 1630).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1630, Integer.Sparse.eval]

theorem keyMoment1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1631) =
      Integer.Sparse.eval keyMomentRow1631 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1631).leftCharge (GramAssembly.key 1631).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2797) := by
    have ha : gramCharges (GramAssembly.key 1631).leftCharge (GramAssembly.key 1631).rightCharge = raw41045 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41045Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41045 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1631).leftCharge (GramAssembly.key 1631).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1631, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

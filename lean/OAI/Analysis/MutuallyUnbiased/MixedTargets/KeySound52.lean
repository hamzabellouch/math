import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical320
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical321

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1664) =
      Integer.Sparse.eval keyMomentRow1664 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1664).leftCharge (GramAssembly.key 1664).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1964) := by
    have ha : gramCharges (GramAssembly.key 1664).leftCharge (GramAssembly.key 1664).rightCharge = raw41078 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41078Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41078 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1664).leftCharge (GramAssembly.key 1664).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1664, Integer.Sparse.eval]

theorem keyMoment1665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1665) =
      Integer.Sparse.eval keyMomentRow1665 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1665).leftCharge (GramAssembly.key 1665).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3054) := by
    have ha : gramCharges (GramAssembly.key 1665).leftCharge (GramAssembly.key 1665).rightCharge = raw41079 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41079Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41079 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1665).leftCharge (GramAssembly.key 1665).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1665, Integer.Sparse.eval]

theorem keyMoment1666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1666) =
      Integer.Sparse.eval keyMomentRow1666 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1666).leftCharge (GramAssembly.key 1666).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2954) := by
    have ha : gramCharges (GramAssembly.key 1666).leftCharge (GramAssembly.key 1666).rightCharge = raw41080 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41080Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41080 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1666).leftCharge (GramAssembly.key 1666).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1666, Integer.Sparse.eval]

theorem keyMoment1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1667) =
      Integer.Sparse.eval keyMomentRow1667 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1667).leftCharge (GramAssembly.key 1667).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2817) := by
    have ha : gramCharges (GramAssembly.key 1667).leftCharge (GramAssembly.key 1667).rightCharge = raw41081 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41081Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41081 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1667).leftCharge (GramAssembly.key 1667).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1667, Integer.Sparse.eval]

theorem keyMoment1668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1668) =
      Integer.Sparse.eval keyMomentRow1668 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1668).leftCharge (GramAssembly.key 1668).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2881) := by
    have ha : gramCharges (GramAssembly.key 1668).leftCharge (GramAssembly.key 1668).rightCharge = raw41082 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41082Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41082 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1668).leftCharge (GramAssembly.key 1668).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1668, Integer.Sparse.eval]

theorem keyMoment1669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1669) =
      Integer.Sparse.eval keyMomentRow1669 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1669).leftCharge (GramAssembly.key 1669).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3077) := by
    have ha : gramCharges (GramAssembly.key 1669).leftCharge (GramAssembly.key 1669).rightCharge = raw41083 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41083Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41083 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1669).leftCharge (GramAssembly.key 1669).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1669, Integer.Sparse.eval]

theorem keyMoment1670 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1670) =
      Integer.Sparse.eval keyMomentRow1670 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1670).leftCharge (GramAssembly.key 1670).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2896) := by
    have ha : gramCharges (GramAssembly.key 1670).leftCharge (GramAssembly.key 1670).rightCharge = raw41084 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41084Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41084 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1670).leftCharge (GramAssembly.key 1670).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1670, Integer.Sparse.eval]

theorem keyMoment1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1671) =
      Integer.Sparse.eval keyMomentRow1671 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1671).leftCharge (GramAssembly.key 1671).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2924) := by
    have ha : gramCharges (GramAssembly.key 1671).leftCharge (GramAssembly.key 1671).rightCharge = raw41085 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41085Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41085 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1671).leftCharge (GramAssembly.key 1671).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1671, Integer.Sparse.eval]

theorem keyMoment1672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1672) =
      Integer.Sparse.eval keyMomentRow1672 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1672).leftCharge (GramAssembly.key 1672).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2807) := by
    have ha : gramCharges (GramAssembly.key 1672).leftCharge (GramAssembly.key 1672).rightCharge = raw41086 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41086Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41086 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1672).leftCharge (GramAssembly.key 1672).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1672, Integer.Sparse.eval]

theorem keyMoment1673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1673) =
      Integer.Sparse.eval keyMomentRow1673 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1673).leftCharge (GramAssembly.key 1673).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2820) := by
    have ha : gramCharges (GramAssembly.key 1673).leftCharge (GramAssembly.key 1673).rightCharge = raw41087 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41087Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41087 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1673).leftCharge (GramAssembly.key 1673).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1673, Integer.Sparse.eval]

theorem keyMoment1674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1674) =
      Integer.Sparse.eval keyMomentRow1674 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1674).leftCharge (GramAssembly.key 1674).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2889) := by
    have ha : gramCharges (GramAssembly.key 1674).leftCharge (GramAssembly.key 1674).rightCharge = raw41088 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41088Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41088 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1674).leftCharge (GramAssembly.key 1674).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1674, Integer.Sparse.eval]

theorem keyMoment1675 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1675) =
      Integer.Sparse.eval keyMomentRow1675 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1675).leftCharge (GramAssembly.key 1675).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2815) := by
    have ha : gramCharges (GramAssembly.key 1675).leftCharge (GramAssembly.key 1675).rightCharge = raw41089 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41089Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41089 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1675).leftCharge (GramAssembly.key 1675).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1675, Integer.Sparse.eval]

theorem keyMoment1676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1676) =
      Integer.Sparse.eval keyMomentRow1676 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1676).leftCharge (GramAssembly.key 1676).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2931) := by
    have ha : gramCharges (GramAssembly.key 1676).leftCharge (GramAssembly.key 1676).rightCharge = raw41090 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41090Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41090 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1676).leftCharge (GramAssembly.key 1676).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1676, Integer.Sparse.eval]

theorem keyMoment1677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1677) =
      Integer.Sparse.eval keyMomentRow1677 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1677).leftCharge (GramAssembly.key 1677).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2813) := by
    have ha : gramCharges (GramAssembly.key 1677).leftCharge (GramAssembly.key 1677).rightCharge = raw41091 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41091Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41091 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1677).leftCharge (GramAssembly.key 1677).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1677, Integer.Sparse.eval]

theorem keyMoment1678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1678) =
      Integer.Sparse.eval keyMomentRow1678 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1678).leftCharge (GramAssembly.key 1678).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2893) := by
    have ha : gramCharges (GramAssembly.key 1678).leftCharge (GramAssembly.key 1678).rightCharge = raw41092 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41092Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41092 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1678).leftCharge (GramAssembly.key 1678).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1678, Integer.Sparse.eval]

theorem keyMoment1679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1679) =
      Integer.Sparse.eval keyMomentRow1679 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1679).leftCharge (GramAssembly.key 1679).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3053) := by
    have ha : gramCharges (GramAssembly.key 1679).leftCharge (GramAssembly.key 1679).rightCharge = raw5460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw5460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical5460 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1679).leftCharge (GramAssembly.key 1679).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1679, Integer.Sparse.eval]

theorem keyMoment1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1680) =
      Integer.Sparse.eval keyMomentRow1680 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1680).leftCharge (GramAssembly.key 1680).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2814) := by
    have ha : gramCharges (GramAssembly.key 1680).leftCharge (GramAssembly.key 1680).rightCharge = raw41093 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41093Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41093 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1680).leftCharge (GramAssembly.key 1680).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1680, Integer.Sparse.eval]

theorem keyMoment1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1681) =
      Integer.Sparse.eval keyMomentRow1681 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1681).leftCharge (GramAssembly.key 1681).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2815) := by
    have ha : gramCharges (GramAssembly.key 1681).leftCharge (GramAssembly.key 1681).rightCharge = raw41094 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41094Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41094 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1681).leftCharge (GramAssembly.key 1681).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1681, Integer.Sparse.eval]

theorem keyMoment1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1682) =
      Integer.Sparse.eval keyMomentRow1682 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1682).leftCharge (GramAssembly.key 1682).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2809) := by
    have ha : gramCharges (GramAssembly.key 1682).leftCharge (GramAssembly.key 1682).rightCharge = raw41095 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41095Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41095 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1682).leftCharge (GramAssembly.key 1682).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1682, Integer.Sparse.eval]

theorem keyMoment1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1683) =
      Integer.Sparse.eval keyMomentRow1683 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1683).leftCharge (GramAssembly.key 1683).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1145) := by
    have ha : gramCharges (GramAssembly.key 1683).leftCharge (GramAssembly.key 1683).rightCharge = raw41096 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41096Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41096 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1683).leftCharge (GramAssembly.key 1683).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1683, Integer.Sparse.eval]

theorem keyMoment1684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1684) =
      Integer.Sparse.eval keyMomentRow1684 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1684).leftCharge (GramAssembly.key 1684).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2519) := by
    have ha : gramCharges (GramAssembly.key 1684).leftCharge (GramAssembly.key 1684).rightCharge = raw41097 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41097Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41097 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1684).leftCharge (GramAssembly.key 1684).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1684, Integer.Sparse.eval]

theorem keyMoment1685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1685) =
      Integer.Sparse.eval keyMomentRow1685 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1685).leftCharge (GramAssembly.key 1685).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2485) := by
    have ha : gramCharges (GramAssembly.key 1685).leftCharge (GramAssembly.key 1685).rightCharge = raw41098 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41098Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41098 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1685).leftCharge (GramAssembly.key 1685).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1685, Integer.Sparse.eval]

theorem keyMoment1686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1686) =
      Integer.Sparse.eval keyMomentRow1686 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1686).leftCharge (GramAssembly.key 1686).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2434) := by
    have ha : gramCharges (GramAssembly.key 1686).leftCharge (GramAssembly.key 1686).rightCharge = raw41099 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41099Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41099 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1686).leftCharge (GramAssembly.key 1686).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1686, Integer.Sparse.eval]

theorem keyMoment1687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1687) =
      Integer.Sparse.eval keyMomentRow1687 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1687).leftCharge (GramAssembly.key 1687).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2818) := by
    have ha : gramCharges (GramAssembly.key 1687).leftCharge (GramAssembly.key 1687).rightCharge = raw41100 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41100Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41100 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1687).leftCharge (GramAssembly.key 1687).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1687, Integer.Sparse.eval]

theorem keyMoment1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1688) =
      Integer.Sparse.eval keyMomentRow1688 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1688).leftCharge (GramAssembly.key 1688).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2429) := by
    have ha : gramCharges (GramAssembly.key 1688).leftCharge (GramAssembly.key 1688).rightCharge = raw41101 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41101Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41101 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1688).leftCharge (GramAssembly.key 1688).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1688, Integer.Sparse.eval]

theorem keyMoment1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1689) =
      Integer.Sparse.eval keyMomentRow1689 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1689).leftCharge (GramAssembly.key 1689).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 620) := by
    have ha : gramCharges (GramAssembly.key 1689).leftCharge (GramAssembly.key 1689).rightCharge = raw41102 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41102Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41102 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1689).leftCharge (GramAssembly.key 1689).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1689, Integer.Sparse.eval]

theorem keyMoment1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1690) =
      Integer.Sparse.eval keyMomentRow1690 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1690).leftCharge (GramAssembly.key 1690).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1091) := by
    have ha : gramCharges (GramAssembly.key 1690).leftCharge (GramAssembly.key 1690).rightCharge = raw41103 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41103Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41103 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1690).leftCharge (GramAssembly.key 1690).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1690, Integer.Sparse.eval]

theorem keyMoment1691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1691) =
      Integer.Sparse.eval keyMomentRow1691 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1691).leftCharge (GramAssembly.key 1691).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 611) := by
    have ha : gramCharges (GramAssembly.key 1691).leftCharge (GramAssembly.key 1691).rightCharge = raw41104 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41104Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41104 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1691).leftCharge (GramAssembly.key 1691).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1691, Integer.Sparse.eval]

theorem keyMoment1692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1692) =
      Integer.Sparse.eval keyMomentRow1692 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1692).leftCharge (GramAssembly.key 1692).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1046) := by
    have ha : gramCharges (GramAssembly.key 1692).leftCharge (GramAssembly.key 1692).rightCharge = raw41105 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41105Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41105 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1692).leftCharge (GramAssembly.key 1692).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1692, Integer.Sparse.eval]

theorem keyMoment1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1693) =
      Integer.Sparse.eval keyMomentRow1693 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1693).leftCharge (GramAssembly.key 1693).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 939) := by
    have ha : gramCharges (GramAssembly.key 1693).leftCharge (GramAssembly.key 1693).rightCharge = raw41106 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41106Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41106 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1693).leftCharge (GramAssembly.key 1693).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1693, Integer.Sparse.eval]

theorem keyMoment1694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1694) =
      Integer.Sparse.eval keyMomentRow1694 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1694).leftCharge (GramAssembly.key 1694).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2345) := by
    have ha : gramCharges (GramAssembly.key 1694).leftCharge (GramAssembly.key 1694).rightCharge = raw41107 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41107Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41107 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1694).leftCharge (GramAssembly.key 1694).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1694, Integer.Sparse.eval]

theorem keyMoment1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1695) =
      Integer.Sparse.eval keyMomentRow1695 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1695).leftCharge (GramAssembly.key 1695).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 930) := by
    have ha : gramCharges (GramAssembly.key 1695).leftCharge (GramAssembly.key 1695).rightCharge = raw41108 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41108Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41108 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1695).leftCharge (GramAssembly.key 1695).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1695, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

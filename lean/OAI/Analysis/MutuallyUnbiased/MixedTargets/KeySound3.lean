import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical308
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical309

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment96 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 96) =
      Integer.Sparse.eval keyMomentRow96 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 96).leftCharge (GramAssembly.key 96).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 256) := by
    have ha : gramCharges (GramAssembly.key 96).leftCharge (GramAssembly.key 96).rightCharge = raw39546 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39546Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39546 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 96).leftCharge (GramAssembly.key 96).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow96, Integer.Sparse.eval]

theorem keyMoment97 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 97) =
      Integer.Sparse.eval keyMomentRow97 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 97).leftCharge (GramAssembly.key 97).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 97).leftCharge (GramAssembly.key 97).rightCharge = raw39547 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39547Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39547 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 97).leftCharge (GramAssembly.key 97).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow97, Integer.Sparse.eval]

theorem keyMoment98 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 98) =
      Integer.Sparse.eval keyMomentRow98 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 98).leftCharge (GramAssembly.key 98).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 251) := by
    have ha : gramCharges (GramAssembly.key 98).leftCharge (GramAssembly.key 98).rightCharge = raw39548 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39548Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39548 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 98).leftCharge (GramAssembly.key 98).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow98, Integer.Sparse.eval]

theorem keyMoment99 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 99) =
      Integer.Sparse.eval keyMomentRow99 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 99).leftCharge (GramAssembly.key 99).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 196) := by
    have ha : gramCharges (GramAssembly.key 99).leftCharge (GramAssembly.key 99).rightCharge = raw39549 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39549Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39549 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 99).leftCharge (GramAssembly.key 99).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow99, Integer.Sparse.eval]

theorem keyMoment100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 100) =
      Integer.Sparse.eval keyMomentRow100 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 100).leftCharge (GramAssembly.key 100).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 229) := by
    have ha : gramCharges (GramAssembly.key 100).leftCharge (GramAssembly.key 100).rightCharge = raw39550 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39550Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39550 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 100).leftCharge (GramAssembly.key 100).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow100, Integer.Sparse.eval]

theorem keyMoment101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 101) =
      Integer.Sparse.eval keyMomentRow101 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 101).leftCharge (GramAssembly.key 101).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 214) := by
    have ha : gramCharges (GramAssembly.key 101).leftCharge (GramAssembly.key 101).rightCharge = raw39551 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39551Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39551 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 101).leftCharge (GramAssembly.key 101).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow101, Integer.Sparse.eval]

theorem keyMoment102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 102) =
      Integer.Sparse.eval keyMomentRow102 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 102).leftCharge (GramAssembly.key 102).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 168) := by
    have ha : gramCharges (GramAssembly.key 102).leftCharge (GramAssembly.key 102).rightCharge = raw39552 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39552Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39552 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 102).leftCharge (GramAssembly.key 102).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow102, Integer.Sparse.eval]

theorem keyMoment103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 103) =
      Integer.Sparse.eval keyMomentRow103 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 103).leftCharge (GramAssembly.key 103).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 195) := by
    have ha : gramCharges (GramAssembly.key 103).leftCharge (GramAssembly.key 103).rightCharge = raw39553 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39553Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39553 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 103).leftCharge (GramAssembly.key 103).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow103, Integer.Sparse.eval]

theorem keyMoment104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 104) =
      Integer.Sparse.eval keyMomentRow104 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 104).leftCharge (GramAssembly.key 104).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 240) := by
    have ha : gramCharges (GramAssembly.key 104).leftCharge (GramAssembly.key 104).rightCharge = raw39554 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39554Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39554 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 104).leftCharge (GramAssembly.key 104).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow104, Integer.Sparse.eval]

theorem keyMoment105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 105) =
      Integer.Sparse.eval keyMomentRow105 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 105).leftCharge (GramAssembly.key 105).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 248) := by
    have ha : gramCharges (GramAssembly.key 105).leftCharge (GramAssembly.key 105).rightCharge = raw39555 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39555Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39555 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 105).leftCharge (GramAssembly.key 105).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow105, Integer.Sparse.eval]

theorem keyMoment106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 106) =
      Integer.Sparse.eval keyMomentRow106 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 106).leftCharge (GramAssembly.key 106).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 213) := by
    have ha : gramCharges (GramAssembly.key 106).leftCharge (GramAssembly.key 106).rightCharge = raw39556 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39556Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39556 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 106).leftCharge (GramAssembly.key 106).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow106, Integer.Sparse.eval]

theorem keyMoment107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 107) =
      Integer.Sparse.eval keyMomentRow107 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 107).leftCharge (GramAssembly.key 107).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 167) := by
    have ha : gramCharges (GramAssembly.key 107).leftCharge (GramAssembly.key 107).rightCharge = raw39557 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39557Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39557 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 107).leftCharge (GramAssembly.key 107).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow107, Integer.Sparse.eval]

theorem keyMoment108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 108) =
      Integer.Sparse.eval keyMomentRow108 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 108).leftCharge (GramAssembly.key 108).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 253) := by
    have ha : gramCharges (GramAssembly.key 108).leftCharge (GramAssembly.key 108).rightCharge = raw39558 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39558Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39558 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 108).leftCharge (GramAssembly.key 108).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow108, Integer.Sparse.eval]

theorem keyMoment109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 109) =
      Integer.Sparse.eval keyMomentRow109 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 109).leftCharge (GramAssembly.key 109).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 257) := by
    have ha : gramCharges (GramAssembly.key 109).leftCharge (GramAssembly.key 109).rightCharge = raw39559 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39559Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39559 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 109).leftCharge (GramAssembly.key 109).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow109, Integer.Sparse.eval]

theorem keyMoment110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 110) =
      Integer.Sparse.eval keyMomentRow110 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 110).leftCharge (GramAssembly.key 110).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 189) := by
    have ha : gramCharges (GramAssembly.key 110).leftCharge (GramAssembly.key 110).rightCharge = raw39560 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39560Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39560 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 110).leftCharge (GramAssembly.key 110).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow110, Integer.Sparse.eval]

theorem keyMoment111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 111) =
      Integer.Sparse.eval keyMomentRow111 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 111).leftCharge (GramAssembly.key 111).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 254) := by
    have ha : gramCharges (GramAssembly.key 111).leftCharge (GramAssembly.key 111).rightCharge = raw39561 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39561Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39561 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 111).leftCharge (GramAssembly.key 111).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow111, Integer.Sparse.eval]

theorem keyMoment112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 112) =
      Integer.Sparse.eval keyMomentRow112 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 112).leftCharge (GramAssembly.key 112).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 260) := by
    have ha : gramCharges (GramAssembly.key 112).leftCharge (GramAssembly.key 112).rightCharge = raw39562 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39562Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39562 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 112).leftCharge (GramAssembly.key 112).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow112, Integer.Sparse.eval]

theorem keyMoment113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 113) =
      Integer.Sparse.eval keyMomentRow113 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 113).leftCharge (GramAssembly.key 113).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 190) := by
    have ha : gramCharges (GramAssembly.key 113).leftCharge (GramAssembly.key 113).rightCharge = raw39563 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39563Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39563 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 113).leftCharge (GramAssembly.key 113).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow113, Integer.Sparse.eval]

theorem keyMoment114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 114) =
      Integer.Sparse.eval keyMomentRow114 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 114).leftCharge (GramAssembly.key 114).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 220) := by
    have ha : gramCharges (GramAssembly.key 114).leftCharge (GramAssembly.key 114).rightCharge = raw39564 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39564Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39564 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 114).leftCharge (GramAssembly.key 114).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow114, Integer.Sparse.eval]

theorem keyMoment115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 115) =
      Integer.Sparse.eval keyMomentRow115 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 115).leftCharge (GramAssembly.key 115).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 163) := by
    have ha : gramCharges (GramAssembly.key 115).leftCharge (GramAssembly.key 115).rightCharge = raw39565 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39565Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39565 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 115).leftCharge (GramAssembly.key 115).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow115, Integer.Sparse.eval]

theorem keyMoment116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 116) =
      Integer.Sparse.eval keyMomentRow116 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 116).leftCharge (GramAssembly.key 116).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 259) := by
    have ha : gramCharges (GramAssembly.key 116).leftCharge (GramAssembly.key 116).rightCharge = raw39566 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39566Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39566 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 116).leftCharge (GramAssembly.key 116).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow116, Integer.Sparse.eval]

theorem keyMoment117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 117) =
      Integer.Sparse.eval keyMomentRow117 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 117).leftCharge (GramAssembly.key 117).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 255) := by
    have ha : gramCharges (GramAssembly.key 117).leftCharge (GramAssembly.key 117).rightCharge = raw39567 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39567Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39567 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 117).leftCharge (GramAssembly.key 117).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow117, Integer.Sparse.eval]

theorem keyMoment118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 118) =
      Integer.Sparse.eval keyMomentRow118 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 118).leftCharge (GramAssembly.key 118).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 134) := by
    have ha : gramCharges (GramAssembly.key 118).leftCharge (GramAssembly.key 118).rightCharge = raw39568 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39568Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39568 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 118).leftCharge (GramAssembly.key 118).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow118, Integer.Sparse.eval]

theorem keyMoment119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 119) =
      Integer.Sparse.eval keyMomentRow119 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 119).leftCharge (GramAssembly.key 119).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 1) := by
    have ha : gramCharges (GramAssembly.key 119).leftCharge (GramAssembly.key 119).rightCharge = raw39569 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39569Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39569 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 119).leftCharge (GramAssembly.key 119).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow119, Integer.Sparse.eval]

theorem keyMoment120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 120) =
      Integer.Sparse.eval keyMomentRow120 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 120).leftCharge (GramAssembly.key 120).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 222) := by
    have ha : gramCharges (GramAssembly.key 120).leftCharge (GramAssembly.key 120).rightCharge = raw39570 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39570Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39570 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 120).leftCharge (GramAssembly.key 120).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow120, Integer.Sparse.eval]

theorem keyMoment121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 121) =
      Integer.Sparse.eval keyMomentRow121 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 121).leftCharge (GramAssembly.key 121).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 117) := by
    have ha : gramCharges (GramAssembly.key 121).leftCharge (GramAssembly.key 121).rightCharge = raw39571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39571 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 121).leftCharge (GramAssembly.key 121).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow121, Integer.Sparse.eval]

theorem keyMoment122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 122) =
      Integer.Sparse.eval keyMomentRow122 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 122).leftCharge (GramAssembly.key 122).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 192) := by
    have ha : gramCharges (GramAssembly.key 122).leftCharge (GramAssembly.key 122).rightCharge = raw39572 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39572Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39572 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 122).leftCharge (GramAssembly.key 122).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow122, Integer.Sparse.eval]

theorem keyMoment123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 123) =
      Integer.Sparse.eval keyMomentRow123 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 123).leftCharge (GramAssembly.key 123).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 239) := by
    have ha : gramCharges (GramAssembly.key 123).leftCharge (GramAssembly.key 123).rightCharge = raw39573 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39573Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39573 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 123).leftCharge (GramAssembly.key 123).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow123, Integer.Sparse.eval]

theorem keyMoment124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 124) =
      Integer.Sparse.eval keyMomentRow124 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 124).leftCharge (GramAssembly.key 124).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 260) := by
    have ha : gramCharges (GramAssembly.key 124).leftCharge (GramAssembly.key 124).rightCharge = raw39574 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39574Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39574 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 124).leftCharge (GramAssembly.key 124).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow124, Integer.Sparse.eval]

theorem keyMoment125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 125) =
      Integer.Sparse.eval keyMomentRow125 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 125).leftCharge (GramAssembly.key 125).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 212) := by
    have ha : gramCharges (GramAssembly.key 125).leftCharge (GramAssembly.key 125).rightCharge = raw39575 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39575Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39575 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 125).leftCharge (GramAssembly.key 125).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow125, Integer.Sparse.eval]

theorem keyMoment126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 126) =
      Integer.Sparse.eval keyMomentRow126 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 126).leftCharge (GramAssembly.key 126).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 221) := by
    have ha : gramCharges (GramAssembly.key 126).leftCharge (GramAssembly.key 126).rightCharge = raw39576 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39576Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39576 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 126).leftCharge (GramAssembly.key 126).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow126, Integer.Sparse.eval]

theorem keyMoment127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 127) =
      Integer.Sparse.eval keyMomentRow127 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 127).leftCharge (GramAssembly.key 127).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 164) := by
    have ha : gramCharges (GramAssembly.key 127).leftCharge (GramAssembly.key 127).rightCharge = raw39577 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39577Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39577 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 127).leftCharge (GramAssembly.key 127).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow127, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

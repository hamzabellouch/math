import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical313

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 672) =
      Integer.Sparse.eval keyMomentRow672 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 672).leftCharge (GramAssembly.key 672).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 373) := by
    have ha : gramCharges (GramAssembly.key 672).leftCharge (GramAssembly.key 672).rightCharge = raw40120 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40120Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40120 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 672).leftCharge (GramAssembly.key 672).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow672, Integer.Sparse.eval]

theorem keyMoment673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 673) =
      Integer.Sparse.eval keyMomentRow673 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 673).leftCharge (GramAssembly.key 673).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 494) := by
    have ha : gramCharges (GramAssembly.key 673).leftCharge (GramAssembly.key 673).rightCharge = raw40121 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40121Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40121 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 673).leftCharge (GramAssembly.key 673).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow673, Integer.Sparse.eval]

theorem keyMoment674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 674) =
      Integer.Sparse.eval keyMomentRow674 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 674).leftCharge (GramAssembly.key 674).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 373) := by
    have ha : gramCharges (GramAssembly.key 674).leftCharge (GramAssembly.key 674).rightCharge = raw40122 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40122Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40122 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 674).leftCharge (GramAssembly.key 674).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow674, Integer.Sparse.eval]

theorem keyMoment675 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 675) =
      Integer.Sparse.eval keyMomentRow675 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 675).leftCharge (GramAssembly.key 675).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 374) := by
    have ha : gramCharges (GramAssembly.key 675).leftCharge (GramAssembly.key 675).rightCharge = raw40123 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40123Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40123 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 675).leftCharge (GramAssembly.key 675).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow675, Integer.Sparse.eval]

theorem keyMoment676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 676) =
      Integer.Sparse.eval keyMomentRow676 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 676).leftCharge (GramAssembly.key 676).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 7) := by
    have ha : gramCharges (GramAssembly.key 676).leftCharge (GramAssembly.key 676).rightCharge = raw40124 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40124Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40124 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 676).leftCharge (GramAssembly.key 676).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow676, Integer.Sparse.eval]

theorem keyMoment677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 677) =
      Integer.Sparse.eval keyMomentRow677 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 677).leftCharge (GramAssembly.key 677).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 488) := by
    have ha : gramCharges (GramAssembly.key 677).leftCharge (GramAssembly.key 677).rightCharge = raw40125 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40125Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40125 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 677).leftCharge (GramAssembly.key 677).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow677, Integer.Sparse.eval]

theorem keyMoment678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 678) =
      Integer.Sparse.eval keyMomentRow678 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 678).leftCharge (GramAssembly.key 678).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 5) := by
    have ha : gramCharges (GramAssembly.key 678).leftCharge (GramAssembly.key 678).rightCharge = raw40126 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40126Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40126 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 678).leftCharge (GramAssembly.key 678).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow678, Integer.Sparse.eval]

theorem keyMoment679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 679) =
      Integer.Sparse.eval keyMomentRow679 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 679).leftCharge (GramAssembly.key 679).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 529) := by
    have ha : gramCharges (GramAssembly.key 679).leftCharge (GramAssembly.key 679).rightCharge = raw40127 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40127Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40127 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 679).leftCharge (GramAssembly.key 679).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow679, Integer.Sparse.eval]

theorem keyMoment680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 680) =
      Integer.Sparse.eval keyMomentRow680 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 680).leftCharge (GramAssembly.key 680).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 505) := by
    have ha : gramCharges (GramAssembly.key 680).leftCharge (GramAssembly.key 680).rightCharge = raw40128 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40128Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40128 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 680).leftCharge (GramAssembly.key 680).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow680, Integer.Sparse.eval]

theorem keyMoment681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 681) =
      Integer.Sparse.eval keyMomentRow681 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 681).leftCharge (GramAssembly.key 681).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 262) := by
    have ha : gramCharges (GramAssembly.key 681).leftCharge (GramAssembly.key 681).rightCharge = raw40129 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40129Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40129 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 681).leftCharge (GramAssembly.key 681).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow681, Integer.Sparse.eval]

theorem keyMoment682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 682) =
      Integer.Sparse.eval keyMomentRow682 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 682).leftCharge (GramAssembly.key 682).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 416) := by
    have ha : gramCharges (GramAssembly.key 682).leftCharge (GramAssembly.key 682).rightCharge = raw40130 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40130Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40130 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 682).leftCharge (GramAssembly.key 682).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow682, Integer.Sparse.eval]

theorem keyMoment683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 683) =
      Integer.Sparse.eval keyMomentRow683 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 683).leftCharge (GramAssembly.key 683).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 7) := by
    have ha : gramCharges (GramAssembly.key 683).leftCharge (GramAssembly.key 683).rightCharge = raw40131 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40131Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40131 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 683).leftCharge (GramAssembly.key 683).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow683, Integer.Sparse.eval]

theorem keyMoment684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 684) =
      Integer.Sparse.eval keyMomentRow684 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 684).leftCharge (GramAssembly.key 684).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 504) := by
    have ha : gramCharges (GramAssembly.key 684).leftCharge (GramAssembly.key 684).rightCharge = raw40132 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40132Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40132 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 684).leftCharge (GramAssembly.key 684).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow684, Integer.Sparse.eval]

theorem keyMoment685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 685) =
      Integer.Sparse.eval keyMomentRow685 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 685).leftCharge (GramAssembly.key 685).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 397) := by
    have ha : gramCharges (GramAssembly.key 685).leftCharge (GramAssembly.key 685).rightCharge = raw40133 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40133Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40133 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 685).leftCharge (GramAssembly.key 685).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow685, Integer.Sparse.eval]

theorem keyMoment686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 686) =
      Integer.Sparse.eval keyMomentRow686 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 686).leftCharge (GramAssembly.key 686).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 532) := by
    have ha : gramCharges (GramAssembly.key 686).leftCharge (GramAssembly.key 686).rightCharge = raw40134 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40134Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40134 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 686).leftCharge (GramAssembly.key 686).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow686, Integer.Sparse.eval]

theorem keyMoment687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 687) =
      Integer.Sparse.eval keyMomentRow687 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 687).leftCharge (GramAssembly.key 687).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 494) := by
    have ha : gramCharges (GramAssembly.key 687).leftCharge (GramAssembly.key 687).rightCharge = raw40135 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40135Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40135 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 687).leftCharge (GramAssembly.key 687).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow687, Integer.Sparse.eval]

theorem keyMoment688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 688) =
      Integer.Sparse.eval keyMomentRow688 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 688).leftCharge (GramAssembly.key 688).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 531) := by
    have ha : gramCharges (GramAssembly.key 688).leftCharge (GramAssembly.key 688).rightCharge = raw40136 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40136Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40136 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 688).leftCharge (GramAssembly.key 688).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow688, Integer.Sparse.eval]

theorem keyMoment689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 689) =
      Integer.Sparse.eval keyMomentRow689 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 689).leftCharge (GramAssembly.key 689).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 259) := by
    have ha : gramCharges (GramAssembly.key 689).leftCharge (GramAssembly.key 689).rightCharge = raw40137 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40137Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40137 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 689).leftCharge (GramAssembly.key 689).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow689, Integer.Sparse.eval]

theorem keyMoment690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 690) =
      Integer.Sparse.eval keyMomentRow690 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 690).leftCharge (GramAssembly.key 690).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 690).leftCharge (GramAssembly.key 690).rightCharge = raw40138 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40138Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40138 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 690).leftCharge (GramAssembly.key 690).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow690, Integer.Sparse.eval]

theorem keyMoment691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 691) =
      Integer.Sparse.eval keyMomentRow691 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 691).leftCharge (GramAssembly.key 691).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 327) := by
    have ha : gramCharges (GramAssembly.key 691).leftCharge (GramAssembly.key 691).rightCharge = raw40139 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40139Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40139 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 691).leftCharge (GramAssembly.key 691).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow691, Integer.Sparse.eval]

theorem keyMoment692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 692) =
      Integer.Sparse.eval keyMomentRow692 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 692).leftCharge (GramAssembly.key 692).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 376) := by
    have ha : gramCharges (GramAssembly.key 692).leftCharge (GramAssembly.key 692).rightCharge = raw40140 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40140Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40140 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 692).leftCharge (GramAssembly.key 692).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow692, Integer.Sparse.eval]

theorem keyMoment693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 693) =
      Integer.Sparse.eval keyMomentRow693 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 693).leftCharge (GramAssembly.key 693).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 693).leftCharge (GramAssembly.key 693).rightCharge = raw40141 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40141Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40141 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 693).leftCharge (GramAssembly.key 693).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow693, Integer.Sparse.eval]

theorem keyMoment694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 694) =
      Integer.Sparse.eval keyMomentRow694 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 694).leftCharge (GramAssembly.key 694).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 378) := by
    have ha : gramCharges (GramAssembly.key 694).leftCharge (GramAssembly.key 694).rightCharge = raw40142 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40142Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40142 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 694).leftCharge (GramAssembly.key 694).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow694, Integer.Sparse.eval]

theorem keyMoment695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 695) =
      Integer.Sparse.eval keyMomentRow695 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 695).leftCharge (GramAssembly.key 695).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 319) := by
    have ha : gramCharges (GramAssembly.key 695).leftCharge (GramAssembly.key 695).rightCharge = raw40143 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40143Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40143 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 695).leftCharge (GramAssembly.key 695).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow695, Integer.Sparse.eval]

theorem keyMoment696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 696) =
      Integer.Sparse.eval keyMomentRow696 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 696).leftCharge (GramAssembly.key 696).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 696).leftCharge (GramAssembly.key 696).rightCharge = raw40144 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40144Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40144 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 696).leftCharge (GramAssembly.key 696).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow696, Integer.Sparse.eval]

theorem keyMoment697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 697) =
      Integer.Sparse.eval keyMomentRow697 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 697).leftCharge (GramAssembly.key 697).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 697).leftCharge (GramAssembly.key 697).rightCharge = raw40145 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40145Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40145 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 697).leftCharge (GramAssembly.key 697).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow697, Integer.Sparse.eval]

theorem keyMoment698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 698) =
      Integer.Sparse.eval keyMomentRow698 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 698).leftCharge (GramAssembly.key 698).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 698).leftCharge (GramAssembly.key 698).rightCharge = raw40146 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40146Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40146 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 698).leftCharge (GramAssembly.key 698).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow698, Integer.Sparse.eval]

theorem keyMoment699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 699) =
      Integer.Sparse.eval keyMomentRow699 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 699).leftCharge (GramAssembly.key 699).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 506) := by
    have ha : gramCharges (GramAssembly.key 699).leftCharge (GramAssembly.key 699).rightCharge = raw40147 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40147Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40147 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 699).leftCharge (GramAssembly.key 699).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow699, Integer.Sparse.eval]

theorem keyMoment700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 700) =
      Integer.Sparse.eval keyMomentRow700 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 700).leftCharge (GramAssembly.key 700).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 526) := by
    have ha : gramCharges (GramAssembly.key 700).leftCharge (GramAssembly.key 700).rightCharge = raw40148 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40148Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40148 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 700).leftCharge (GramAssembly.key 700).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow700, Integer.Sparse.eval]

theorem keyMoment701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 701) =
      Integer.Sparse.eval keyMomentRow701 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 701).leftCharge (GramAssembly.key 701).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 490) := by
    have ha : gramCharges (GramAssembly.key 701).leftCharge (GramAssembly.key 701).rightCharge = raw40149 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40149Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40149 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 701).leftCharge (GramAssembly.key 701).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow701, Integer.Sparse.eval]

theorem keyMoment702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 702) =
      Integer.Sparse.eval keyMomentRow702 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 702).leftCharge (GramAssembly.key 702).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 224) := by
    have ha : gramCharges (GramAssembly.key 702).leftCharge (GramAssembly.key 702).rightCharge = raw40150 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40150Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40150 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 702).leftCharge (GramAssembly.key 702).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow702, Integer.Sparse.eval]

theorem keyMoment703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 703) =
      Integer.Sparse.eval keyMomentRow703 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 703).leftCharge (GramAssembly.key 703).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 703).leftCharge (GramAssembly.key 703).rightCharge = raw40151 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40151Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40151 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 703).leftCharge (GramAssembly.key 703).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow703, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

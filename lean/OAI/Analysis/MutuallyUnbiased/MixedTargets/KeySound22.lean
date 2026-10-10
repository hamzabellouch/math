import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical313

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 704) =
      Integer.Sparse.eval keyMomentRow704 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 704).leftCharge (GramAssembly.key 704).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 532) := by
    have ha : gramCharges (GramAssembly.key 704).leftCharge (GramAssembly.key 704).rightCharge = raw40152 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40152Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40152 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 704).leftCharge (GramAssembly.key 704).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow704, Integer.Sparse.eval]

theorem keyMoment705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 705) =
      Integer.Sparse.eval keyMomentRow705 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 705).leftCharge (GramAssembly.key 705).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 488) := by
    have ha : gramCharges (GramAssembly.key 705).leftCharge (GramAssembly.key 705).rightCharge = raw40153 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40153Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40153 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 705).leftCharge (GramAssembly.key 705).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow705, Integer.Sparse.eval]

theorem keyMoment706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 706) =
      Integer.Sparse.eval keyMomentRow706 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 706).leftCharge (GramAssembly.key 706).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 326) := by
    have ha : gramCharges (GramAssembly.key 706).leftCharge (GramAssembly.key 706).rightCharge = raw40154 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40154Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40154 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 706).leftCharge (GramAssembly.key 706).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow706, Integer.Sparse.eval]

theorem keyMoment707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 707) =
      Integer.Sparse.eval keyMomentRow707 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 707).leftCharge (GramAssembly.key 707).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 533) := by
    have ha : gramCharges (GramAssembly.key 707).leftCharge (GramAssembly.key 707).rightCharge = raw40155 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40155Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40155 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 707).leftCharge (GramAssembly.key 707).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow707, Integer.Sparse.eval]

theorem keyMoment708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 708) =
      Integer.Sparse.eval keyMomentRow708 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 708).leftCharge (GramAssembly.key 708).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 708).leftCharge (GramAssembly.key 708).rightCharge = raw40156 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40156Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40156 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 708).leftCharge (GramAssembly.key 708).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow708, Integer.Sparse.eval]

theorem keyMoment709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 709) =
      Integer.Sparse.eval keyMomentRow709 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 709).leftCharge (GramAssembly.key 709).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 709).leftCharge (GramAssembly.key 709).rightCharge = raw40157 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40157Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40157 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 709).leftCharge (GramAssembly.key 709).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow709, Integer.Sparse.eval]

theorem keyMoment710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 710) =
      Integer.Sparse.eval keyMomentRow710 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 710).leftCharge (GramAssembly.key 710).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 403) := by
    have ha : gramCharges (GramAssembly.key 710).leftCharge (GramAssembly.key 710).rightCharge = raw40158 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40158Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40158 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 710).leftCharge (GramAssembly.key 710).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow710, Integer.Sparse.eval]

theorem keyMoment711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 711) =
      Integer.Sparse.eval keyMomentRow711 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 711).leftCharge (GramAssembly.key 711).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 711).leftCharge (GramAssembly.key 711).rightCharge = raw40159 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40159Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40159 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 711).leftCharge (GramAssembly.key 711).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow711, Integer.Sparse.eval]

theorem keyMoment712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 712) =
      Integer.Sparse.eval keyMomentRow712 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 712).leftCharge (GramAssembly.key 712).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 526) := by
    have ha : gramCharges (GramAssembly.key 712).leftCharge (GramAssembly.key 712).rightCharge = raw40160 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40160Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40160 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 712).leftCharge (GramAssembly.key 712).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow712, Integer.Sparse.eval]

theorem keyMoment713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 713) =
      Integer.Sparse.eval keyMomentRow713 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 713).leftCharge (GramAssembly.key 713).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 713).leftCharge (GramAssembly.key 713).rightCharge = raw40161 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40161Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40161 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 713).leftCharge (GramAssembly.key 713).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow713, Integer.Sparse.eval]

theorem keyMoment714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 714) =
      Integer.Sparse.eval keyMomentRow714 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 714).leftCharge (GramAssembly.key 714).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 714).leftCharge (GramAssembly.key 714).rightCharge = raw40162 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40162Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40162 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 714).leftCharge (GramAssembly.key 714).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow714, Integer.Sparse.eval]

theorem keyMoment715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 715) =
      Integer.Sparse.eval keyMomentRow715 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 715).leftCharge (GramAssembly.key 715).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 715).leftCharge (GramAssembly.key 715).rightCharge = raw40163 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40163Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40163 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 715).leftCharge (GramAssembly.key 715).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow715, Integer.Sparse.eval]

theorem keyMoment716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 716) =
      Integer.Sparse.eval keyMomentRow716 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 716).leftCharge (GramAssembly.key 716).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 432) := by
    have ha : gramCharges (GramAssembly.key 716).leftCharge (GramAssembly.key 716).rightCharge = raw40164 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40164Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40164 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 716).leftCharge (GramAssembly.key 716).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow716, Integer.Sparse.eval]

theorem keyMoment717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 717) =
      Integer.Sparse.eval keyMomentRow717 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 717).leftCharge (GramAssembly.key 717).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 717).leftCharge (GramAssembly.key 717).rightCharge = raw40165 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40165Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40165 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 717).leftCharge (GramAssembly.key 717).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow717, Integer.Sparse.eval]

theorem keyMoment718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 718) =
      Integer.Sparse.eval keyMomentRow718 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 718).leftCharge (GramAssembly.key 718).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 429) := by
    have ha : gramCharges (GramAssembly.key 718).leftCharge (GramAssembly.key 718).rightCharge = raw40166 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40166Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40166 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 718).leftCharge (GramAssembly.key 718).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow718, Integer.Sparse.eval]

theorem keyMoment719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 719) =
      Integer.Sparse.eval keyMomentRow719 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 719).leftCharge (GramAssembly.key 719).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 719).leftCharge (GramAssembly.key 719).rightCharge = raw40167 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40167Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40167 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 719).leftCharge (GramAssembly.key 719).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow719, Integer.Sparse.eval]

theorem keyMoment720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 720) =
      Integer.Sparse.eval keyMomentRow720 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 720).leftCharge (GramAssembly.key 720).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 526) := by
    have ha : gramCharges (GramAssembly.key 720).leftCharge (GramAssembly.key 720).rightCharge = raw40168 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40168Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40168 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 720).leftCharge (GramAssembly.key 720).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow720, Integer.Sparse.eval]

theorem keyMoment721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 721) =
      Integer.Sparse.eval keyMomentRow721 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 721).leftCharge (GramAssembly.key 721).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 721).leftCharge (GramAssembly.key 721).rightCharge = raw40169 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40169Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40169 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 721).leftCharge (GramAssembly.key 721).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow721, Integer.Sparse.eval]

theorem keyMoment722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 722) =
      Integer.Sparse.eval keyMomentRow722 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 722).leftCharge (GramAssembly.key 722).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 404) := by
    have ha : gramCharges (GramAssembly.key 722).leftCharge (GramAssembly.key 722).rightCharge = raw40170 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40170Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40170 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 722).leftCharge (GramAssembly.key 722).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow722, Integer.Sparse.eval]

theorem keyMoment723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 723) =
      Integer.Sparse.eval keyMomentRow723 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 723).leftCharge (GramAssembly.key 723).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 149) := by
    have ha : gramCharges (GramAssembly.key 723).leftCharge (GramAssembly.key 723).rightCharge = raw40171 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40171Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40171 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 723).leftCharge (GramAssembly.key 723).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow723, Integer.Sparse.eval]

theorem keyMoment724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 724) =
      Integer.Sparse.eval keyMomentRow724 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 724).leftCharge (GramAssembly.key 724).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 390) := by
    have ha : gramCharges (GramAssembly.key 724).leftCharge (GramAssembly.key 724).rightCharge = raw40172 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40172Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40172 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 724).leftCharge (GramAssembly.key 724).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow724, Integer.Sparse.eval]

theorem keyMoment725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 725) =
      Integer.Sparse.eval keyMomentRow725 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 725).leftCharge (GramAssembly.key 725).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 527) := by
    have ha : gramCharges (GramAssembly.key 725).leftCharge (GramAssembly.key 725).rightCharge = raw40173 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40173Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40173 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 725).leftCharge (GramAssembly.key 725).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow725, Integer.Sparse.eval]

theorem keyMoment726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 726) =
      Integer.Sparse.eval keyMomentRow726 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 726).leftCharge (GramAssembly.key 726).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 521) := by
    have ha : gramCharges (GramAssembly.key 726).leftCharge (GramAssembly.key 726).rightCharge = raw40174 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40174Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40174 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 726).leftCharge (GramAssembly.key 726).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow726, Integer.Sparse.eval]

theorem keyMoment727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 727) =
      Integer.Sparse.eval keyMomentRow727 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 727).leftCharge (GramAssembly.key 727).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 325) := by
    have ha : gramCharges (GramAssembly.key 727).leftCharge (GramAssembly.key 727).rightCharge = raw40175 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40175Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40175 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 727).leftCharge (GramAssembly.key 727).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow727, Integer.Sparse.eval]

theorem keyMoment728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 728) =
      Integer.Sparse.eval keyMomentRow728 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 728).leftCharge (GramAssembly.key 728).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 728).leftCharge (GramAssembly.key 728).rightCharge = raw40176 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40176Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40176 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 728).leftCharge (GramAssembly.key 728).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow728, Integer.Sparse.eval]

theorem keyMoment729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 729) =
      Integer.Sparse.eval keyMomentRow729 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 729).leftCharge (GramAssembly.key 729).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 306) := by
    have ha : gramCharges (GramAssembly.key 729).leftCharge (GramAssembly.key 729).rightCharge = raw40177 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40177Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40177 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 729).leftCharge (GramAssembly.key 729).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow729, Integer.Sparse.eval]

theorem keyMoment730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 730) =
      Integer.Sparse.eval keyMomentRow730 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 730).leftCharge (GramAssembly.key 730).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 730).leftCharge (GramAssembly.key 730).rightCharge = raw40178 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40178Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40178 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 730).leftCharge (GramAssembly.key 730).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow730, Integer.Sparse.eval]

theorem keyMoment731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 731) =
      Integer.Sparse.eval keyMomentRow731 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 731).leftCharge (GramAssembly.key 731).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 301) := by
    have ha : gramCharges (GramAssembly.key 731).leftCharge (GramAssembly.key 731).rightCharge = raw40179 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40179Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40179 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 731).leftCharge (GramAssembly.key 731).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow731, Integer.Sparse.eval]

theorem keyMoment732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 732) =
      Integer.Sparse.eval keyMomentRow732 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 732).leftCharge (GramAssembly.key 732).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 376) := by
    have ha : gramCharges (GramAssembly.key 732).leftCharge (GramAssembly.key 732).rightCharge = raw40180 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40180Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40180 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 732).leftCharge (GramAssembly.key 732).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow732, Integer.Sparse.eval]

theorem keyMoment733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 733) =
      Integer.Sparse.eval keyMomentRow733 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 733).leftCharge (GramAssembly.key 733).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 733).leftCharge (GramAssembly.key 733).rightCharge = raw40181 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40181Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40181 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 733).leftCharge (GramAssembly.key 733).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow733, Integer.Sparse.eval]

theorem keyMoment734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 734) =
      Integer.Sparse.eval keyMomentRow734 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 734).leftCharge (GramAssembly.key 734).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 305) := by
    have ha : gramCharges (GramAssembly.key 734).leftCharge (GramAssembly.key 734).rightCharge = raw40182 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40182Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40182 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 734).leftCharge (GramAssembly.key 734).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow734, Integer.Sparse.eval]

theorem keyMoment735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 735) =
      Integer.Sparse.eval keyMomentRow735 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 735).leftCharge (GramAssembly.key 735).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 378) := by
    have ha : gramCharges (GramAssembly.key 735).leftCharge (GramAssembly.key 735).rightCharge = raw40183 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40183Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40183 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 735).leftCharge (GramAssembly.key 735).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow735, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

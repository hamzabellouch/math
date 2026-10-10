import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical312
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical313

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 608) =
      Integer.Sparse.eval keyMomentRow608 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 608).leftCharge (GramAssembly.key 608).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 395) := by
    have ha : gramCharges (GramAssembly.key 608).leftCharge (GramAssembly.key 608).rightCharge = raw40056 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40056Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40056 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 608).leftCharge (GramAssembly.key 608).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow608, Integer.Sparse.eval]

theorem keyMoment609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 609) =
      Integer.Sparse.eval keyMomentRow609 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 609).leftCharge (GramAssembly.key 609).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 394) := by
    have ha : gramCharges (GramAssembly.key 609).leftCharge (GramAssembly.key 609).rightCharge = raw40057 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40057Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40057 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 609).leftCharge (GramAssembly.key 609).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow609, Integer.Sparse.eval]

theorem keyMoment610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 610) =
      Integer.Sparse.eval keyMomentRow610 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 610).leftCharge (GramAssembly.key 610).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 358) := by
    have ha : gramCharges (GramAssembly.key 610).leftCharge (GramAssembly.key 610).rightCharge = raw40058 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40058Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40058 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 610).leftCharge (GramAssembly.key 610).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow610, Integer.Sparse.eval]

theorem keyMoment611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 611) =
      Integer.Sparse.eval keyMomentRow611 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 611).leftCharge (GramAssembly.key 611).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 357) := by
    have ha : gramCharges (GramAssembly.key 611).leftCharge (GramAssembly.key 611).rightCharge = raw40059 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40059Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40059 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 611).leftCharge (GramAssembly.key 611).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow611, Integer.Sparse.eval]

theorem keyMoment612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 612) =
      Integer.Sparse.eval keyMomentRow612 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 612).leftCharge (GramAssembly.key 612).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 400) := by
    have ha : gramCharges (GramAssembly.key 612).leftCharge (GramAssembly.key 612).rightCharge = raw40060 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40060Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40060 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 612).leftCharge (GramAssembly.key 612).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow612, Integer.Sparse.eval]

theorem keyMoment613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 613) =
      Integer.Sparse.eval keyMomentRow613 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 613).leftCharge (GramAssembly.key 613).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 362) := by
    have ha : gramCharges (GramAssembly.key 613).leftCharge (GramAssembly.key 613).rightCharge = raw40061 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40061Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40061 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 613).leftCharge (GramAssembly.key 613).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow613, Integer.Sparse.eval]

theorem keyMoment614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 614) =
      Integer.Sparse.eval keyMomentRow614 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 614).leftCharge (GramAssembly.key 614).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 359) := by
    have ha : gramCharges (GramAssembly.key 614).leftCharge (GramAssembly.key 614).rightCharge = raw40062 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40062Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40062 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 614).leftCharge (GramAssembly.key 614).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow614, Integer.Sparse.eval]

theorem keyMoment615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 615) =
      Integer.Sparse.eval keyMomentRow615 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 615).leftCharge (GramAssembly.key 615).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 404) := by
    have ha : gramCharges (GramAssembly.key 615).leftCharge (GramAssembly.key 615).rightCharge = raw40063 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40063Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40063 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 615).leftCharge (GramAssembly.key 615).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow615, Integer.Sparse.eval]

theorem keyMoment616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 616) =
      Integer.Sparse.eval keyMomentRow616 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 616).leftCharge (GramAssembly.key 616).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 401) := by
    have ha : gramCharges (GramAssembly.key 616).leftCharge (GramAssembly.key 616).rightCharge = raw40064 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40064Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40064 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 616).leftCharge (GramAssembly.key 616).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow616, Integer.Sparse.eval]

theorem keyMoment617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 617) =
      Integer.Sparse.eval keyMomentRow617 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 617).leftCharge (GramAssembly.key 617).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 361) := by
    have ha : gramCharges (GramAssembly.key 617).leftCharge (GramAssembly.key 617).rightCharge = raw40065 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40065Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40065 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 617).leftCharge (GramAssembly.key 617).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow617, Integer.Sparse.eval]

theorem keyMoment618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 618) =
      Integer.Sparse.eval keyMomentRow618 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 618).leftCharge (GramAssembly.key 618).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 378) := by
    have ha : gramCharges (GramAssembly.key 618).leftCharge (GramAssembly.key 618).rightCharge = raw40066 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40066Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40066 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 618).leftCharge (GramAssembly.key 618).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow618, Integer.Sparse.eval]

theorem keyMoment619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 619) =
      Integer.Sparse.eval keyMomentRow619 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 619).leftCharge (GramAssembly.key 619).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 403) := by
    have ha : gramCharges (GramAssembly.key 619).leftCharge (GramAssembly.key 619).rightCharge = raw40067 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40067Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40067 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 619).leftCharge (GramAssembly.key 619).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow619, Integer.Sparse.eval]

theorem keyMoment620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 620) =
      Integer.Sparse.eval keyMomentRow620 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 620).leftCharge (GramAssembly.key 620).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 620).leftCharge (GramAssembly.key 620).rightCharge = raw40068 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40068Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40068 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 620).leftCharge (GramAssembly.key 620).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow620, Integer.Sparse.eval]

theorem keyMoment621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 621) =
      Integer.Sparse.eval keyMomentRow621 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 621).leftCharge (GramAssembly.key 621).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 360) := by
    have ha : gramCharges (GramAssembly.key 621).leftCharge (GramAssembly.key 621).rightCharge = raw40069 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40069Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40069 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 621).leftCharge (GramAssembly.key 621).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow621, Integer.Sparse.eval]

theorem keyMoment622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 622) =
      Integer.Sparse.eval keyMomentRow622 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 622).leftCharge (GramAssembly.key 622).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 376) := by
    have ha : gramCharges (GramAssembly.key 622).leftCharge (GramAssembly.key 622).rightCharge = raw40070 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40070Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40070 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 622).leftCharge (GramAssembly.key 622).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow622, Integer.Sparse.eval]

theorem keyMoment623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 623) =
      Integer.Sparse.eval keyMomentRow623 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 623).leftCharge (GramAssembly.key 623).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 367) := by
    have ha : gramCharges (GramAssembly.key 623).leftCharge (GramAssembly.key 623).rightCharge = raw40071 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40071Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40071 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 623).leftCharge (GramAssembly.key 623).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow623, Integer.Sparse.eval]

theorem keyMoment624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 624) =
      Integer.Sparse.eval keyMomentRow624 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 624).leftCharge (GramAssembly.key 624).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 624).leftCharge (GramAssembly.key 624).rightCharge = raw40072 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40072Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40072 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 624).leftCharge (GramAssembly.key 624).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow624, Integer.Sparse.eval]

theorem keyMoment625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 625) =
      Integer.Sparse.eval keyMomentRow625 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 625).leftCharge (GramAssembly.key 625).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 414) := by
    have ha : gramCharges (GramAssembly.key 625).leftCharge (GramAssembly.key 625).rightCharge = raw40073 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40073Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40073 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 625).leftCharge (GramAssembly.key 625).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow625, Integer.Sparse.eval]

theorem keyMoment626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 626) =
      Integer.Sparse.eval keyMomentRow626 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 626).leftCharge (GramAssembly.key 626).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 369) := by
    have ha : gramCharges (GramAssembly.key 626).leftCharge (GramAssembly.key 626).rightCharge = raw40074 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40074Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40074 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 626).leftCharge (GramAssembly.key 626).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow626, Integer.Sparse.eval]

theorem keyMoment627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 627) =
      Integer.Sparse.eval keyMomentRow627 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 627).leftCharge (GramAssembly.key 627).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 390) := by
    have ha : gramCharges (GramAssembly.key 627).leftCharge (GramAssembly.key 627).rightCharge = raw40075 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40075Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40075 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 627).leftCharge (GramAssembly.key 627).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow627, Integer.Sparse.eval]

theorem keyMoment628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 628) =
      Integer.Sparse.eval keyMomentRow628 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 628).leftCharge (GramAssembly.key 628).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 416) := by
    have ha : gramCharges (GramAssembly.key 628).leftCharge (GramAssembly.key 628).rightCharge = raw40076 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40076Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40076 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 628).leftCharge (GramAssembly.key 628).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow628, Integer.Sparse.eval]

theorem keyMoment629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 629) =
      Integer.Sparse.eval keyMomentRow629 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 629).leftCharge (GramAssembly.key 629).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 368) := by
    have ha : gramCharges (GramAssembly.key 629).leftCharge (GramAssembly.key 629).rightCharge = raw40077 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40077Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40077 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 629).leftCharge (GramAssembly.key 629).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow629, Integer.Sparse.eval]

theorem keyMoment630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 630) =
      Integer.Sparse.eval keyMomentRow630 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 630).leftCharge (GramAssembly.key 630).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 630).leftCharge (GramAssembly.key 630).rightCharge = raw40078 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40078Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40078 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 630).leftCharge (GramAssembly.key 630).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow630, Integer.Sparse.eval]

theorem keyMoment631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 631) =
      Integer.Sparse.eval keyMomentRow631 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 631).leftCharge (GramAssembly.key 631).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 371) := by
    have ha : gramCharges (GramAssembly.key 631).leftCharge (GramAssembly.key 631).rightCharge = raw40079 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40079Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40079 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 631).leftCharge (GramAssembly.key 631).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow631, Integer.Sparse.eval]

theorem keyMoment632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 632) =
      Integer.Sparse.eval keyMomentRow632 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 632).leftCharge (GramAssembly.key 632).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 415) := by
    have ha : gramCharges (GramAssembly.key 632).leftCharge (GramAssembly.key 632).rightCharge = raw40080 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40080Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40080 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 632).leftCharge (GramAssembly.key 632).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow632, Integer.Sparse.eval]

theorem keyMoment633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 633) =
      Integer.Sparse.eval keyMomentRow633 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 633).leftCharge (GramAssembly.key 633).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 316) := by
    have ha : gramCharges (GramAssembly.key 633).leftCharge (GramAssembly.key 633).rightCharge = raw40081 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40081Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40081 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 633).leftCharge (GramAssembly.key 633).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow633, Integer.Sparse.eval]

theorem keyMoment634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 634) =
      Integer.Sparse.eval keyMomentRow634 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 634).leftCharge (GramAssembly.key 634).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 388) := by
    have ha : gramCharges (GramAssembly.key 634).leftCharge (GramAssembly.key 634).rightCharge = raw40082 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40082Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40082 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 634).leftCharge (GramAssembly.key 634).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow634, Integer.Sparse.eval]

theorem keyMoment635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 635) =
      Integer.Sparse.eval keyMomentRow635 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 635).leftCharge (GramAssembly.key 635).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 113) := by
    have ha : gramCharges (GramAssembly.key 635).leftCharge (GramAssembly.key 635).rightCharge = raw40083 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40083Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40083 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 635).leftCharge (GramAssembly.key 635).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow635, Integer.Sparse.eval]

theorem keyMoment636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 636) =
      Integer.Sparse.eval keyMomentRow636 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 636).leftCharge (GramAssembly.key 636).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 4) := by
    have ha : gramCharges (GramAssembly.key 636).leftCharge (GramAssembly.key 636).rightCharge = raw40084 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40084Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40084 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 636).leftCharge (GramAssembly.key 636).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow636, Integer.Sparse.eval]

theorem keyMoment637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 637) =
      Integer.Sparse.eval keyMomentRow637 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 637).leftCharge (GramAssembly.key 637).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 637).leftCharge (GramAssembly.key 637).rightCharge = raw40085 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40085Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40085 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 637).leftCharge (GramAssembly.key 637).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow637, Integer.Sparse.eval]

theorem keyMoment638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 638) =
      Integer.Sparse.eval keyMomentRow638 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 638).leftCharge (GramAssembly.key 638).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 521) := by
    have ha : gramCharges (GramAssembly.key 638).leftCharge (GramAssembly.key 638).rightCharge = raw40086 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40086Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40086 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 638).leftCharge (GramAssembly.key 638).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow638, Integer.Sparse.eval]

theorem keyMoment639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 639) =
      Integer.Sparse.eval keyMomentRow639 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 639).leftCharge (GramAssembly.key 639).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 518) := by
    have ha : gramCharges (GramAssembly.key 639).leftCharge (GramAssembly.key 639).rightCharge = raw40087 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40087Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40087 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 639).leftCharge (GramAssembly.key 639).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow639, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

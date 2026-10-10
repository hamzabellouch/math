import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical313

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 640) =
      Integer.Sparse.eval keyMomentRow640 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 640).leftCharge (GramAssembly.key 640).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 640).leftCharge (GramAssembly.key 640).rightCharge = raw40088 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40088Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40088 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 640).leftCharge (GramAssembly.key 640).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow640, Integer.Sparse.eval]

theorem keyMoment641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 641) =
      Integer.Sparse.eval keyMomentRow641 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 641).leftCharge (GramAssembly.key 641).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 5) := by
    have ha : gramCharges (GramAssembly.key 641).leftCharge (GramAssembly.key 641).rightCharge = raw40089 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40089Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40089 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 641).leftCharge (GramAssembly.key 641).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow641, Integer.Sparse.eval]

theorem keyMoment642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 642) =
      Integer.Sparse.eval keyMomentRow642 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 642).leftCharge (GramAssembly.key 642).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 528) := by
    have ha : gramCharges (GramAssembly.key 642).leftCharge (GramAssembly.key 642).rightCharge = raw40090 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40090Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40090 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 642).leftCharge (GramAssembly.key 642).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow642, Integer.Sparse.eval]

theorem keyMoment643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 643) =
      Integer.Sparse.eval keyMomentRow643 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 643).leftCharge (GramAssembly.key 643).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 643).leftCharge (GramAssembly.key 643).rightCharge = raw40091 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40091Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40091 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 643).leftCharge (GramAssembly.key 643).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow643, Integer.Sparse.eval]

theorem keyMoment644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 644) =
      Integer.Sparse.eval keyMomentRow644 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 644).leftCharge (GramAssembly.key 644).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 502) := by
    have ha : gramCharges (GramAssembly.key 644).leftCharge (GramAssembly.key 644).rightCharge = raw40092 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40092Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40092 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 644).leftCharge (GramAssembly.key 644).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow644, Integer.Sparse.eval]

theorem keyMoment645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 645) =
      Integer.Sparse.eval keyMomentRow645 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 645).leftCharge (GramAssembly.key 645).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 514) := by
    have ha : gramCharges (GramAssembly.key 645).leftCharge (GramAssembly.key 645).rightCharge = raw40093 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40093Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40093 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 645).leftCharge (GramAssembly.key 645).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow645, Integer.Sparse.eval]

theorem keyMoment646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 646) =
      Integer.Sparse.eval keyMomentRow646 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 646).leftCharge (GramAssembly.key 646).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 646).leftCharge (GramAssembly.key 646).rightCharge = raw40094 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40094Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40094 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 646).leftCharge (GramAssembly.key 646).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow646, Integer.Sparse.eval]

theorem keyMoment647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 647) =
      Integer.Sparse.eval keyMomentRow647 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 647).leftCharge (GramAssembly.key 647).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 438) := by
    have ha : gramCharges (GramAssembly.key 647).leftCharge (GramAssembly.key 647).rightCharge = raw40095 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40095Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40095 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 647).leftCharge (GramAssembly.key 647).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow647, Integer.Sparse.eval]

theorem keyMoment648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 648) =
      Integer.Sparse.eval keyMomentRow648 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 648).leftCharge (GramAssembly.key 648).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 514) := by
    have ha : gramCharges (GramAssembly.key 648).leftCharge (GramAssembly.key 648).rightCharge = raw40096 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40096Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40096 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 648).leftCharge (GramAssembly.key 648).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow648, Integer.Sparse.eval]

theorem keyMoment649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 649) =
      Integer.Sparse.eval keyMomentRow649 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 649).leftCharge (GramAssembly.key 649).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 436) := by
    have ha : gramCharges (GramAssembly.key 649).leftCharge (GramAssembly.key 649).rightCharge = raw40097 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40097Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40097 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 649).leftCharge (GramAssembly.key 649).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow649, Integer.Sparse.eval]

theorem keyMoment650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 650) =
      Integer.Sparse.eval keyMomentRow650 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 650).leftCharge (GramAssembly.key 650).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 530) := by
    have ha : gramCharges (GramAssembly.key 650).leftCharge (GramAssembly.key 650).rightCharge = raw40098 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40098Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40098 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 650).leftCharge (GramAssembly.key 650).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow650, Integer.Sparse.eval]

theorem keyMoment651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 651) =
      Integer.Sparse.eval keyMomentRow651 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 651).leftCharge (GramAssembly.key 651).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 651).leftCharge (GramAssembly.key 651).rightCharge = raw40099 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40099Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40099 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 651).leftCharge (GramAssembly.key 651).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow651, Integer.Sparse.eval]

theorem keyMoment652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 652) =
      Integer.Sparse.eval keyMomentRow652 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 652).leftCharge (GramAssembly.key 652).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 355) := by
    have ha : gramCharges (GramAssembly.key 652).leftCharge (GramAssembly.key 652).rightCharge = raw40100 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40100Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40100 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 652).leftCharge (GramAssembly.key 652).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow652, Integer.Sparse.eval]

theorem keyMoment653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 653) =
      Integer.Sparse.eval keyMomentRow653 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 653).leftCharge (GramAssembly.key 653).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 516) := by
    have ha : gramCharges (GramAssembly.key 653).leftCharge (GramAssembly.key 653).rightCharge = raw40101 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40101Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40101 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 653).leftCharge (GramAssembly.key 653).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow653, Integer.Sparse.eval]

theorem keyMoment654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 654) =
      Integer.Sparse.eval keyMomentRow654 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 654).leftCharge (GramAssembly.key 654).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 437) := by
    have ha : gramCharges (GramAssembly.key 654).leftCharge (GramAssembly.key 654).rightCharge = raw40102 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40102Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40102 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 654).leftCharge (GramAssembly.key 654).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow654, Integer.Sparse.eval]

theorem keyMoment655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 655) =
      Integer.Sparse.eval keyMomentRow655 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 655).leftCharge (GramAssembly.key 655).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 655).leftCharge (GramAssembly.key 655).rightCharge = raw40103 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40103Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40103 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 655).leftCharge (GramAssembly.key 655).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow655, Integer.Sparse.eval]

theorem keyMoment656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 656) =
      Integer.Sparse.eval keyMomentRow656 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 656).leftCharge (GramAssembly.key 656).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 310) := by
    have ha : gramCharges (GramAssembly.key 656).leftCharge (GramAssembly.key 656).rightCharge = raw40104 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40104Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40104 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 656).leftCharge (GramAssembly.key 656).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow656, Integer.Sparse.eval]

theorem keyMoment657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 657) =
      Integer.Sparse.eval keyMomentRow657 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 657).leftCharge (GramAssembly.key 657).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 657).leftCharge (GramAssembly.key 657).rightCharge = raw40105 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40105Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40105 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 657).leftCharge (GramAssembly.key 657).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow657, Integer.Sparse.eval]

theorem keyMoment658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 658) =
      Integer.Sparse.eval keyMomentRow658 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 658).leftCharge (GramAssembly.key 658).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 390) := by
    have ha : gramCharges (GramAssembly.key 658).leftCharge (GramAssembly.key 658).rightCharge = raw40106 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40106Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40106 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 658).leftCharge (GramAssembly.key 658).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow658, Integer.Sparse.eval]

theorem keyMoment659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 659) =
      Integer.Sparse.eval keyMomentRow659 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 659).leftCharge (GramAssembly.key 659).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 312) := by
    have ha : gramCharges (GramAssembly.key 659).leftCharge (GramAssembly.key 659).rightCharge = raw40107 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40107Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40107 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 659).leftCharge (GramAssembly.key 659).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow659, Integer.Sparse.eval]

theorem keyMoment660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 660) =
      Integer.Sparse.eval keyMomentRow660 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 660).leftCharge (GramAssembly.key 660).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 111) := by
    have ha : gramCharges (GramAssembly.key 660).leftCharge (GramAssembly.key 660).rightCharge = raw40108 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40108Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40108 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 660).leftCharge (GramAssembly.key 660).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow660, Integer.Sparse.eval]

theorem keyMoment661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 661) =
      Integer.Sparse.eval keyMomentRow661 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 661).leftCharge (GramAssembly.key 661).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 112) := by
    have ha : gramCharges (GramAssembly.key 661).leftCharge (GramAssembly.key 661).rightCharge = raw40109 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40109Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40109 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 661).leftCharge (GramAssembly.key 661).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow661, Integer.Sparse.eval]

theorem keyMoment662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 662) =
      Integer.Sparse.eval keyMomentRow662 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 662).leftCharge (GramAssembly.key 662).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 0) := by
    have ha : gramCharges (GramAssembly.key 662).leftCharge (GramAssembly.key 662).rightCharge = raw40110 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40110Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40110 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 662).leftCharge (GramAssembly.key 662).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow662, Integer.Sparse.eval]

theorem keyMoment663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 663) =
      Integer.Sparse.eval keyMomentRow663 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 663).leftCharge (GramAssembly.key 663).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 3) := by
    have ha : gramCharges (GramAssembly.key 663).leftCharge (GramAssembly.key 663).rightCharge = raw40111 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40111Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40111 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 663).leftCharge (GramAssembly.key 663).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow663, Integer.Sparse.eval]

theorem keyMoment664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 664) =
      Integer.Sparse.eval keyMomentRow664 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 664).leftCharge (GramAssembly.key 664).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 411) := by
    have ha : gramCharges (GramAssembly.key 664).leftCharge (GramAssembly.key 664).rightCharge = raw40112 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40112Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40112 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 664).leftCharge (GramAssembly.key 664).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow664, Integer.Sparse.eval]

theorem keyMoment665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 665) =
      Integer.Sparse.eval keyMomentRow665 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 665).leftCharge (GramAssembly.key 665).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 492) := by
    have ha : gramCharges (GramAssembly.key 665).leftCharge (GramAssembly.key 665).rightCharge = raw40113 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40113Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40113 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 665).leftCharge (GramAssembly.key 665).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow665, Integer.Sparse.eval]

theorem keyMoment666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 666) =
      Integer.Sparse.eval keyMomentRow666 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 666).leftCharge (GramAssembly.key 666).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 265) := by
    have ha : gramCharges (GramAssembly.key 666).leftCharge (GramAssembly.key 666).rightCharge = raw40114 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40114Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40114 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 666).leftCharge (GramAssembly.key 666).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow666, Integer.Sparse.eval]

theorem keyMoment667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 667) =
      Integer.Sparse.eval keyMomentRow667 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 667).leftCharge (GramAssembly.key 667).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 464) := by
    have ha : gramCharges (GramAssembly.key 667).leftCharge (GramAssembly.key 667).rightCharge = raw40115 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40115Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40115 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 667).leftCharge (GramAssembly.key 667).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow667, Integer.Sparse.eval]

theorem keyMoment668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 668) =
      Integer.Sparse.eval keyMomentRow668 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 668).leftCharge (GramAssembly.key 668).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 382) := by
    have ha : gramCharges (GramAssembly.key 668).leftCharge (GramAssembly.key 668).rightCharge = raw40116 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40116Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40116 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 668).leftCharge (GramAssembly.key 668).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow668, Integer.Sparse.eval]

theorem keyMoment669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 669) =
      Integer.Sparse.eval keyMomentRow669 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 669).leftCharge (GramAssembly.key 669).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 7) := by
    have ha : gramCharges (GramAssembly.key 669).leftCharge (GramAssembly.key 669).rightCharge = raw40117 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40117Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40117 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 669).leftCharge (GramAssembly.key 669).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow669, Integer.Sparse.eval]

theorem keyMoment670 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 670) =
      Integer.Sparse.eval keyMomentRow670 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 670).leftCharge (GramAssembly.key 670).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 386) := by
    have ha : gramCharges (GramAssembly.key 670).leftCharge (GramAssembly.key 670).rightCharge = raw40118 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40118Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40118 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 670).leftCharge (GramAssembly.key 670).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow670, Integer.Sparse.eval]

theorem keyMoment671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 671) =
      Integer.Sparse.eval keyMomentRow671 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 671).leftCharge (GramAssembly.key 671).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 488) := by
    have ha : gramCharges (GramAssembly.key 671).leftCharge (GramAssembly.key 671).rightCharge = raw40119 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40119Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40119 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 671).leftCharge (GramAssembly.key 671).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow671, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

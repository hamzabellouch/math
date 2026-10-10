import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical312

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 544) =
      Integer.Sparse.eval keyMomentRow544 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 544).leftCharge (GramAssembly.key 544).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 224) := by
    have ha : gramCharges (GramAssembly.key 544).leftCharge (GramAssembly.key 544).rightCharge = raw39992 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39992Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39992 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 544).leftCharge (GramAssembly.key 544).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow544, Integer.Sparse.eval]

theorem keyMoment545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 545) =
      Integer.Sparse.eval keyMomentRow545 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 545).leftCharge (GramAssembly.key 545).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 211) := by
    have ha : gramCharges (GramAssembly.key 545).leftCharge (GramAssembly.key 545).rightCharge = raw39993 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39993Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39993 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 545).leftCharge (GramAssembly.key 545).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow545, Integer.Sparse.eval]

theorem keyMoment546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 546) =
      Integer.Sparse.eval keyMomentRow546 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 546).leftCharge (GramAssembly.key 546).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 207) := by
    have ha : gramCharges (GramAssembly.key 546).leftCharge (GramAssembly.key 546).rightCharge = raw39994 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39994Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39994 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 546).leftCharge (GramAssembly.key 546).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow546, Integer.Sparse.eval]

theorem keyMoment547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 547) =
      Integer.Sparse.eval keyMomentRow547 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 547).leftCharge (GramAssembly.key 547).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 547).leftCharge (GramAssembly.key 547).rightCharge = raw39995 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39995Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39995 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 547).leftCharge (GramAssembly.key 547).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow547, Integer.Sparse.eval]

theorem keyMoment548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 548) =
      Integer.Sparse.eval keyMomentRow548 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 548).leftCharge (GramAssembly.key 548).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 286) := by
    have ha : gramCharges (GramAssembly.key 548).leftCharge (GramAssembly.key 548).rightCharge = raw39996 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39996Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39996 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 548).leftCharge (GramAssembly.key 548).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow548, Integer.Sparse.eval]

theorem keyMoment549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 549) =
      Integer.Sparse.eval keyMomentRow549 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 549).leftCharge (GramAssembly.key 549).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 353) := by
    have ha : gramCharges (GramAssembly.key 549).leftCharge (GramAssembly.key 549).rightCharge = raw39997 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39997Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39997 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 549).leftCharge (GramAssembly.key 549).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow549, Integer.Sparse.eval]

theorem keyMoment550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 550) =
      Integer.Sparse.eval keyMomentRow550 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 550).leftCharge (GramAssembly.key 550).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 290) := by
    have ha : gramCharges (GramAssembly.key 550).leftCharge (GramAssembly.key 550).rightCharge = raw39998 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39998Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39998 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 550).leftCharge (GramAssembly.key 550).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow550, Integer.Sparse.eval]

theorem keyMoment551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 551) =
      Integer.Sparse.eval keyMomentRow551 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 551).leftCharge (GramAssembly.key 551).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 355) := by
    have ha : gramCharges (GramAssembly.key 551).leftCharge (GramAssembly.key 551).rightCharge = raw39999 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39999Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39999 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 551).leftCharge (GramAssembly.key 551).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow551, Integer.Sparse.eval]

theorem keyMoment552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 552) =
      Integer.Sparse.eval keyMomentRow552 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 552).leftCharge (GramAssembly.key 552).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 552).leftCharge (GramAssembly.key 552).rightCharge = raw40000 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40000Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40000 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 552).leftCharge (GramAssembly.key 552).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow552, Integer.Sparse.eval]

theorem keyMoment553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 553) =
      Integer.Sparse.eval keyMomentRow553 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 553).leftCharge (GramAssembly.key 553).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 339) := by
    have ha : gramCharges (GramAssembly.key 553).leftCharge (GramAssembly.key 553).rightCharge = raw40001 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40001Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40001 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 553).leftCharge (GramAssembly.key 553).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow553, Integer.Sparse.eval]

theorem keyMoment554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 554) =
      Integer.Sparse.eval keyMomentRow554 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 554).leftCharge (GramAssembly.key 554).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 351) := by
    have ha : gramCharges (GramAssembly.key 554).leftCharge (GramAssembly.key 554).rightCharge = raw40002 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40002Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40002 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 554).leftCharge (GramAssembly.key 554).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow554, Integer.Sparse.eval]

theorem keyMoment555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 555) =
      Integer.Sparse.eval keyMomentRow555 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 555).leftCharge (GramAssembly.key 555).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 352) := by
    have ha : gramCharges (GramAssembly.key 555).leftCharge (GramAssembly.key 555).rightCharge = raw40003 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40003Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40003 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 555).leftCharge (GramAssembly.key 555).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow555, Integer.Sparse.eval]

theorem keyMoment556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 556) =
      Integer.Sparse.eval keyMomentRow556 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 556).leftCharge (GramAssembly.key 556).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 334) := by
    have ha : gramCharges (GramAssembly.key 556).leftCharge (GramAssembly.key 556).rightCharge = raw40004 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40004Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40004 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 556).leftCharge (GramAssembly.key 556).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow556, Integer.Sparse.eval]

theorem keyMoment557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 557) =
      Integer.Sparse.eval keyMomentRow557 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 557).leftCharge (GramAssembly.key 557).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 283) := by
    have ha : gramCharges (GramAssembly.key 557).leftCharge (GramAssembly.key 557).rightCharge = raw40005 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40005Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40005 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 557).leftCharge (GramAssembly.key 557).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow557, Integer.Sparse.eval]

theorem keyMoment558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 558) =
      Integer.Sparse.eval keyMomentRow558 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 558).leftCharge (GramAssembly.key 558).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 133) := by
    have ha : gramCharges (GramAssembly.key 558).leftCharge (GramAssembly.key 558).rightCharge = raw40006 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40006Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40006 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 558).leftCharge (GramAssembly.key 558).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow558, Integer.Sparse.eval]

theorem keyMoment559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 559) =
      Integer.Sparse.eval keyMomentRow559 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 559).leftCharge (GramAssembly.key 559).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 336) := by
    have ha : gramCharges (GramAssembly.key 559).leftCharge (GramAssembly.key 559).rightCharge = raw40007 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40007Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40007 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 559).leftCharge (GramAssembly.key 559).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow559, Integer.Sparse.eval]

theorem keyMoment560 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 560) =
      Integer.Sparse.eval keyMomentRow560 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 560).leftCharge (GramAssembly.key 560).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 287) := by
    have ha : gramCharges (GramAssembly.key 560).leftCharge (GramAssembly.key 560).rightCharge = raw40008 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40008Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40008 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 560).leftCharge (GramAssembly.key 560).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow560, Integer.Sparse.eval]

theorem keyMoment561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 561) =
      Integer.Sparse.eval keyMomentRow561 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 561).leftCharge (GramAssembly.key 561).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 40) := by
    have ha : gramCharges (GramAssembly.key 561).leftCharge (GramAssembly.key 561).rightCharge = raw40009 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40009Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40009 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 561).leftCharge (GramAssembly.key 561).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow561, Integer.Sparse.eval]

theorem keyMoment562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 562) =
      Integer.Sparse.eval keyMomentRow562 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 562).leftCharge (GramAssembly.key 562).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 112) := by
    have ha : gramCharges (GramAssembly.key 562).leftCharge (GramAssembly.key 562).rightCharge = raw40010 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40010Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40010 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 562).leftCharge (GramAssembly.key 562).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow562, Integer.Sparse.eval]

theorem keyMoment563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 563) =
      Integer.Sparse.eval keyMomentRow563 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 563).leftCharge (GramAssembly.key 563).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 407) := by
    have ha : gramCharges (GramAssembly.key 563).leftCharge (GramAssembly.key 563).rightCharge = raw40011 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40011Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40011 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 563).leftCharge (GramAssembly.key 563).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow563, Integer.Sparse.eval]

theorem keyMoment564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 564) =
      Integer.Sparse.eval keyMomentRow564 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 564).leftCharge (GramAssembly.key 564).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 96) := by
    have ha : gramCharges (GramAssembly.key 564).leftCharge (GramAssembly.key 564).rightCharge = raw40012 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40012Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40012 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 564).leftCharge (GramAssembly.key 564).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow564, Integer.Sparse.eval]

theorem keyMoment565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 565) =
      Integer.Sparse.eval keyMomentRow565 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 565).leftCharge (GramAssembly.key 565).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 341) := by
    have ha : gramCharges (GramAssembly.key 565).leftCharge (GramAssembly.key 565).rightCharge = raw40013 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40013Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40013 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 565).leftCharge (GramAssembly.key 565).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow565, Integer.Sparse.eval]

theorem keyMoment566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 566) =
      Integer.Sparse.eval keyMomentRow566 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 566).leftCharge (GramAssembly.key 566).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 344) := by
    have ha : gramCharges (GramAssembly.key 566).leftCharge (GramAssembly.key 566).rightCharge = raw40014 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40014Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40014 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 566).leftCharge (GramAssembly.key 566).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow566, Integer.Sparse.eval]

theorem keyMoment567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 567) =
      Integer.Sparse.eval keyMomentRow567 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 567).leftCharge (GramAssembly.key 567).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 72) := by
    have ha : gramCharges (GramAssembly.key 567).leftCharge (GramAssembly.key 567).rightCharge = raw40015 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40015Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40015 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 567).leftCharge (GramAssembly.key 567).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow567, Integer.Sparse.eval]

theorem keyMoment568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 568) =
      Integer.Sparse.eval keyMomentRow568 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 568).leftCharge (GramAssembly.key 568).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 66) := by
    have ha : gramCharges (GramAssembly.key 568).leftCharge (GramAssembly.key 568).rightCharge = raw40016 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40016Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40016 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 568).leftCharge (GramAssembly.key 568).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow568, Integer.Sparse.eval]

theorem keyMoment569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 569) =
      Integer.Sparse.eval keyMomentRow569 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 569).leftCharge (GramAssembly.key 569).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 148) := by
    have ha : gramCharges (GramAssembly.key 569).leftCharge (GramAssembly.key 569).rightCharge = raw40017 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40017Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40017 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 569).leftCharge (GramAssembly.key 569).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow569, Integer.Sparse.eval]

theorem keyMoment570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 570) =
      Integer.Sparse.eval keyMomentRow570 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 570).leftCharge (GramAssembly.key 570).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 145) := by
    have ha : gramCharges (GramAssembly.key 570).leftCharge (GramAssembly.key 570).rightCharge = raw40018 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40018Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40018 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 570).leftCharge (GramAssembly.key 570).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow570, Integer.Sparse.eval]

theorem keyMoment571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 571) =
      Integer.Sparse.eval keyMomentRow571 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 571).leftCharge (GramAssembly.key 571).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 147) := by
    have ha : gramCharges (GramAssembly.key 571).leftCharge (GramAssembly.key 571).rightCharge = raw40019 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40019Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40019 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 571).leftCharge (GramAssembly.key 571).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow571, Integer.Sparse.eval]

theorem keyMoment572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 572) =
      Integer.Sparse.eval keyMomentRow572 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 572).leftCharge (GramAssembly.key 572).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 139) := by
    have ha : gramCharges (GramAssembly.key 572).leftCharge (GramAssembly.key 572).rightCharge = raw40020 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40020Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40020 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 572).leftCharge (GramAssembly.key 572).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow572, Integer.Sparse.eval]

theorem keyMoment573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 573) =
      Integer.Sparse.eval keyMomentRow573 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 573).leftCharge (GramAssembly.key 573).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 140) := by
    have ha : gramCharges (GramAssembly.key 573).leftCharge (GramAssembly.key 573).rightCharge = raw40021 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40021Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40021 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 573).leftCharge (GramAssembly.key 573).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow573, Integer.Sparse.eval]

theorem keyMoment574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 574) =
      Integer.Sparse.eval keyMomentRow574 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 574).leftCharge (GramAssembly.key 574).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 117) := by
    have ha : gramCharges (GramAssembly.key 574).leftCharge (GramAssembly.key 574).rightCharge = raw40022 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40022Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40022 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 574).leftCharge (GramAssembly.key 574).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow574, Integer.Sparse.eval]

theorem keyMoment575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 575) =
      Integer.Sparse.eval keyMomentRow575 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 575).leftCharge (GramAssembly.key 575).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 114) := by
    have ha : gramCharges (GramAssembly.key 575).leftCharge (GramAssembly.key 575).rightCharge = raw40023 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40023Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40023 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 575).leftCharge (GramAssembly.key 575).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow575, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

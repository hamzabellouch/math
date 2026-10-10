import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical297
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical310
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical311

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 352) =
      Integer.Sparse.eval keyMomentRow352 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 352).leftCharge (GramAssembly.key 352).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 346) := by
    have ha : gramCharges (GramAssembly.key 352).leftCharge (GramAssembly.key 352).rightCharge = raw39801 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39801Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39801 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 352).leftCharge (GramAssembly.key 352).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow352, Integer.Sparse.eval]

theorem keyMoment353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 353) =
      Integer.Sparse.eval keyMomentRow353 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 353).leftCharge (GramAssembly.key 353).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 476) := by
    have ha : gramCharges (GramAssembly.key 353).leftCharge (GramAssembly.key 353).rightCharge = raw39802 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39802Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39802 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 353).leftCharge (GramAssembly.key 353).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow353, Integer.Sparse.eval]

theorem keyMoment354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 354) =
      Integer.Sparse.eval keyMomentRow354 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 354).leftCharge (GramAssembly.key 354).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 484) := by
    have ha : gramCharges (GramAssembly.key 354).leftCharge (GramAssembly.key 354).rightCharge = raw39803 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39803Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39803 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 354).leftCharge (GramAssembly.key 354).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow354, Integer.Sparse.eval]

theorem keyMoment355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 355) =
      Integer.Sparse.eval keyMomentRow355 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 355).leftCharge (GramAssembly.key 355).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 269) := by
    have ha : gramCharges (GramAssembly.key 355).leftCharge (GramAssembly.key 355).rightCharge = raw39804 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39804Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39804 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 355).leftCharge (GramAssembly.key 355).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow355, Integer.Sparse.eval]

theorem keyMoment356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 356) =
      Integer.Sparse.eval keyMomentRow356 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 356).leftCharge (GramAssembly.key 356).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 356).leftCharge (GramAssembly.key 356).rightCharge = raw39805 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39805Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39805 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 356).leftCharge (GramAssembly.key 356).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow356, Integer.Sparse.eval]

theorem keyMoment357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 357) =
      Integer.Sparse.eval keyMomentRow357 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 357).leftCharge (GramAssembly.key 357).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 468) := by
    have ha : gramCharges (GramAssembly.key 357).leftCharge (GramAssembly.key 357).rightCharge = raw39806 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39806Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39806 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 357).leftCharge (GramAssembly.key 357).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow357, Integer.Sparse.eval]

theorem keyMoment358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 358) =
      Integer.Sparse.eval keyMomentRow358 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 358).leftCharge (GramAssembly.key 358).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 358).leftCharge (GramAssembly.key 358).rightCharge = raw39807 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39807Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39807 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 358).leftCharge (GramAssembly.key 358).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow358, Integer.Sparse.eval]

theorem keyMoment359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 359) =
      Integer.Sparse.eval keyMomentRow359 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 359).leftCharge (GramAssembly.key 359).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 364) := by
    have ha : gramCharges (GramAssembly.key 359).leftCharge (GramAssembly.key 359).rightCharge = raw39808 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39808Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39808 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 359).leftCharge (GramAssembly.key 359).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow359, Integer.Sparse.eval]

theorem keyMoment360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 360) =
      Integer.Sparse.eval keyMomentRow360 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 360).leftCharge (GramAssembly.key 360).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 481) := by
    have ha : gramCharges (GramAssembly.key 360).leftCharge (GramAssembly.key 360).rightCharge = raw39809 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39809Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39809 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 360).leftCharge (GramAssembly.key 360).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow360, Integer.Sparse.eval]

theorem keyMoment361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 361) =
      Integer.Sparse.eval keyMomentRow361 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 361).leftCharge (GramAssembly.key 361).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 443) := by
    have ha : gramCharges (GramAssembly.key 361).leftCharge (GramAssembly.key 361).rightCharge = raw39810 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39810Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39810 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 361).leftCharge (GramAssembly.key 361).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow361, Integer.Sparse.eval]

theorem keyMoment362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 362) =
      Integer.Sparse.eval keyMomentRow362 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 362).leftCharge (GramAssembly.key 362).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 440) := by
    have ha : gramCharges (GramAssembly.key 362).leftCharge (GramAssembly.key 362).rightCharge = raw39811 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39811Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39811 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 362).leftCharge (GramAssembly.key 362).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow362, Integer.Sparse.eval]

theorem keyMoment363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 363) =
      Integer.Sparse.eval keyMomentRow363 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 363).leftCharge (GramAssembly.key 363).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 480) := by
    have ha : gramCharges (GramAssembly.key 363).leftCharge (GramAssembly.key 363).rightCharge = raw39812 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39812Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39812 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 363).leftCharge (GramAssembly.key 363).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow363, Integer.Sparse.eval]

theorem keyMoment364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 364) =
      Integer.Sparse.eval keyMomentRow364 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 364).leftCharge (GramAssembly.key 364).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 492) := by
    have ha : gramCharges (GramAssembly.key 364).leftCharge (GramAssembly.key 364).rightCharge = raw38091 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw38091Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical38091 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 364).leftCharge (GramAssembly.key 364).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow364, Integer.Sparse.eval]

theorem keyMoment365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 365) =
      Integer.Sparse.eval keyMomentRow365 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 365).leftCharge (GramAssembly.key 365).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 365).leftCharge (GramAssembly.key 365).rightCharge = raw39813 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39813Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39813 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 365).leftCharge (GramAssembly.key 365).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow365, Integer.Sparse.eval]

theorem keyMoment366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 366) =
      Integer.Sparse.eval keyMomentRow366 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 366).leftCharge (GramAssembly.key 366).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 478) := by
    have ha : gramCharges (GramAssembly.key 366).leftCharge (GramAssembly.key 366).rightCharge = raw39814 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39814Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39814 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 366).leftCharge (GramAssembly.key 366).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow366, Integer.Sparse.eval]

theorem keyMoment367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 367) =
      Integer.Sparse.eval keyMomentRow367 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 367).leftCharge (GramAssembly.key 367).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 367).leftCharge (GramAssembly.key 367).rightCharge = raw39815 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39815Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39815 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 367).leftCharge (GramAssembly.key 367).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow367, Integer.Sparse.eval]

theorem keyMoment368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 368) =
      Integer.Sparse.eval keyMomentRow368 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 368).leftCharge (GramAssembly.key 368).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 148) := by
    have ha : gramCharges (GramAssembly.key 368).leftCharge (GramAssembly.key 368).rightCharge = raw39816 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39816Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39816 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 368).leftCharge (GramAssembly.key 368).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow368, Integer.Sparse.eval]

theorem keyMoment369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 369) =
      Integer.Sparse.eval keyMomentRow369 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 369).leftCharge (GramAssembly.key 369).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 369).leftCharge (GramAssembly.key 369).rightCharge = raw39817 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39817Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39817 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 369).leftCharge (GramAssembly.key 369).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow369, Integer.Sparse.eval]

theorem keyMoment370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 370) =
      Integer.Sparse.eval keyMomentRow370 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 370).leftCharge (GramAssembly.key 370).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 370).leftCharge (GramAssembly.key 370).rightCharge = raw39818 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39818Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39818 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 370).leftCharge (GramAssembly.key 370).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow370, Integer.Sparse.eval]

theorem keyMoment371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 371) =
      Integer.Sparse.eval keyMomentRow371 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 371).leftCharge (GramAssembly.key 371).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 145) := by
    have ha : gramCharges (GramAssembly.key 371).leftCharge (GramAssembly.key 371).rightCharge = raw39819 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39819Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39819 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 371).leftCharge (GramAssembly.key 371).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow371, Integer.Sparse.eval]

theorem keyMoment372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 372) =
      Integer.Sparse.eval keyMomentRow372 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 372).leftCharge (GramAssembly.key 372).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 139) := by
    have ha : gramCharges (GramAssembly.key 372).leftCharge (GramAssembly.key 372).rightCharge = raw39820 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39820Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39820 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 372).leftCharge (GramAssembly.key 372).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow372, Integer.Sparse.eval]

theorem keyMoment373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 373) =
      Integer.Sparse.eval keyMomentRow373 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 373).leftCharge (GramAssembly.key 373).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 322) := by
    have ha : gramCharges (GramAssembly.key 373).leftCharge (GramAssembly.key 373).rightCharge = raw39821 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39821Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39821 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 373).leftCharge (GramAssembly.key 373).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow373, Integer.Sparse.eval]

theorem keyMoment374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 374) =
      Integer.Sparse.eval keyMomentRow374 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 374).leftCharge (GramAssembly.key 374).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 373) := by
    have ha : gramCharges (GramAssembly.key 374).leftCharge (GramAssembly.key 374).rightCharge = raw39822 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39822Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39822 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 374).leftCharge (GramAssembly.key 374).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow374, Integer.Sparse.eval]

theorem keyMoment375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 375) =
      Integer.Sparse.eval keyMomentRow375 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 375).leftCharge (GramAssembly.key 375).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 264) := by
    have ha : gramCharges (GramAssembly.key 375).leftCharge (GramAssembly.key 375).rightCharge = raw39823 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39823Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39823 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 375).leftCharge (GramAssembly.key 375).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow375, Integer.Sparse.eval]

theorem keyMoment376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 376) =
      Integer.Sparse.eval keyMomentRow376 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 376).leftCharge (GramAssembly.key 376).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 263) := by
    have ha : gramCharges (GramAssembly.key 376).leftCharge (GramAssembly.key 376).rightCharge = raw39824 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39824Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39824 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 376).leftCharge (GramAssembly.key 376).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow376, Integer.Sparse.eval]

theorem keyMoment377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 377) =
      Integer.Sparse.eval keyMomentRow377 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 377).leftCharge (GramAssembly.key 377).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 246) := by
    have ha : gramCharges (GramAssembly.key 377).leftCharge (GramAssembly.key 377).rightCharge = raw39825 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39825Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39825 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 377).leftCharge (GramAssembly.key 377).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow377, Integer.Sparse.eval]

theorem keyMoment378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 378) =
      Integer.Sparse.eval keyMomentRow378 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 378).leftCharge (GramAssembly.key 378).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 177) := by
    have ha : gramCharges (GramAssembly.key 378).leftCharge (GramAssembly.key 378).rightCharge = raw39826 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39826Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39826 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 378).leftCharge (GramAssembly.key 378).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow378, Integer.Sparse.eval]

theorem keyMoment379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 379) =
      Integer.Sparse.eval keyMomentRow379 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 379).leftCharge (GramAssembly.key 379).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 238) := by
    have ha : gramCharges (GramAssembly.key 379).leftCharge (GramAssembly.key 379).rightCharge = raw39827 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39827Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39827 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 379).leftCharge (GramAssembly.key 379).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow379, Integer.Sparse.eval]

theorem keyMoment380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 380) =
      Integer.Sparse.eval keyMomentRow380 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 380).leftCharge (GramAssembly.key 380).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 165) := by
    have ha : gramCharges (GramAssembly.key 380).leftCharge (GramAssembly.key 380).rightCharge = raw39828 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39828Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39828 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 380).leftCharge (GramAssembly.key 380).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow380, Integer.Sparse.eval]

theorem keyMoment381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 381) =
      Integer.Sparse.eval keyMomentRow381 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 381).leftCharge (GramAssembly.key 381).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 263) := by
    have ha : gramCharges (GramAssembly.key 381).leftCharge (GramAssembly.key 381).rightCharge = raw39829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39829 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 381).leftCharge (GramAssembly.key 381).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow381, Integer.Sparse.eval]

theorem keyMoment382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 382) =
      Integer.Sparse.eval keyMomentRow382 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 382).leftCharge (GramAssembly.key 382).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 463) := by
    have ha : gramCharges (GramAssembly.key 382).leftCharge (GramAssembly.key 382).rightCharge = raw39830 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39830Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39830 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 382).leftCharge (GramAssembly.key 382).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow382, Integer.Sparse.eval]

theorem keyMoment383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 383) =
      Integer.Sparse.eval keyMomentRow383 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 383).leftCharge (GramAssembly.key 383).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 458) := by
    have ha : gramCharges (GramAssembly.key 383).leftCharge (GramAssembly.key 383).rightCharge = raw39831 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39831Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39831 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 383).leftCharge (GramAssembly.key 383).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow383, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical331

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2528) =
      Integer.Sparse.eval keyMomentRow2528 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2678) := by
    have ha : gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge = raw42368 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42368Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42368 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5233) := by
    have ha : gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge = raw42369 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42369Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42369 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2528).leftCharge (GramAssembly.key 2528).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2528, Integer.Sparse.eval]
  ring

theorem keyMoment2529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2529) =
      Integer.Sparse.eval keyMomentRow2529 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge = raw42370 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42370Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42370 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge = raw42371 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42371Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42371 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2529).leftCharge (GramAssembly.key 2529).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2529, Integer.Sparse.eval]
  ring

theorem keyMoment2530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2530) =
      Integer.Sparse.eval keyMomentRow2530 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3871) := by
    have ha : gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge = raw42372 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42372Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42372 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge = raw42373 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42373Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42373 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2530).leftCharge (GramAssembly.key 2530).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2530, Integer.Sparse.eval]
  ring

theorem keyMoment2531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2531) =
      Integer.Sparse.eval keyMomentRow2531 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3870) := by
    have ha : gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge = raw42374 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42374Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42374 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5420) := by
    have ha : gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge = raw42375 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42375Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42375 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2531).leftCharge (GramAssembly.key 2531).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2531, Integer.Sparse.eval]
  ring

theorem keyMoment2532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2532) =
      Integer.Sparse.eval keyMomentRow2532 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3834) := by
    have ha : gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge = raw42376 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42376Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42376 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5381) := by
    have ha : gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge = raw42377 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42377Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42377 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2532).leftCharge (GramAssembly.key 2532).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2532, Integer.Sparse.eval]
  ring

theorem keyMoment2533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2533) =
      Integer.Sparse.eval keyMomentRow2533 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2662) := by
    have ha : gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge = raw42378 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42378Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42378 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5220) := by
    have ha : gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge = raw42379 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42379Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42379 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2533).leftCharge (GramAssembly.key 2533).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2533, Integer.Sparse.eval]
  ring

theorem keyMoment2534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2534) =
      Integer.Sparse.eval keyMomentRow2534 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge = raw42380 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42380Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42380 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge = raw42381 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42381Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42381 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2534).leftCharge (GramAssembly.key 2534).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2534, Integer.Sparse.eval]
  ring

theorem keyMoment2535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2535) =
      Integer.Sparse.eval keyMomentRow2535 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3882) := by
    have ha : gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge = raw42382 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42382Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42382 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5447) := by
    have ha : gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge = raw42383 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42383Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42383 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2535).leftCharge (GramAssembly.key 2535).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2535, Integer.Sparse.eval]
  ring

theorem keyMoment2536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2536) =
      Integer.Sparse.eval keyMomentRow2536 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge = raw42384 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42384Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42384 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge = raw42385 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42385Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42385 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2536).leftCharge (GramAssembly.key 2536).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2536, Integer.Sparse.eval]
  ring

theorem keyMoment2537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2537) =
      Integer.Sparse.eval keyMomentRow2537 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2687) := by
    have ha : gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge = raw42386 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42386Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42386 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5206) := by
    have ha : gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge = raw42387 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42387Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42387 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2537).leftCharge (GramAssembly.key 2537).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2537, Integer.Sparse.eval]
  ring

theorem keyMoment2538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2538) =
      Integer.Sparse.eval keyMomentRow2538 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge = raw42388 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42388Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42388 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge = raw42389 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42389Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42389 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2538).leftCharge (GramAssembly.key 2538).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2538, Integer.Sparse.eval]
  ring

theorem keyMoment2539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2539) =
      Integer.Sparse.eval keyMomentRow2539 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3570) := by
    have ha : gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge = raw42390 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42390Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42390 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5198) := by
    have ha : gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge = raw42391 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42391Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42391 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2539).leftCharge (GramAssembly.key 2539).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2539, Integer.Sparse.eval]
  ring

theorem keyMoment2540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2540) =
      Integer.Sparse.eval keyMomentRow2540 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3538) := by
    have ha : gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge = raw42392 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42392Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42392 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5188) := by
    have ha : gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge = raw42393 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42393Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42393 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2540).leftCharge (GramAssembly.key 2540).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2540, Integer.Sparse.eval]
  ring

theorem keyMoment2541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2541) =
      Integer.Sparse.eval keyMomentRow2541 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2673) := by
    have ha : gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge = raw42394 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42394Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42394 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5229) := by
    have ha : gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge = raw42395 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42395Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42395 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2541).leftCharge (GramAssembly.key 2541).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2541, Integer.Sparse.eval]
  ring

theorem keyMoment2542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2542) =
      Integer.Sparse.eval keyMomentRow2542 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge = raw42396 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42396Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42396 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge = raw42397 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42397Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42397 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2542).leftCharge (GramAssembly.key 2542).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2542, Integer.Sparse.eval]
  ring

theorem keyMoment2543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2543) =
      Integer.Sparse.eval keyMomentRow2543 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3524) := by
    have ha : gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge = raw42398 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42398Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42398 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5184) := by
    have ha : gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge = raw42399 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42399Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42399 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2543).leftCharge (GramAssembly.key 2543).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2543, Integer.Sparse.eval]
  ring

theorem keyMoment2544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2544) =
      Integer.Sparse.eval keyMomentRow2544 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3873) := by
    have ha : gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge = raw42400 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42400Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42400 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5421) := by
    have ha : gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge = raw42401 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42401Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42401 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2544).leftCharge (GramAssembly.key 2544).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2544, Integer.Sparse.eval]
  ring

theorem keyMoment2545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2545) =
      Integer.Sparse.eval keyMomentRow2545 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge = raw42402 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42402Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42402 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge = raw42403 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42403Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42403 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2545).leftCharge (GramAssembly.key 2545).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2545, Integer.Sparse.eval]
  ring

theorem keyMoment2546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2546) =
      Integer.Sparse.eval keyMomentRow2546 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3832) := by
    have ha : gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge = raw42404 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42404Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42404 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5379) := by
    have ha : gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge = raw42405 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42405Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42405 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2546).leftCharge (GramAssembly.key 2546).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2546, Integer.Sparse.eval]
  ring

theorem keyMoment2547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2547) =
      Integer.Sparse.eval keyMomentRow2547 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3224) := by
    have ha : gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge = raw42406 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42406Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42406 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4898) := by
    have ha : gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge = raw42407 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42407Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42407 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2547).leftCharge (GramAssembly.key 2547).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2547, Integer.Sparse.eval]
  ring

theorem keyMoment2548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2548) =
      Integer.Sparse.eval keyMomentRow2548 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge = raw42408 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42408Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42408 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge = raw42409 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42409Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42409 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2548).leftCharge (GramAssembly.key 2548).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2548, Integer.Sparse.eval]
  ring

theorem keyMoment2549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2549) =
      Integer.Sparse.eval keyMomentRow2549 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3856) := by
    have ha : gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge = raw42410 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42410Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42410 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5412) := by
    have ha : gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge = raw42411 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42411Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42411 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2549).leftCharge (GramAssembly.key 2549).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2549, Integer.Sparse.eval]
  ring

theorem keyMoment2550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2550) =
      Integer.Sparse.eval keyMomentRow2550 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3854) := by
    have ha : gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge = raw42412 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42412Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42412 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge = raw42413 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42413Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42413 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2550).leftCharge (GramAssembly.key 2550).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2550, Integer.Sparse.eval]
  ring

theorem keyMoment2551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2551) =
      Integer.Sparse.eval keyMomentRow2551 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2677) := by
    have ha : gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge = raw42414 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42414Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42414 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5232) := by
    have ha : gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge = raw42415 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42415Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42415 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2551).leftCharge (GramAssembly.key 2551).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2551, Integer.Sparse.eval]
  ring

theorem keyMoment2552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2552) =
      Integer.Sparse.eval keyMomentRow2552 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3841) := by
    have ha : gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge = raw42416 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42416Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42416 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5426) := by
    have ha : gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge = raw42417 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42417Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42417 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2552).leftCharge (GramAssembly.key 2552).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2552, Integer.Sparse.eval]
  ring

theorem keyMoment2553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2553) =
      Integer.Sparse.eval keyMomentRow2553 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge = raw42418 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42418Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42418 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge = raw42419 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42419Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42419 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2553).leftCharge (GramAssembly.key 2553).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2553, Integer.Sparse.eval]
  ring

theorem keyMoment2554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2554) =
      Integer.Sparse.eval keyMomentRow2554 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3834) := by
    have ha : gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge = raw42420 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42420Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42420 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5381) := by
    have ha : gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge = raw42421 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42421Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42421 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2554).leftCharge (GramAssembly.key 2554).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2554, Integer.Sparse.eval]
  ring

theorem keyMoment2555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2555) =
      Integer.Sparse.eval keyMomentRow2555 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3833) := by
    have ha : gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge = raw42422 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42422Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42422 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5376) := by
    have ha : gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge = raw42423 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42423Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42423 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2555).leftCharge (GramAssembly.key 2555).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2555, Integer.Sparse.eval]
  ring

theorem keyMoment2556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2556) =
      Integer.Sparse.eval keyMomentRow2556 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2661) := by
    have ha : gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge = raw42424 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42424Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42424 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5219) := by
    have ha : gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge = raw42425 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42425Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42425 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2556).leftCharge (GramAssembly.key 2556).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2556, Integer.Sparse.eval]
  ring

theorem keyMoment2557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2557) =
      Integer.Sparse.eval keyMomentRow2557 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge = raw42426 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42426Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42426 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge = raw42427 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42427Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42427 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2557).leftCharge (GramAssembly.key 2557).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2557, Integer.Sparse.eval]
  ring

theorem keyMoment2558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2558) =
      Integer.Sparse.eval keyMomentRow2558 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3855) := by
    have ha : gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge = raw42428 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42428Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42428 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5437) := by
    have ha : gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge = raw42429 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42429Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42429 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2558).leftCharge (GramAssembly.key 2558).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2558, Integer.Sparse.eval]
  ring

theorem keyMoment2559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2559) =
      Integer.Sparse.eval keyMomentRow2559 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3223) := by
    have ha : gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge = raw42430 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42430Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42430 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4889) := by
    have ha : gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge = raw42431 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42431Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42431 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2559).leftCharge (GramAssembly.key 2559).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2559, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

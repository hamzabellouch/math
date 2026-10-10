import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical331

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2560 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2560) =
      Integer.Sparse.eval keyMomentRow2560 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge = raw42432 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42432Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42432 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge = raw42433 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42433Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42433 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2560, Integer.Sparse.eval]
  ring

theorem keyMoment2561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2561) =
      Integer.Sparse.eval keyMomentRow2561 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3847) := by
    have ha : gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge = raw42434 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42434Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42434 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5406) := by
    have ha : gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge = raw42435 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42435Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42435 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2561, Integer.Sparse.eval]
  ring

theorem keyMoment2562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2562) =
      Integer.Sparse.eval keyMomentRow2562 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge = raw42436 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42436Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42436 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge = raw42437 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42437Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42437 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2562, Integer.Sparse.eval]
  ring

theorem keyMoment2563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2563) =
      Integer.Sparse.eval keyMomentRow2563 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2676) := by
    have ha : gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge = raw42438 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42438Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42438 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5231) := by
    have ha : gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge = raw42439 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42439Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42439 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2563, Integer.Sparse.eval]
  ring

theorem keyMoment2564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2564) =
      Integer.Sparse.eval keyMomentRow2564 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge = raw42440 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42440Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42440 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge = raw42441 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42441Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42441 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2564, Integer.Sparse.eval]
  ring

theorem keyMoment2565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2565) =
      Integer.Sparse.eval keyMomentRow2565 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2681) := by
    have ha : gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge = raw42442 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42442Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42442 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5151) := by
    have ha : gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge = raw42443 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42443Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42443 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2565, Integer.Sparse.eval]
  ring

theorem keyMoment2566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2566) =
      Integer.Sparse.eval keyMomentRow2566 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge = raw42444 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42444Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42444 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge = raw42445 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42445Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42445 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2566, Integer.Sparse.eval]
  ring

theorem keyMoment2567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2567) =
      Integer.Sparse.eval keyMomentRow2567 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3557) := by
    have ha : gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge = raw42446 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42446Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42446 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5144) := by
    have ha : gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge = raw42447 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42447Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42447 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2567, Integer.Sparse.eval]
  ring

theorem keyMoment2568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2568) =
      Integer.Sparse.eval keyMomentRow2568 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3516) := by
    have ha : gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge = raw42448 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42448Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42448 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5129) := by
    have ha : gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge = raw42449 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42449Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42449 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2568, Integer.Sparse.eval]
  ring

theorem keyMoment2569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2569) =
      Integer.Sparse.eval keyMomentRow2569 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge = raw42450 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42450Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42450 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge = raw42451 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42451Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42451 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2569, Integer.Sparse.eval]
  ring

theorem keyMoment2570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2570) =
      Integer.Sparse.eval keyMomentRow2570 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge = raw42452 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42452Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42452 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge = raw42453 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42453Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42453 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2570, Integer.Sparse.eval]
  ring

theorem keyMoment2571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2571) =
      Integer.Sparse.eval keyMomentRow2571 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2683) := by
    have ha : gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge = raw42454 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42454Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42454 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4611) := by
    have ha : gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge = raw42455 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42455Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42455 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2571, Integer.Sparse.eval]
  ring

theorem keyMoment2572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2572) =
      Integer.Sparse.eval keyMomentRow2572 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge = raw42456 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42456Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42456 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge = raw42457 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42457Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42457 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2572, Integer.Sparse.eval]
  ring

theorem keyMoment2573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2573) =
      Integer.Sparse.eval keyMomentRow2573 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3296) := by
    have ha : gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge = raw42458 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42458Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42458 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4607) := by
    have ha : gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge = raw42459 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42459Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42459 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2573, Integer.Sparse.eval]
  ring

theorem keyMoment2574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2574) =
      Integer.Sparse.eval keyMomentRow2574 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3295) := by
    have ha : gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge = raw42460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42460 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4592) := by
    have ha : gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge = raw42461 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42461Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42461 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2574, Integer.Sparse.eval]
  ring

theorem keyMoment2575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2575) =
      Integer.Sparse.eval keyMomentRow2575 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2670) := by
    have ha : gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge = raw42462 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42462Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42462 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5140) := by
    have ha : gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge = raw42463 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42463Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42463 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2575, Integer.Sparse.eval]
  ring

theorem keyMoment2576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2576) =
      Integer.Sparse.eval keyMomentRow2576 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3540) := by
    have ha : gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge = raw42464 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42464Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42464 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge = raw42465 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42465Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42465 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2576, Integer.Sparse.eval]
  ring

theorem keyMoment2577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2577) =
      Integer.Sparse.eval keyMomentRow2577 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2682) := by
    have ha : gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge = raw42466 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42466Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42466 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5236) := by
    have ha : gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge = raw42467 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42467Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42467 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2577, Integer.Sparse.eval]
  ring

theorem keyMoment2578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2578) =
      Integer.Sparse.eval keyMomentRow2578 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3288) := by
    have ha : gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge = raw42468 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42468Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42468 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4589) := by
    have ha : gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge = raw42469 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42469Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42469 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2578, Integer.Sparse.eval]
  ring

theorem keyMoment2579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2579) =
      Integer.Sparse.eval keyMomentRow2579 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3517) := by
    have ha : gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge = raw42470 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42470Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42470 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5138) := by
    have ha : gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge = raw42471 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42471Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42471 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2579, Integer.Sparse.eval]
  ring

theorem keyMoment2580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2580) =
      Integer.Sparse.eval keyMomentRow2580 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3539) := by
    have ha : gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge = raw42472 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42472Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42472 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge = raw42473 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42473Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42473 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2580, Integer.Sparse.eval]
  ring

theorem keyMoment2581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2581) =
      Integer.Sparse.eval keyMomentRow2581 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3842) := by
    have ha : gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge = raw42474 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42474Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42474 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5419) := by
    have ha : gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge = raw42475 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42475Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42475 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2581, Integer.Sparse.eval]
  ring

theorem keyMoment2582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2582) =
      Integer.Sparse.eval keyMomentRow2582 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3516) := by
    have ha : gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge = raw42476 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42476Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42476 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5129) := by
    have ha : gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge = raw42477 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42477Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42477 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2582, Integer.Sparse.eval]
  ring

theorem keyMoment2583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2583) =
      Integer.Sparse.eval keyMomentRow2583 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3835) := by
    have ha : gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge = raw42478 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42478Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42478 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5377) := by
    have ha : gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge = raw42479 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42479Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42479 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2583, Integer.Sparse.eval]
  ring

theorem keyMoment2584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2584) =
      Integer.Sparse.eval keyMomentRow2584 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2255) := by
    have ha : gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge = raw42480 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42480Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42480 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4892) := by
    have ha : gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge = raw42481 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42481Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42481 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2584, Integer.Sparse.eval]
  ring

theorem keyMoment2585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2585) =
      Integer.Sparse.eval keyMomentRow2585 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2197) := by
    have ha : gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge = raw42482 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42482Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42482 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4836) := by
    have ha : gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge = raw42483 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42483Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42483 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2585, Integer.Sparse.eval]
  ring

theorem keyMoment2586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2586) =
      Integer.Sparse.eval keyMomentRow2586 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2253) := by
    have ha : gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge = raw42484 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42484Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42484 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4891) := by
    have ha : gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge = raw42485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42485 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2586, Integer.Sparse.eval]
  ring

theorem keyMoment2587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2587) =
      Integer.Sparse.eval keyMomentRow2587 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2251) := by
    have ha : gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge = raw42486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42486 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4867) := by
    have ha : gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge = raw42487 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42487Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42487 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2587, Integer.Sparse.eval]
  ring

theorem keyMoment2588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2588) =
      Integer.Sparse.eval keyMomentRow2588 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2146) := by
    have ha : gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge = raw42488 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42488Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42488 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4683) := by
    have ha : gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge = raw42489 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42489Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42489 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2588, Integer.Sparse.eval]
  ring

theorem keyMoment2589 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2589) =
      Integer.Sparse.eval keyMomentRow2589 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2196) := by
    have ha : gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge = raw42490 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42490Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42490 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4816) := by
    have ha : gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge = raw42491 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42491Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42491 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2589, Integer.Sparse.eval]
  ring

theorem keyMoment2590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2590) =
      Integer.Sparse.eval keyMomentRow2590 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2250) := by
    have ha : gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge = raw42492 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42492Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42492 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4852) := by
    have ha : gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge = raw42493 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42493Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42493 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2590, Integer.Sparse.eval]
  ring

theorem keyMoment2591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2591) =
      Integer.Sparse.eval keyMomentRow2591 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2145) := by
    have ha : gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge = raw42494 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42494Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42494 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4680) := by
    have ha : gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge = raw42495 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42495Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42495 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2591, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

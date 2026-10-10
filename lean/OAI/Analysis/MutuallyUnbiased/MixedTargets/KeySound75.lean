import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical329

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2400) =
      Integer.Sparse.eval keyMomentRow2400 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge = raw42112 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42112Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42112 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge = raw42113 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42113Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42113 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2400).leftCharge (GramAssembly.key 2400).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2400, Integer.Sparse.eval]
  ring

theorem keyMoment2401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2401) =
      Integer.Sparse.eval keyMomentRow2401 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge = raw42114 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42114Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42114 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge = raw42115 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42115Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42115 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2401).leftCharge (GramAssembly.key 2401).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2401, Integer.Sparse.eval]
  ring

theorem keyMoment2402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2402) =
      Integer.Sparse.eval keyMomentRow2402 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge = raw42116 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42116Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42116 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge = raw42117 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42117Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42117 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2402).leftCharge (GramAssembly.key 2402).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2402, Integer.Sparse.eval]
  ring

theorem keyMoment2403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2403) =
      Integer.Sparse.eval keyMomentRow2403 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4028) := by
    have ha : gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge = raw42118 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42118Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42118 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5448) := by
    have ha : gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge = raw42119 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42119Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42119 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2403).leftCharge (GramAssembly.key 2403).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2403, Integer.Sparse.eval]
  ring

theorem keyMoment2404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2404) =
      Integer.Sparse.eval keyMomentRow2404 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4024) := by
    have ha : gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge = raw42120 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42120Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42120 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge = raw42121 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42121Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42121 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2404).leftCharge (GramAssembly.key 2404).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2404, Integer.Sparse.eval]
  ring

theorem keyMoment2405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2405) =
      Integer.Sparse.eval keyMomentRow2405 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge = raw42122 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42122Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42122 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge = raw42123 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42123Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42123 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2405).leftCharge (GramAssembly.key 2405).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2405, Integer.Sparse.eval]
  ring

theorem keyMoment2406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2406) =
      Integer.Sparse.eval keyMomentRow2406 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge = raw42124 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42124Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42124 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge = raw42125 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42125Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42125 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2406).leftCharge (GramAssembly.key 2406).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2406, Integer.Sparse.eval]
  ring

theorem keyMoment2407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2407) =
      Integer.Sparse.eval keyMomentRow2407 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3549) := by
    have ha : gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge = raw42126 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42126Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42126 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5268) := by
    have ha : gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge = raw42127 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42127Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42127 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2407).leftCharge (GramAssembly.key 2407).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2407, Integer.Sparse.eval]
  ring

theorem keyMoment2408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2408) =
      Integer.Sparse.eval keyMomentRow2408 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge = raw42128 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42128Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42128 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge = raw42129 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42129Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42129 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2408).leftCharge (GramAssembly.key 2408).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2408, Integer.Sparse.eval]
  ring

theorem keyMoment2409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2409) =
      Integer.Sparse.eval keyMomentRow2409 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3231) := by
    have ha : gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge = raw42130 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42130Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42130 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4901) := by
    have ha : gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge = raw42131 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42131Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42131 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2409).leftCharge (GramAssembly.key 2409).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2409, Integer.Sparse.eval]
  ring

theorem keyMoment2410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2410) =
      Integer.Sparse.eval keyMomentRow2410 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3110) := by
    have ha : gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge = raw42132 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42132Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42132 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5275) := by
    have ha : gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge = raw42133 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42133Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42133 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2410).leftCharge (GramAssembly.key 2410).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2410, Integer.Sparse.eval]
  ring

theorem keyMoment2411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2411) =
      Integer.Sparse.eval keyMomentRow2411 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4006) := by
    have ha : gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge = raw42134 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42134Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42134 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5413) := by
    have ha : gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge = raw42135 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42135Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42135 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2411).leftCharge (GramAssembly.key 2411).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2411, Integer.Sparse.eval]
  ring

theorem keyMoment2412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2412) =
      Integer.Sparse.eval keyMomentRow2412 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4004) := by
    have ha : gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge = raw42136 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42136Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42136 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5475) := by
    have ha : gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge = raw42137 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42137Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42137 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2412).leftCharge (GramAssembly.key 2412).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2412, Integer.Sparse.eval]
  ring

theorem keyMoment2413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2413) =
      Integer.Sparse.eval keyMomentRow2413 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge = raw42138 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42138Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42138 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge = raw42139 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42139Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42139 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2413).leftCharge (GramAssembly.key 2413).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2413, Integer.Sparse.eval]
  ring

theorem keyMoment2414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2414) =
      Integer.Sparse.eval keyMomentRow2414 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4003) := by
    have ha : gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge = raw42140 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42140Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42140 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5428) := by
    have ha : gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge = raw42141 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42141Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42141 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2414).leftCharge (GramAssembly.key 2414).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2414, Integer.Sparse.eval]
  ring

theorem keyMoment2415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2415) =
      Integer.Sparse.eval keyMomentRow2415 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3995) := by
    have ha : gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge = raw42142 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42142Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42142 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5473) := by
    have ha : gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge = raw42143 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42143Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42143 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2415).leftCharge (GramAssembly.key 2415).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2415, Integer.Sparse.eval]
  ring

theorem keyMoment2416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2416) =
      Integer.Sparse.eval keyMomentRow2416 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge = raw42144 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42144Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42144 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge = raw42145 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42145Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42145 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2416).leftCharge (GramAssembly.key 2416).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2416, Integer.Sparse.eval]
  ring

theorem keyMoment2417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2417) =
      Integer.Sparse.eval keyMomentRow2417 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3854) := by
    have ha : gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge = raw42146 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42146Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42146 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge = raw42147 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42147Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42147 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2417).leftCharge (GramAssembly.key 2417).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2417, Integer.Sparse.eval]
  ring

theorem keyMoment2418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2418) =
      Integer.Sparse.eval keyMomentRow2418 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge = raw42148 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42148Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42148 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge = raw42149 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42149Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42149 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2418).leftCharge (GramAssembly.key 2418).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2418, Integer.Sparse.eval]
  ring

theorem keyMoment2419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2419) =
      Integer.Sparse.eval keyMomentRow2419 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3995) := by
    have ha : gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge = raw42150 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42150Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42150 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5473) := by
    have ha : gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge = raw42151 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42151Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42151 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2419).leftCharge (GramAssembly.key 2419).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2419, Integer.Sparse.eval]
  ring

theorem keyMoment2420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2420) =
      Integer.Sparse.eval keyMomentRow2420 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4005) := by
    have ha : gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge = raw42152 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42152Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42152 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5474) := by
    have ha : gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge = raw42153 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42153Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42153 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2420).leftCharge (GramAssembly.key 2420).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2420, Integer.Sparse.eval]
  ring

theorem keyMoment2421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2421) =
      Integer.Sparse.eval keyMomentRow2421 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge = raw42154 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42154Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42154 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge = raw42155 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42155Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42155 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2421).leftCharge (GramAssembly.key 2421).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2421, Integer.Sparse.eval]
  ring

theorem keyMoment2422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2422) =
      Integer.Sparse.eval keyMomentRow2422 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3976) := by
    have ha : gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge = raw42156 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42156Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42156 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5471) := by
    have ha : gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge = raw42157 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42157Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42157 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2422).leftCharge (GramAssembly.key 2422).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2422, Integer.Sparse.eval]
  ring

theorem keyMoment2423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2423) =
      Integer.Sparse.eval keyMomentRow2423 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4002) := by
    have ha : gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge = raw42158 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42158Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42158 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5472) := by
    have ha : gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge = raw42159 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42159Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42159 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2423).leftCharge (GramAssembly.key 2423).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2423, Integer.Sparse.eval]
  ring

theorem keyMoment2424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2424) =
      Integer.Sparse.eval keyMomentRow2424 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge = raw42160 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42160Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42160 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge = raw42161 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42161Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42161 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2424).leftCharge (GramAssembly.key 2424).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2424, Integer.Sparse.eval]
  ring

theorem keyMoment2425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2425) =
      Integer.Sparse.eval keyMomentRow2425 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3229) := by
    have ha : gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge = raw42162 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42162Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42162 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4895) := by
    have ha : gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge = raw42163 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42163Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42163 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2425).leftCharge (GramAssembly.key 2425).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2425, Integer.Sparse.eval]
  ring

theorem keyMoment2426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2426) =
      Integer.Sparse.eval keyMomentRow2426 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3109) := by
    have ha : gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge = raw42164 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42164Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42164 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5271) := by
    have ha : gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge = raw42165 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42165Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42165 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2426).leftCharge (GramAssembly.key 2426).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2426, Integer.Sparse.eval]
  ring

theorem keyMoment2427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2427) =
      Integer.Sparse.eval keyMomentRow2427 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3996) := by
    have ha : gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge = raw42166 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42166Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42166 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5410) := by
    have ha : gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge = raw42167 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42167Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42167 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2427).leftCharge (GramAssembly.key 2427).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2427, Integer.Sparse.eval]
  ring

theorem keyMoment2428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2428) =
      Integer.Sparse.eval keyMomentRow2428 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3995) := by
    have ha : gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge = raw42168 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42168Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42168 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5473) := by
    have ha : gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge = raw42169 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42169Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42169 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2428).leftCharge (GramAssembly.key 2428).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2428, Integer.Sparse.eval]
  ring

theorem keyMoment2429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2429) =
      Integer.Sparse.eval keyMomentRow2429 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge = raw42170 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42170Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42170 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge = raw42171 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42171Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42171 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2429).leftCharge (GramAssembly.key 2429).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2429, Integer.Sparse.eval]
  ring

theorem keyMoment2430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2430) =
      Integer.Sparse.eval keyMomentRow2430 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3990) := by
    have ha : gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge = raw42172 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42172Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42172 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5424) := by
    have ha : gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge = raw42173 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42173Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42173 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2430).leftCharge (GramAssembly.key 2430).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2430, Integer.Sparse.eval]
  ring

theorem keyMoment2431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2431) =
      Integer.Sparse.eval keyMomentRow2431 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3871) := by
    have ha : gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge = raw42174 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42174Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42174 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge = raw42175 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42175Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42175 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2431).leftCharge (GramAssembly.key 2431).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2431, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

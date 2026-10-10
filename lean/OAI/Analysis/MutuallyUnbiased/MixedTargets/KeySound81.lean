import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical332

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2592) =
      Integer.Sparse.eval keyMomentRow2592 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2144) := by
    have ha : gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge = raw42496 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42496Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42496 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4665) := by
    have ha : gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge = raw42497 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42497Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42497 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2592, Integer.Sparse.eval]
  ring

theorem keyMoment2593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2593) =
      Integer.Sparse.eval keyMomentRow2593 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2171) := by
    have ha : gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge = raw42498 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42498Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42498 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4762) := by
    have ha : gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge = raw42499 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42499Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42499 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2593, Integer.Sparse.eval]
  ring

theorem keyMoment2594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2594) =
      Integer.Sparse.eval keyMomentRow2594 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2195) := by
    have ha : gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge = raw42500 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42500Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42500 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4803) := by
    have ha : gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge = raw42501 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42501Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42501 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2594, Integer.Sparse.eval]
  ring

theorem keyMoment2595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2595) =
      Integer.Sparse.eval keyMomentRow2595 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2252) := by
    have ha : gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge = raw42502 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42502Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42502 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge = raw42503 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42503Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42503 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2595, Integer.Sparse.eval]
  ring

theorem keyMoment2596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2596) =
      Integer.Sparse.eval keyMomentRow2596 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3222) := by
    have ha : gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge = raw42504 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42504Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42504 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4891) := by
    have ha : gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge = raw42505 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42505Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42505 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2596, Integer.Sparse.eval]
  ring

theorem keyMoment2597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2597) =
      Integer.Sparse.eval keyMomentRow2597 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3016) := by
    have ha : gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge = raw42506 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42506Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42506 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5254) := by
    have ha : gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge = raw42507 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42507Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42507 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2597, Integer.Sparse.eval]
  ring

theorem keyMoment2598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2598) =
      Integer.Sparse.eval keyMomentRow2598 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3803) := by
    have ha : gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge = raw42508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42508 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5407) := by
    have ha : gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge = raw42509 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42509Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42509 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2598, Integer.Sparse.eval]
  ring

theorem keyMoment2599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2599) =
      Integer.Sparse.eval keyMomentRow2599 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3802) := by
    have ha : gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge = raw42510 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42510Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42510 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5402) := by
    have ha : gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge = raw42511 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42511Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42511 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2599, Integer.Sparse.eval]
  ring

theorem keyMoment2600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2600) =
      Integer.Sparse.eval keyMomentRow2600 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2654) := by
    have ha : gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge = raw42512 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42512Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42512 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5216) := by
    have ha : gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge = raw42513 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42513Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42513 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2600, Integer.Sparse.eval]
  ring

theorem keyMoment2601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2601) =
      Integer.Sparse.eval keyMomentRow2601 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3025) := by
    have ha : gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge = raw42514 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42514Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42514 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5287) := by
    have ha : gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge = raw42515 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42515Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42515 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2601, Integer.Sparse.eval]
  ring

theorem keyMoment2602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2602) =
      Integer.Sparse.eval keyMomentRow2602 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2659) := by
    have ha : gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge = raw42516 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42516Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42516 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4976) := by
    have ha : gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge = raw42517 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42517Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42517 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2602, Integer.Sparse.eval]
  ring

theorem keyMoment2603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2603) =
      Integer.Sparse.eval keyMomentRow2603 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3762) := by
    have ha : gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge = raw42518 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42518Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42518 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5360) := by
    have ha : gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge = raw42519 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42519Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42519 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2603, Integer.Sparse.eval]
  ring

theorem keyMoment2604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2604) =
      Integer.Sparse.eval keyMomentRow2604 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3553) := by
    have ha : gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge = raw42520 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42520Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42520 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4963) := by
    have ha : gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge = raw42521 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42521Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42521 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2604, Integer.Sparse.eval]
  ring

theorem keyMoment2605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2605) =
      Integer.Sparse.eval keyMomentRow2605 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3509) := by
    have ha : gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge = raw42522 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42522Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42522 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4957) := by
    have ha : gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge = raw42523 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42523Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42523 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2605, Integer.Sparse.eval]
  ring

theorem keyMoment2606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2606) =
      Integer.Sparse.eval keyMomentRow2606 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2653) := by
    have ha : gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge = raw42524 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42524Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42524 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5215) := by
    have ha : gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge = raw42525 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42525Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42525 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2606, Integer.Sparse.eval]
  ring

theorem keyMoment2607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2607) =
      Integer.Sparse.eval keyMomentRow2607 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3761) := by
    have ha : gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge = raw42526 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42526Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42526 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5353) := by
    have ha : gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge = raw42527 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42527Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42527 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2607, Integer.Sparse.eval]
  ring

theorem keyMoment2608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2608) =
      Integer.Sparse.eval keyMomentRow2608 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3221) := by
    have ha : gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge = raw42528 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42528Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42528 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge = raw42529 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42529Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42529 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2608, Integer.Sparse.eval]
  ring

theorem keyMoment2609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2609) =
      Integer.Sparse.eval keyMomentRow2609 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3023) := by
    have ha : gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge = raw42530 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42530Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42530 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5286) := by
    have ha : gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge = raw42531 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42531Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42531 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2609, Integer.Sparse.eval]
  ring

theorem keyMoment2610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2610) =
      Integer.Sparse.eval keyMomentRow2610 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2655) := by
    have ha : gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge = raw42532 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42532Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42532 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5116) := by
    have ha : gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge = raw42533 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42533Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42533 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2610, Integer.Sparse.eval]
  ring

theorem keyMoment2611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2611) =
      Integer.Sparse.eval keyMomentRow2611 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3024) := by
    have ha : gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge = raw42534 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42534Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42534 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5103) := by
    have ha : gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge = raw42535 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42535Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42535 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2611, Integer.Sparse.eval]
  ring

theorem keyMoment2612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2612) =
      Integer.Sparse.eval keyMomentRow2612 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2657) := by
    have ha : gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge = raw42536 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42536Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42536 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4548) := by
    have ha : gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge = raw42537 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42537Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42537 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2612, Integer.Sparse.eval]
  ring

theorem keyMoment2613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2613) =
      Integer.Sparse.eval keyMomentRow2613 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3464) := by
    have ha : gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge = raw42538 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42538Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42538 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5086) := by
    have ha : gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge = raw42539 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42539Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42539 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2613, Integer.Sparse.eval]
  ring

theorem keyMoment2614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2614) =
      Integer.Sparse.eval keyMomentRow2614 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3259) := by
    have ha : gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge = raw42540 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42540Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42540 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4545) := by
    have ha : gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge = raw42541 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42541Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42541 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2614, Integer.Sparse.eval]
  ring

theorem keyMoment2615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2615) =
      Integer.Sparse.eval keyMomentRow2615 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3258) := by
    have ha : gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge = raw42542 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42542Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42542 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4529) := by
    have ha : gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge = raw42543 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42543Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42543 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2615, Integer.Sparse.eval]
  ring

theorem keyMoment2616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2616) =
      Integer.Sparse.eval keyMomentRow2616 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2652) := by
    have ha : gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge = raw42544 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42544Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42544 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5035) := by
    have ha : gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge = raw42545 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42545Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42545 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2616, Integer.Sparse.eval]
  ring

theorem keyMoment2617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2617) =
      Integer.Sparse.eval keyMomentRow2617 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3463) := by
    have ha : gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge = raw42546 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42546Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42546 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5074) := by
    have ha : gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge = raw42547 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42547Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42547 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2617, Integer.Sparse.eval]
  ring

theorem keyMoment2618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2618) =
      Integer.Sparse.eval keyMomentRow2618 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2656) := by
    have ha : gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge = raw42548 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42548Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42548 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5217) := by
    have ha : gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge = raw42549 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42549Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42549 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2618, Integer.Sparse.eval]
  ring

theorem keyMoment2619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2619) =
      Integer.Sparse.eval keyMomentRow2619 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1716) := by
    have ha : gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge = raw42550 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42550Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42550 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4500) := by
    have ha : gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge = raw42551 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42551Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42551 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2619, Integer.Sparse.eval]
  ring

theorem keyMoment2620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2620) =
      Integer.Sparse.eval keyMomentRow2620 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1513) := by
    have ha : gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge = raw42552 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42552Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42552 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4179) := by
    have ha : gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge = raw42553 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42553Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42553 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2620, Integer.Sparse.eval]
  ring

theorem keyMoment2621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2621) =
      Integer.Sparse.eval keyMomentRow2621 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1715) := by
    have ha : gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge = raw42554 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42554Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42554 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4475) := by
    have ha : gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge = raw42555 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42555Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42555 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2621, Integer.Sparse.eval]
  ring

theorem keyMoment2622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2622) =
      Integer.Sparse.eval keyMomentRow2622 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1512) := by
    have ha : gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge = raw42556 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42556Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42556 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4176) := by
    have ha : gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge = raw42557 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42557Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42557 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2622, Integer.Sparse.eval]
  ring

theorem keyMoment2623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2623) =
      Integer.Sparse.eval keyMomentRow2623 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1511) := by
    have ha : gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge = raw42558 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42558Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42558 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4154) := by
    have ha : gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge = raw42559 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42559Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42559 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2623, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

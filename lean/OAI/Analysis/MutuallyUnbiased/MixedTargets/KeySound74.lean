import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical328

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2368) =
      Integer.Sparse.eval keyMomentRow2368 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4038) := by
    have ha : gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge = raw42048 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42048Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42048 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5408) := by
    have ha : gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge = raw42049 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42049Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42049 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2368).leftCharge (GramAssembly.key 2368).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2368, Integer.Sparse.eval]; ring

theorem keyMoment2369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2369) =
      Integer.Sparse.eval keyMomentRow2369 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3847) := by
    have ha : gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge = raw42050 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42050Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42050 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5406) := by
    have ha : gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge = raw42051 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42051Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42051 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2369).leftCharge (GramAssembly.key 2369).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2369, Integer.Sparse.eval]; ring

theorem keyMoment2370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2370) =
      Integer.Sparse.eval keyMomentRow2370 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3230) := by
    have ha : gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge = raw42052 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42052Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42052 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4894) := by
    have ha : gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge = raw42053 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42053Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42053 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2370).leftCharge (GramAssembly.key 2370).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2370, Integer.Sparse.eval]; ring

theorem keyMoment2371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2371) =
      Integer.Sparse.eval keyMomentRow2371 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3089) := by
    have ha : gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge = raw42054 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42054Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42054 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5258) := by
    have ha : gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge = raw42055 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42055Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42055 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2371).leftCharge (GramAssembly.key 2371).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2371, Integer.Sparse.eval]; ring

theorem keyMoment2372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2372) =
      Integer.Sparse.eval keyMomentRow2372 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4035) := by
    have ha : gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge = raw42056 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42056Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42056 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5409) := by
    have ha : gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge = raw42057 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42057Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42057 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2372).leftCharge (GramAssembly.key 2372).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2372, Integer.Sparse.eval]; ring

theorem keyMoment2373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2373) =
      Integer.Sparse.eval keyMomentRow2373 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4003) := by
    have ha : gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge = raw42058 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42058Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42058 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5428) := by
    have ha : gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge = raw42059 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42059Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42059 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2373).leftCharge (GramAssembly.key 2373).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2373, Integer.Sparse.eval]; ring

theorem keyMoment2374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2374) =
      Integer.Sparse.eval keyMomentRow2374 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge = raw42060 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42060Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42060 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge = raw42061 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42061Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42061 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2374).leftCharge (GramAssembly.key 2374).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2374, Integer.Sparse.eval]; ring

theorem keyMoment2375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2375) =
      Integer.Sparse.eval keyMomentRow2375 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4032) := by
    have ha : gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge = raw42062 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42062Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42062 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5423) := by
    have ha : gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge = raw42063 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42063Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42063 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2375).leftCharge (GramAssembly.key 2375).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2375, Integer.Sparse.eval]; ring

theorem keyMoment2376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2376) =
      Integer.Sparse.eval keyMomentRow2376 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3990) := by
    have ha : gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge = raw42064 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42064Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42064 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5424) := by
    have ha : gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge = raw42065 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42065Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42065 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2376).leftCharge (GramAssembly.key 2376).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2376, Integer.Sparse.eval]; ring

theorem keyMoment2377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2377) =
      Integer.Sparse.eval keyMomentRow2377 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge = raw42066 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42066Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42066 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge = raw42067 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42067Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42067 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2377).leftCharge (GramAssembly.key 2377).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2377, Integer.Sparse.eval]; ring

theorem keyMoment2378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2378) =
      Integer.Sparse.eval keyMomentRow2378 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3841) := by
    have ha : gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge = raw42068 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42068Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42068 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5426) := by
    have ha : gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge = raw42069 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42069Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42069 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2378).leftCharge (GramAssembly.key 2378).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2378, Integer.Sparse.eval]; ring

theorem keyMoment2379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2379) =
      Integer.Sparse.eval keyMomentRow2379 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge = raw42070 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42070Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42070 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge = raw42071 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42071Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42071 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2379).leftCharge (GramAssembly.key 2379).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2379, Integer.Sparse.eval]; ring

theorem keyMoment2380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2380) =
      Integer.Sparse.eval keyMomentRow2380 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3990) := by
    have ha : gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge = raw42072 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42072Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42072 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5424) := by
    have ha : gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge = raw42073 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42073Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42073 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2380).leftCharge (GramAssembly.key 2380).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2380, Integer.Sparse.eval]; ring

theorem keyMoment2381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2381) =
      Integer.Sparse.eval keyMomentRow2381 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4034) := by
    have ha : gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge = raw42074 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42074Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42074 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5427) := by
    have ha : gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge = raw42075 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42075Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42075 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2381).leftCharge (GramAssembly.key 2381).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2381, Integer.Sparse.eval]; ring

theorem keyMoment2382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2382) =
      Integer.Sparse.eval keyMomentRow2382 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3103) := by
    have ha : gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge = raw42076 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42076Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42076 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5291) := by
    have ha : gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge = raw42077 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42077Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42077 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2382).leftCharge (GramAssembly.key 2382).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2382, Integer.Sparse.eval]; ring

theorem keyMoment2383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2383) =
      Integer.Sparse.eval keyMomentRow2383 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge = raw42078 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42078Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42078 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge = raw42079 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42079Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42079 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2383).leftCharge (GramAssembly.key 2383).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2383, Integer.Sparse.eval]; ring

theorem keyMoment2384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2384) =
      Integer.Sparse.eval keyMomentRow2384 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4027) := by
    have ha : gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge = raw42080 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42080Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42080 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5432) := by
    have ha : gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge = raw42081 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42081Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42081 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2384).leftCharge (GramAssembly.key 2384).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2384, Integer.Sparse.eval]; ring

theorem keyMoment2385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2385) =
      Integer.Sparse.eval keyMomentRow2385 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge = raw42082 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42082Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42082 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge = raw42083 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42083Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42083 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2385).leftCharge (GramAssembly.key 2385).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2385, Integer.Sparse.eval]; ring

theorem keyMoment2386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2386) =
      Integer.Sparse.eval keyMomentRow2386 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge = raw42084 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42084Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42084 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge = raw42085 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42085Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42085 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2386).leftCharge (GramAssembly.key 2386).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2386, Integer.Sparse.eval]; ring

theorem keyMoment2387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2387) =
      Integer.Sparse.eval keyMomentRow2387 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge = raw42086 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42086Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42086 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge = raw42087 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42087Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42087 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2387).leftCharge (GramAssembly.key 2387).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2387, Integer.Sparse.eval]; ring

theorem keyMoment2388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2388) =
      Integer.Sparse.eval keyMomentRow2388 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3993) := by
    have ha : gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge = raw42088 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42088Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42088 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5438) := by
    have ha : gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge = raw42089 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42089Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42089 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2388).leftCharge (GramAssembly.key 2388).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2388, Integer.Sparse.eval]; ring

theorem keyMoment2389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2389) =
      Integer.Sparse.eval keyMomentRow2389 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge = raw42090 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42090Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42090 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge = raw42091 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42091Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42091 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2389).leftCharge (GramAssembly.key 2389).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2389, Integer.Sparse.eval]; ring

theorem keyMoment2390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2390) =
      Integer.Sparse.eval keyMomentRow2390 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge = raw42092 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42092Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42092 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge = raw42093 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42093Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42093 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2390).leftCharge (GramAssembly.key 2390).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2390, Integer.Sparse.eval]; ring

theorem keyMoment2391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2391) =
      Integer.Sparse.eval keyMomentRow2391 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4026) := by
    have ha : gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge = raw42094 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42094Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42094 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5431) := by
    have ha : gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge = raw42095 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42095Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42095 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2391).leftCharge (GramAssembly.key 2391).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2391, Integer.Sparse.eval]; ring

theorem keyMoment2392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2392) =
      Integer.Sparse.eval keyMomentRow2392 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge = raw42096 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42096Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42096 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge = raw42097 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42097Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42097 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2392).leftCharge (GramAssembly.key 2392).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2392, Integer.Sparse.eval]; ring

theorem keyMoment2393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2393) =
      Integer.Sparse.eval keyMomentRow2393 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4027) := by
    have ha : gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge = raw42098 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42098Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42098 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5432) := by
    have ha : gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge = raw42099 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42099Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42099 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2393).leftCharge (GramAssembly.key 2393).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2393, Integer.Sparse.eval]; ring

theorem keyMoment2394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2394) =
      Integer.Sparse.eval keyMomentRow2394 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3993) := by
    have ha : gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge = raw42100 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42100Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42100 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5438) := by
    have ha : gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge = raw42101 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42101Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42101 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2394).leftCharge (GramAssembly.key 2394).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2394, Integer.Sparse.eval]; ring

theorem keyMoment2395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2395) =
      Integer.Sparse.eval keyMomentRow2395 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge = raw42102 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42102Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42102 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge = raw42103 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42103Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42103 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2395).leftCharge (GramAssembly.key 2395).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2395, Integer.Sparse.eval]; ring

theorem keyMoment2396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2396) =
      Integer.Sparse.eval keyMomentRow2396 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge = raw42104 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42104Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42104 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge = raw42105 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42105Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42105 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2396).leftCharge (GramAssembly.key 2396).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2396, Integer.Sparse.eval]; ring

theorem keyMoment2397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2397) =
      Integer.Sparse.eval keyMomentRow2397 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge = raw42106 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42106Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42106 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge = raw42107 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42107Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42107 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2397).leftCharge (GramAssembly.key 2397).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2397, Integer.Sparse.eval]; ring

theorem keyMoment2398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2398) =
      Integer.Sparse.eval keyMomentRow2398 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4026) := by
    have ha : gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge = raw42108 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42108Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42108 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5431) := by
    have ha : gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge = raw42109 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42109Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42109 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2398).leftCharge (GramAssembly.key 2398).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2398, Integer.Sparse.eval]; ring

theorem keyMoment2399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2399) =
      Integer.Sparse.eval keyMomentRow2399 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4030) := by
    have ha : gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge = raw42110 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42110Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42110 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5449) := by
    have ha : gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge = raw42111 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42111Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42111 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2399).leftCharge (GramAssembly.key 2399).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2399, Integer.Sparse.eval]; ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

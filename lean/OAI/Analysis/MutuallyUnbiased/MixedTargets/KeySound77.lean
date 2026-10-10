import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical330

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2464) =
      Integer.Sparse.eval keyMomentRow2464 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3558) := by
    have ha : gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge = raw42240 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42240Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42240 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5160) := by
    have ha : gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge = raw42241 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42241Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42241 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2464).leftCharge (GramAssembly.key 2464).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2464, Integer.Sparse.eval]; ring

theorem keyMoment2465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2465) =
      Integer.Sparse.eval keyMomentRow2465 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3517) := by
    have ha : gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge = raw42242 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42242Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42242 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5138) := by
    have ha : gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge = raw42243 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42243Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42243 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2465).leftCharge (GramAssembly.key 2465).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2465, Integer.Sparse.eval]; ring

theorem keyMoment2466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2466) =
      Integer.Sparse.eval keyMomentRow2466 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2718) := by
    have ha : gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge = raw42244 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42244Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42244 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5255) := by
    have ha : gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge = raw42245 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42245Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42245 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2466).leftCharge (GramAssembly.key 2466).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2466, Integer.Sparse.eval]; ring

theorem keyMoment2467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2467) =
      Integer.Sparse.eval keyMomentRow2467 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3978) := by
    have ha : gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge = raw42246 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42246Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42246 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5480) := by
    have ha : gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge = raw42247 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42247Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42247 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2467).leftCharge (GramAssembly.key 2467).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2467, Integer.Sparse.eval]; ring

theorem keyMoment2468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2468) =
      Integer.Sparse.eval keyMomentRow2468 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge = raw42248 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42248Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42248 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge = raw42249 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42249Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42249 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2468).leftCharge (GramAssembly.key 2468).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2468, Integer.Sparse.eval]; ring

theorem keyMoment2469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2469) =
      Integer.Sparse.eval keyMomentRow2469 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2737) := by
    have ha : gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge = raw42250 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42250Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42250 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4617) := by
    have ha : gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge = raw42251 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42251Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42251 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2469).leftCharge (GramAssembly.key 2469).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2469, Integer.Sparse.eval]; ring

theorem keyMoment2470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2470) =
      Integer.Sparse.eval keyMomentRow2470 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge = raw42252 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42252Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42252 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge = raw42253 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42253Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42253 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2470).leftCharge (GramAssembly.key 2470).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2470, Integer.Sparse.eval]; ring

theorem keyMoment2471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2471) =
      Integer.Sparse.eval keyMomentRow2471 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3303) := by
    have ha : gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge = raw42254 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42254Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42254 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4616) := by
    have ha : gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge = raw42255 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42255Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42255 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2471).leftCharge (GramAssembly.key 2471).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2471, Integer.Sparse.eval]; ring

theorem keyMoment2472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2472) =
      Integer.Sparse.eval keyMomentRow2472 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3296) := by
    have ha : gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge = raw42256 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42256Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42256 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4607) := by
    have ha : gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge = raw42257 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42257Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42257 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2472).leftCharge (GramAssembly.key 2472).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2472, Integer.Sparse.eval]; ring

theorem keyMoment2473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2473) =
      Integer.Sparse.eval keyMomentRow2473 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2719) := by
    have ha : gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge = raw42258 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42258Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42258 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5161) := by
    have ha : gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge = raw42259 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42259Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42259 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2473).leftCharge (GramAssembly.key 2473).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2473, Integer.Sparse.eval]; ring

theorem keyMoment2474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2474) =
      Integer.Sparse.eval keyMomentRow2474 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge = raw42260 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42260Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42260 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge = raw42261 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42261Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42261 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2474).leftCharge (GramAssembly.key 2474).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2474, Integer.Sparse.eval]; ring

theorem keyMoment2475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2475) =
      Integer.Sparse.eval keyMomentRow2475 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2736) := by
    have ha : gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge = raw42262 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42262Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42262 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5269) := by
    have ha : gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge = raw42263 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42263Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42263 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2475).leftCharge (GramAssembly.key 2475).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2475, Integer.Sparse.eval]; ring

theorem keyMoment2476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2476) =
      Integer.Sparse.eval keyMomentRow2476 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3289) := by
    have ha : gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge = raw42264 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42264Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42264 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4599) := by
    have ha : gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge = raw42265 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42265Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42265 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2476).leftCharge (GramAssembly.key 2476).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2476, Integer.Sparse.eval]; ring

theorem keyMoment2477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2477) =
      Integer.Sparse.eval keyMomentRow2477 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3558) := by
    have ha : gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge = raw42266 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42266Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42266 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5160) := by
    have ha : gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge = raw42267 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42267Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42267 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2477).leftCharge (GramAssembly.key 2477).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2477, Integer.Sparse.eval]; ring

theorem keyMoment2478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2478) =
      Integer.Sparse.eval keyMomentRow2478 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3571) := by
    have ha : gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge = raw42268 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42268Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42268 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge = raw42269 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42269Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42269 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2478).leftCharge (GramAssembly.key 2478).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2478, Integer.Sparse.eval]; ring

theorem keyMoment2479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2479) =
      Integer.Sparse.eval keyMomentRow2479 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3973) := by
    have ha : gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge = raw42270 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42270Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42270 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5461) := by
    have ha : gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge = raw42271 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42271Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42271 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2479).leftCharge (GramAssembly.key 2479).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2479, Integer.Sparse.eval]; ring

theorem keyMoment2480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2480) =
      Integer.Sparse.eval keyMomentRow2480 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3557) := by
    have ha : gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge = raw42272 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42272Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42272 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5144) := by
    have ha : gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge = raw42273 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42273Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42273 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2480).leftCharge (GramAssembly.key 2480).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2480, Integer.Sparse.eval]; ring

theorem keyMoment2481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2481) =
      Integer.Sparse.eval keyMomentRow2481 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3842) := by
    have ha : gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge = raw42274 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42274Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42274 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5419) := by
    have ha : gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge = raw42275 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42275Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42275 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2481).leftCharge (GramAssembly.key 2481).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2481, Integer.Sparse.eval]; ring

theorem keyMoment2482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2482) =
      Integer.Sparse.eval keyMomentRow2482 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge = raw42276 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42276Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42276 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5436) := by
    have ha : gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge = raw42277 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42277Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42277 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2482).leftCharge (GramAssembly.key 2482).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2482, Integer.Sparse.eval]; ring

theorem keyMoment2483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2483) =
      Integer.Sparse.eval keyMomentRow2483 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge = raw42278 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42278Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42278 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge = raw42279 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42279Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42279 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2483).leftCharge (GramAssembly.key 2483).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2483, Integer.Sparse.eval]; ring

theorem keyMoment2484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2484) =
      Integer.Sparse.eval keyMomentRow2484 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3868) := by
    have ha : gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge = raw42280 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42280Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42280 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5385) := by
    have ha : gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge = raw42281 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42281Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42281 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2484).leftCharge (GramAssembly.key 2484).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2484, Integer.Sparse.eval]; ring

theorem keyMoment2485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2485) =
      Integer.Sparse.eval keyMomentRow2485 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3832) := by
    have ha : gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge = raw42282 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42282Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42282 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5379) := by
    have ha : gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge = raw42283 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42283Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42283 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2485).leftCharge (GramAssembly.key 2485).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2485, Integer.Sparse.eval]; ring

theorem keyMoment2486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2486) =
      Integer.Sparse.eval keyMomentRow2486 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3869) := by
    have ha : gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge = raw42284 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42284Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42284 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5414) := by
    have ha : gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge = raw42285 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42285Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42285 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2486).leftCharge (GramAssembly.key 2486).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2486, Integer.Sparse.eval]; ring

theorem keyMoment2487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2487) =
      Integer.Sparse.eval keyMomentRow2487 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge = raw42286 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42286Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42286 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge = raw42287 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42287Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42287 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2487).leftCharge (GramAssembly.key 2487).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2487, Integer.Sparse.eval]; ring

theorem keyMoment2488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2488) =
      Integer.Sparse.eval keyMomentRow2488 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge = raw42288 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42288Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42288 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge = raw42289 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42289Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42289 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2488).leftCharge (GramAssembly.key 2488).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2488, Integer.Sparse.eval]; ring

theorem keyMoment2489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2489) =
      Integer.Sparse.eval keyMomentRow2489 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3869) := by
    have ha : gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge = raw42290 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42290Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42290 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5414) := by
    have ha : gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge = raw42291 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42291Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42291 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2489).leftCharge (GramAssembly.key 2489).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2489, Integer.Sparse.eval]; ring

theorem keyMoment2490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2490) =
      Integer.Sparse.eval keyMomentRow2490 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge = raw42292 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42292Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42292 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge = raw42293 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42293Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42293 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2490).leftCharge (GramAssembly.key 2490).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2490, Integer.Sparse.eval]; ring

theorem keyMoment2491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2491) =
      Integer.Sparse.eval keyMomentRow2491 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3565) := by
    have ha : gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge = raw42294 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42294Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42294 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5164) := by
    have ha : gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge = raw42295 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42295Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42295 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2491).leftCharge (GramAssembly.key 2491).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2491, Integer.Sparse.eval]; ring

theorem keyMoment2492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2492) =
      Integer.Sparse.eval keyMomentRow2492 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3955) := by
    have ha : gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge = raw42296 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42296Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42296 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5470) := by
    have ha : gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge = raw42297 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42297Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42297 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2492).leftCharge (GramAssembly.key 2492).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2492, Integer.Sparse.eval]; ring

theorem keyMoment2493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2493) =
      Integer.Sparse.eval keyMomentRow2493 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge = raw42298 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42298Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42298 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge = raw42299 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42299Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42299 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2493).leftCharge (GramAssembly.key 2493).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2493, Integer.Sparse.eval]; ring

theorem keyMoment2494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2494) =
      Integer.Sparse.eval keyMomentRow2494 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3306) := by
    have ha : gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge = raw42300 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42300Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42300 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4620) := by
    have ha : gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge = raw42301 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42301Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42301 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2494).leftCharge (GramAssembly.key 2494).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2494, Integer.Sparse.eval]; ring

theorem keyMoment2495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2495) =
      Integer.Sparse.eval keyMomentRow2495 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3294) := by
    have ha : gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge = raw42302 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42302Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42302 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4603) := by
    have ha : gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge = raw42303 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42303Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42303 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2495).leftCharge (GramAssembly.key 2495).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2495, Integer.Sparse.eval]; ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

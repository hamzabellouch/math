import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical329

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2432) =
      Integer.Sparse.eval keyMomentRow2432 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge = raw42176 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42176Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42176 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge = raw42177 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42177Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42177 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2432).leftCharge (GramAssembly.key 2432).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2432, Integer.Sparse.eval]
  ring

theorem keyMoment2433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2433) =
      Integer.Sparse.eval keyMomentRow2433 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge = raw42178 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42178Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42178 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge = raw42179 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42179Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42179 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2433).leftCharge (GramAssembly.key 2433).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2433, Integer.Sparse.eval]
  ring

theorem keyMoment2434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2434) =
      Integer.Sparse.eval keyMomentRow2434 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3994) := by
    have ha : gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge = raw42180 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42180Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42180 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5478) := by
    have ha : gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge = raw42181 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42181Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42181 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2434).leftCharge (GramAssembly.key 2434).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2434, Integer.Sparse.eval]
  ring

theorem keyMoment2435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2435) =
      Integer.Sparse.eval keyMomentRow2435 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3119) := by
    have ha : gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge = raw42182 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42182Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42182 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5304) := by
    have ha : gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge = raw42183 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42183Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42183 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2435).leftCharge (GramAssembly.key 2435).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2435, Integer.Sparse.eval]
  ring

theorem keyMoment2436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2436) =
      Integer.Sparse.eval keyMomentRow2436 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge = raw42184 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42184Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42184 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge = raw42185 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42185Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42185 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2436).leftCharge (GramAssembly.key 2436).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2436, Integer.Sparse.eval]
  ring

theorem keyMoment2437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2437) =
      Integer.Sparse.eval keyMomentRow2437 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3993) := by
    have ha : gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge = raw42186 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42186Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42186 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5438) := by
    have ha : gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge = raw42187 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42187Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42187 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2437).leftCharge (GramAssembly.key 2437).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2437, Integer.Sparse.eval]
  ring

theorem keyMoment2438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2438) =
      Integer.Sparse.eval keyMomentRow2438 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge = raw42188 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42188Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42188 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge = raw42189 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42189Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42189 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2438).leftCharge (GramAssembly.key 2438).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2438, Integer.Sparse.eval]
  ring

theorem keyMoment2439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2439) =
      Integer.Sparse.eval keyMomentRow2439 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3540) := by
    have ha : gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge = raw42190 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42190Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42190 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge = raw42191 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42191Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42191 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2439).leftCharge (GramAssembly.key 2439).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2439, Integer.Sparse.eval]
  ring

theorem keyMoment2440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2440) =
      Integer.Sparse.eval keyMomentRow2440 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge = raw42192 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42192Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42192 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge = raw42193 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42193Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42193 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2440).leftCharge (GramAssembly.key 2440).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2440, Integer.Sparse.eval]
  ring

theorem keyMoment2441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2441) =
      Integer.Sparse.eval keyMomentRow2441 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3997) := by
    have ha : gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge = raw42194 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42194Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42194 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5484) := by
    have ha : gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge = raw42195 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42195Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42195 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2441).leftCharge (GramAssembly.key 2441).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2441, Integer.Sparse.eval]
  ring

theorem keyMoment2442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2442) =
      Integer.Sparse.eval keyMomentRow2442 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3978) := by
    have ha : gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge = raw42196 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42196Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42196 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5480) := by
    have ha : gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge = raw42197 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42197Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42197 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2442).leftCharge (GramAssembly.key 2442).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2442, Integer.Sparse.eval]
  ring

theorem keyMoment2443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2443) =
      Integer.Sparse.eval keyMomentRow2443 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge = raw42198 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42198Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42198 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge = raw42199 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42199Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42199 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2443).leftCharge (GramAssembly.key 2443).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2443, Integer.Sparse.eval]
  ring

theorem keyMoment2444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2444) =
      Integer.Sparse.eval keyMomentRow2444 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3225) := by
    have ha : gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge = raw42200 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42200Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42200 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4896) := by
    have ha : gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge = raw42201 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42201Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42201 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2444).leftCharge (GramAssembly.key 2444).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2444, Integer.Sparse.eval]
  ring

theorem keyMoment2445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2445) =
      Integer.Sparse.eval keyMomentRow2445 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge = raw42202 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42202Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42202 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge = raw42203 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42203Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42203 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2445).leftCharge (GramAssembly.key 2445).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2445, Integer.Sparse.eval]
  ring

theorem keyMoment2446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2446) =
      Integer.Sparse.eval keyMomentRow2446 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3883) := by
    have ha : gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge = raw42204 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42204Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42204 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5411) := by
    have ha : gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge = raw42205 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42205Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42205 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2446).leftCharge (GramAssembly.key 2446).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2446, Integer.Sparse.eval]
  ring

theorem keyMoment2447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2447) =
      Integer.Sparse.eval keyMomentRow2447 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge = raw42206 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42206Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42206 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge = raw42207 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42207Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42207 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2447).leftCharge (GramAssembly.key 2447).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2447, Integer.Sparse.eval]
  ring

theorem keyMoment2448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2448) =
      Integer.Sparse.eval keyMomentRow2448 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2729) := by
    have ha : gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge = raw42208 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42208Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42208 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5264) := by
    have ha : gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge = raw42209 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42209Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42209 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2448).leftCharge (GramAssembly.key 2448).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2448, Integer.Sparse.eval]
  ring

theorem keyMoment2449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2449) =
      Integer.Sparse.eval keyMomentRow2449 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge = raw42210 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42210Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42210 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge = raw42211 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42211Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42211 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2449).leftCharge (GramAssembly.key 2449).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2449, Integer.Sparse.eval]
  ring

theorem keyMoment2450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2450) =
      Integer.Sparse.eval keyMomentRow2450 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge = raw42212 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42212Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42212 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge = raw42213 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42213Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42213 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2450).leftCharge (GramAssembly.key 2450).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2450, Integer.Sparse.eval]
  ring

theorem keyMoment2451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2451) =
      Integer.Sparse.eval keyMomentRow2451 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3866) := by
    have ha : gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge = raw42214 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42214Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42214 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5382) := by
    have ha : gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge = raw42215 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42215Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42215 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2451).leftCharge (GramAssembly.key 2451).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2451, Integer.Sparse.eval]
  ring

theorem keyMoment2452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2452) =
      Integer.Sparse.eval keyMomentRow2452 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3834) := by
    have ha : gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge = raw42216 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42216Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42216 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5381) := by
    have ha : gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge = raw42217 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42217Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42217 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2452).leftCharge (GramAssembly.key 2452).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2452, Integer.Sparse.eval]
  ring

theorem keyMoment2453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2453) =
      Integer.Sparse.eval keyMomentRow2453 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2708) := by
    have ha : gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge = raw42218 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42218Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42218 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5249) := by
    have ha : gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge = raw42219 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42219Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42219 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2453).leftCharge (GramAssembly.key 2453).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2453, Integer.Sparse.eval]
  ring

theorem keyMoment2454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2454) =
      Integer.Sparse.eval keyMomentRow2454 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3871) := by
    have ha : gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge = raw42220 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42220Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42220 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge = raw42221 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42221Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42221 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2454).leftCharge (GramAssembly.key 2454).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2454, Integer.Sparse.eval]
  ring

theorem keyMoment2455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2455) =
      Integer.Sparse.eval keyMomentRow2455 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3882) := by
    have ha : gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge = raw42222 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42222Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42222 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5447) := by
    have ha : gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge = raw42223 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42223Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42223 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2455).leftCharge (GramAssembly.key 2455).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2455, Integer.Sparse.eval]
  ring

theorem keyMoment2456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2456) =
      Integer.Sparse.eval keyMomentRow2456 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3227) := by
    have ha : gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge = raw42224 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42224Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42224 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4888) := by
    have ha : gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge = raw42225 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42225Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42225 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2456).leftCharge (GramAssembly.key 2456).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2456, Integer.Sparse.eval]
  ring

theorem keyMoment2457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2457) =
      Integer.Sparse.eval keyMomentRow2457 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3085) := by
    have ha : gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge = raw42226 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42226Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42226 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5256) := by
    have ha : gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge = raw42227 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42227Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42227 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2457).leftCharge (GramAssembly.key 2457).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2457, Integer.Sparse.eval]
  ring

theorem keyMoment2458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2458) =
      Integer.Sparse.eval keyMomentRow2458 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3977) := by
    have ha : gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge = raw42228 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42228Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42228 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5405) := by
    have ha : gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge = raw42229 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42229Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42229 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2458).leftCharge (GramAssembly.key 2458).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2458, Integer.Sparse.eval]
  ring

theorem keyMoment2459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2459) =
      Integer.Sparse.eval keyMomentRow2459 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3976) := by
    have ha : gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge = raw42230 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42230Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42230 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5471) := by
    have ha : gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge = raw42231 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42231Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42231 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2459).leftCharge (GramAssembly.key 2459).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2459, Integer.Sparse.eval]
  ring

theorem keyMoment2460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2460) =
      Integer.Sparse.eval keyMomentRow2460 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2728) := by
    have ha : gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge = raw42232 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42232Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42232 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5263) := by
    have ha : gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge = raw42233 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42233Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42233 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2460).leftCharge (GramAssembly.key 2460).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2460, Integer.Sparse.eval]
  ring

theorem keyMoment2461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2461) =
      Integer.Sparse.eval keyMomentRow2461 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge = raw42234 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42234Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42234 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge = raw42235 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42235Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42235 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2461).leftCharge (GramAssembly.key 2461).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2461, Integer.Sparse.eval]
  ring

theorem keyMoment2462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2462) =
      Integer.Sparse.eval keyMomentRow2462 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2735) := by
    have ha : gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge = raw42236 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42236Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42236 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5173) := by
    have ha : gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge = raw42237 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42237Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42237 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2462).leftCharge (GramAssembly.key 2462).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2462, Integer.Sparse.eval]
  ring

theorem keyMoment2463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2463) =
      Integer.Sparse.eval keyMomentRow2463 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge = raw42238 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42238Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42238 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge = raw42239 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42239Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42239 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2463).leftCharge (GramAssembly.key 2463).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2463, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

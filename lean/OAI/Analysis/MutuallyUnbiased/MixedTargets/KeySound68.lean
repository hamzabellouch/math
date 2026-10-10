import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical325

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2176) =
      Integer.Sparse.eval keyMomentRow2176 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2670) := by
    have ha : gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge = raw41664 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41664Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41664 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5140) := by
    have ha : gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge = raw41665 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41665Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41665 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2176).leftCharge (GramAssembly.key 2176).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2176, Integer.Sparse.eval]
  ring

theorem keyMoment2177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2177) =
      Integer.Sparse.eval keyMomentRow2177 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2760) := by
    have ha : gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge = raw41666 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41666Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41666 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5288) := by
    have ha : gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge = raw41667 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41667Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41667 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2177).leftCharge (GramAssembly.key 2177).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2177, Integer.Sparse.eval]
  ring

theorem keyMoment2178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2178) =
      Integer.Sparse.eval keyMomentRow2178 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge = raw41668 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41668Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41668 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge = raw41669 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41669Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41669 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2178).leftCharge (GramAssembly.key 2178).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2178, Integer.Sparse.eval]
  ring

theorem keyMoment2179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2179) =
      Integer.Sparse.eval keyMomentRow2179 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2718) := by
    have ha : gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge = raw41670 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41670Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41670 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5255) := by
    have ha : gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge = raw41671 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41671Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41671 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2179).leftCharge (GramAssembly.key 2179).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2179, Integer.Sparse.eval]
  ring

theorem keyMoment2180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2180) =
      Integer.Sparse.eval keyMomentRow2180 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2669) := by
    have ha : gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge = raw41672 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41672Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41672 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5226) := by
    have ha : gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge = raw41673 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41673Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41673 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2180).leftCharge (GramAssembly.key 2180).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2180, Integer.Sparse.eval]
  ring

theorem keyMoment2181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2181) =
      Integer.Sparse.eval keyMomentRow2181 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge = raw41674 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41674Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41674 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5311) := by
    have ha : gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge = raw41675 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41675Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41675 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2181).leftCharge (GramAssembly.key 2181).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2181, Integer.Sparse.eval]
  ring

theorem keyMoment2182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2182) =
      Integer.Sparse.eval keyMomentRow2182 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2780) := by
    have ha : gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge = raw41676 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41676Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41676 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4626) := by
    have ha : gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge = raw41677 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41677Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41677 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2182).leftCharge (GramAssembly.key 2182).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2182, Integer.Sparse.eval]
  ring

theorem keyMoment2183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2183) =
      Integer.Sparse.eval keyMomentRow2183 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge = raw41678 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41678Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41678 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge = raw41679 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41679Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41679 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2183).leftCharge (GramAssembly.key 2183).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2183, Integer.Sparse.eval]
  ring

theorem keyMoment2184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2184) =
      Integer.Sparse.eval keyMomentRow2184 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2737) := by
    have ha : gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge = raw41680 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41680Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41680 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4617) := by
    have ha : gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge = raw41681 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41681Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41681 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2184).leftCharge (GramAssembly.key 2184).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2184, Integer.Sparse.eval]
  ring

theorem keyMoment2185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2185) =
      Integer.Sparse.eval keyMomentRow2185 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2683) := by
    have ha : gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge = raw41682 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41682Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41682 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4611) := by
    have ha : gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge = raw41683 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41683Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41683 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2185).leftCharge (GramAssembly.key 2185).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2185, Integer.Sparse.eval]
  ring

theorem keyMoment2186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2186) =
      Integer.Sparse.eval keyMomentRow2186 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2761) := by
    have ha : gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge = raw41684 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41684Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41684 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5175) := by
    have ha : gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge = raw41685 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41685Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41685 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2186).leftCharge (GramAssembly.key 2186).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2186, Integer.Sparse.eval]
  ring

theorem keyMoment2187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2187) =
      Integer.Sparse.eval keyMomentRow2187 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge = raw41686 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41686Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41686 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge = raw41687 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41687Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41687 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2187).leftCharge (GramAssembly.key 2187).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2187, Integer.Sparse.eval]
  ring

theorem keyMoment2188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2188) =
      Integer.Sparse.eval keyMomentRow2188 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2779) := by
    have ha : gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge = raw41688 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41688Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41688 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5303) := by
    have ha : gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge = raw41689 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41689Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41689 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2188).leftCharge (GramAssembly.key 2188).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2188, Integer.Sparse.eval]
  ring

theorem keyMoment2189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2189) =
      Integer.Sparse.eval keyMomentRow2189 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2702) := by
    have ha : gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge = raw41690 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41690Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41690 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4600) := by
    have ha : gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge = raw41691 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41691Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41691 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2189).leftCharge (GramAssembly.key 2189).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2189, Integer.Sparse.eval]
  ring

theorem keyMoment2190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2190) =
      Integer.Sparse.eval keyMomentRow2190 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2735) := by
    have ha : gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge = raw41692 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41692Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41692 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5173) := by
    have ha : gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge = raw41693 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41693Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41693 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2190).leftCharge (GramAssembly.key 2190).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2190, Integer.Sparse.eval]
  ring

theorem keyMoment2191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2191) =
      Integer.Sparse.eval keyMomentRow2191 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2738) := by
    have ha : gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge = raw41694 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41694Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41694 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge = raw41695 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41695Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41695 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2191).leftCharge (GramAssembly.key 2191).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2191, Integer.Sparse.eval]
  ring

theorem keyMoment2192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2192) =
      Integer.Sparse.eval keyMomentRow2192 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2736) := by
    have ha : gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge = raw41696 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41696Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41696 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5269) := by
    have ha : gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge = raw41697 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41697Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41697 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2192).leftCharge (GramAssembly.key 2192).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2192, Integer.Sparse.eval]
  ring

theorem keyMoment2193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2193) =
      Integer.Sparse.eval keyMomentRow2193 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2681) := by
    have ha : gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge = raw41698 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41698Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41698 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5151) := by
    have ha : gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge = raw41699 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41699Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41699 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2193).leftCharge (GramAssembly.key 2193).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2193, Integer.Sparse.eval]
  ring

theorem keyMoment2194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2194) =
      Integer.Sparse.eval keyMomentRow2194 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2682) := by
    have ha : gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge = raw41700 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41700Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41700 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5236) := by
    have ha : gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge = raw41701 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41701Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41701 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2194).leftCharge (GramAssembly.key 2194).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2194, Integer.Sparse.eval]
  ring

theorem keyMoment2195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2195) =
      Integer.Sparse.eval keyMomentRow2195 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2700) := by
    have ha : gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge = raw41702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41702 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5150) := by
    have ha : gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge = raw41703 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41703Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41703 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2195).leftCharge (GramAssembly.key 2195).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2195, Integer.Sparse.eval]
  ring

theorem keyMoment2196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2196) =
      Integer.Sparse.eval keyMomentRow2196 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2285) := by
    have ha : gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge = raw41704 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41704Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41704 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4900) := by
    have ha : gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge = raw41705 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41705Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41705 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2196).leftCharge (GramAssembly.key 2196).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2196, Integer.Sparse.eval]
  ring

theorem keyMoment2197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2197) =
      Integer.Sparse.eval keyMomentRow2197 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2222) := by
    have ha : gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge = raw41706 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41706Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41706 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4844) := by
    have ha : gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge = raw41707 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41707Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41707 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2197).leftCharge (GramAssembly.key 2197).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2197, Integer.Sparse.eval]
  ring

theorem keyMoment2198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2198) =
      Integer.Sparse.eval keyMomentRow2198 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2284) := by
    have ha : gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge = raw41708 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41708Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41708 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4892) := by
    have ha : gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge = raw41709 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41709Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41709 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2198).leftCharge (GramAssembly.key 2198).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2198, Integer.Sparse.eval]
  ring

theorem keyMoment2199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2199) =
      Integer.Sparse.eval keyMomentRow2199 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2282) := by
    have ha : gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge = raw41710 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41710Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41710 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4872) := by
    have ha : gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge = raw41711 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41711Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41711 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2199).leftCharge (GramAssembly.key 2199).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2199, Integer.Sparse.eval]
  ring

theorem keyMoment2200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2200) =
      Integer.Sparse.eval keyMomentRow2200 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2163) := by
    have ha : gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge = raw41712 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41712Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41712 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4694) := by
    have ha : gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge = raw41713 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41713Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41713 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2200).leftCharge (GramAssembly.key 2200).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2200, Integer.Sparse.eval]
  ring

theorem keyMoment2201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2201) =
      Integer.Sparse.eval keyMomentRow2201 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2221) := by
    have ha : gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge = raw41714 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41714Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41714 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4819) := by
    have ha : gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge = raw41715 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41715Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41715 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2201).leftCharge (GramAssembly.key 2201).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2201, Integer.Sparse.eval]
  ring

theorem keyMoment2202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2202) =
      Integer.Sparse.eval keyMomentRow2202 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2220) := by
    have ha : gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge = raw41716 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41716Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41716 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4808) := by
    have ha : gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge = raw41717 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41717Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41717 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2202).leftCharge (GramAssembly.key 2202).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2202, Integer.Sparse.eval]
  ring

theorem keyMoment2203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2203) =
      Integer.Sparse.eval keyMomentRow2203 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2162) := by
    have ha : gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge = raw41718 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41718Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41718 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4687) := by
    have ha : gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge = raw41719 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41719Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41719 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2203).leftCharge (GramAssembly.key 2203).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2203, Integer.Sparse.eval]
  ring

theorem keyMoment2204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2204) =
      Integer.Sparse.eval keyMomentRow2204 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2161) := by
    have ha : gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge = raw41720 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41720Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41720 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4671) := by
    have ha : gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge = raw41721 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41721Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41721 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2204).leftCharge (GramAssembly.key 2204).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2204, Integer.Sparse.eval]
  ring

theorem keyMoment2205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2205) =
      Integer.Sparse.eval keyMomentRow2205 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2180) := by
    have ha : gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge = raw41722 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41722Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41722 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4702) := by
    have ha : gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge = raw41723 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41723Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41723 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2205).leftCharge (GramAssembly.key 2205).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2205, Integer.Sparse.eval]
  ring

theorem keyMoment2206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2206) =
      Integer.Sparse.eval keyMomentRow2206 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2220) := by
    have ha : gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge = raw41724 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41724Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41724 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4808) := by
    have ha : gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge = raw41725 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41725Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41725 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2206).leftCharge (GramAssembly.key 2206).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2206, Integer.Sparse.eval]
  ring

theorem keyMoment2207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2207) =
      Integer.Sparse.eval keyMomentRow2207 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2283) := by
    have ha : gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge = raw41726 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41726Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41726 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4886) := by
    have ha : gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge = raw41727 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41727Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41727 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2207).leftCharge (GramAssembly.key 2207).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2207, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

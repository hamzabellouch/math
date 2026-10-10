import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical326

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2240) =
      Integer.Sparse.eval keyMomentRow2240 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2246) := by
    have ha : gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge = raw41792 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41792Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41792 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4879) := by
    have ha : gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge = raw41793 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41793Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41793 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2240, Integer.Sparse.eval]
  ring

theorem keyMoment2241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2241) =
      Integer.Sparse.eval keyMomentRow2241 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2239) := by
    have ha : gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge = raw41794 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41794Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41794 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4697) := by
    have ha : gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge = raw41795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41795 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2241, Integer.Sparse.eval]
  ring

theorem keyMoment2242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2242) =
      Integer.Sparse.eval keyMomentRow2242 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2192) := by
    have ha : gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge = raw41796 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41796Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41796 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4815) := by
    have ha : gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge = raw41797 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41797Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41797 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2242, Integer.Sparse.eval]
  ring

theorem keyMoment2243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2243) =
      Integer.Sparse.eval keyMomentRow2243 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2189) := by
    have ha : gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge = raw41798 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41798Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41798 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4771) := by
    have ha : gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge = raw41799 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41799Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41799 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2243, Integer.Sparse.eval]
  ring

theorem keyMoment2244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2244) =
      Integer.Sparse.eval keyMomentRow2244 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2140) := by
    have ha : gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge = raw41800 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41800Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41800 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4663) := by
    have ha : gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge = raw41801 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41801Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41801 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2244, Integer.Sparse.eval]
  ring

theorem keyMoment2245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2245) =
      Integer.Sparse.eval keyMomentRow2245 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2238) := by
    have ha : gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge = raw41802 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41802Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41802 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4696) := by
    have ha : gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge = raw41803 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41803Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41803 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2245, Integer.Sparse.eval]
  ring

theorem keyMoment2246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2246) =
      Integer.Sparse.eval keyMomentRow2246 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2240) := by
    have ha : gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge = raw41804 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41804Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41804 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4851) := by
    have ha : gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge = raw41805 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41805Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41805 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2246, Integer.Sparse.eval]
  ring

theorem keyMoment2247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2247) =
      Integer.Sparse.eval keyMomentRow2247 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2267) := by
    have ha : gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge = raw41806 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41806Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41806 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4881) := by
    have ha : gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge = raw41807 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41807Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41807 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2247, Integer.Sparse.eval]
  ring

theorem keyMoment2248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2248) =
      Integer.Sparse.eval keyMomentRow2248 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2258) := by
    have ha : gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge = raw41808 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41808Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41808 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4560) := by
    have ha : gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge = raw41809 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41809Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41809 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2248, Integer.Sparse.eval]
  ring

theorem keyMoment2249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2249) =
      Integer.Sparse.eval keyMomentRow2249 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2207) := by
    have ha : gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge = raw41810 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41810Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41810 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4817) := by
    have ha : gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge = raw41811 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41811Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41811 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2249, Integer.Sparse.eval]
  ring

theorem keyMoment2250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2250) =
      Integer.Sparse.eval keyMomentRow2250 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2200) := by
    have ha : gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge = raw41812 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41812Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41812 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4552) := by
    have ha : gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge = raw41813 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41813Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41813 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2250, Integer.Sparse.eval]
  ring

theorem keyMoment2251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2251) =
      Integer.Sparse.eval keyMomentRow2251 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2149) := by
    have ha : gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge = raw41814 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41814Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41814 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4536) := by
    have ha : gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge = raw41815 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41815Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41815 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2251, Integer.Sparse.eval]
  ring

theorem keyMoment2252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2252) =
      Integer.Sparse.eval keyMomentRow2252 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2256) := by
    have ha : gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge = raw41816 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41816Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41816 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4699) := by
    have ha : gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge = raw41817 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41817Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41817 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2252, Integer.Sparse.eval]
  ring

theorem keyMoment2253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2253) =
      Integer.Sparse.eval keyMomentRow2253 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2259) := by
    have ha : gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge = raw41818 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41818Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41818 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4853) := by
    have ha : gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge = raw41819 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41819Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41819 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2253, Integer.Sparse.eval]
  ring

theorem keyMoment2254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2254) =
      Integer.Sparse.eval keyMomentRow2254 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2257) := by
    have ha : gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge = raw41820 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41820Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41820 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4701) := by
    have ha : gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge = raw41821 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41821Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41821 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2254, Integer.Sparse.eval]
  ring

theorem keyMoment2255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2255) =
      Integer.Sparse.eval keyMomentRow2255 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2172) := by
    have ha : gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge = raw41822 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41822Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41822 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4532) := by
    have ha : gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge = raw41823 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41823Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41823 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2255, Integer.Sparse.eval]
  ring

theorem keyMoment2256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2256) =
      Integer.Sparse.eval keyMomentRow2256 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2198) := by
    have ha : gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge = raw41824 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41824Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41824 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4772) := by
    have ha : gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge = raw41825 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41825Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41825 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2256, Integer.Sparse.eval]
  ring

theorem keyMoment2257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2257) =
      Integer.Sparse.eval keyMomentRow2257 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2201) := by
    have ha : gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge = raw41826 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41826Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41826 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4792) := by
    have ha : gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge = raw41827 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41827Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41827 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2257, Integer.Sparse.eval]
  ring

theorem keyMoment2258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2258) =
      Integer.Sparse.eval keyMomentRow2258 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2199) := by
    have ha : gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge = raw41828 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41828Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41828 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4774) := by
    have ha : gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge = raw41829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41829 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2258, Integer.Sparse.eval]
  ring

theorem keyMoment2259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2259) =
      Integer.Sparse.eval keyMomentRow2259 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2147) := by
    have ha : gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge = raw41830 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41830Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41830 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4664) := by
    have ha : gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge = raw41831 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41831Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41831 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2259, Integer.Sparse.eval]
  ring

theorem keyMoment2260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2260) =
      Integer.Sparse.eval keyMomentRow2260 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2148) := by
    have ha : gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge = raw41832 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41832Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41832 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4666) := by
    have ha : gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge = raw41833 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41833Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41833 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2260, Integer.Sparse.eval]
  ring

theorem keyMoment2261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2261) =
      Integer.Sparse.eval keyMomentRow2261 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1747) := by
    have ha : gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge = raw41834 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41834Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41834 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4508) := by
    have ha : gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge = raw41835 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41835Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41835 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2261, Integer.Sparse.eval]
  ring

theorem keyMoment2262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2262) =
      Integer.Sparse.eval keyMomentRow2262 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1531) := by
    have ha : gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge = raw41836 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41836Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41836 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4193) := by
    have ha : gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge = raw41837 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41837Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41837 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2262, Integer.Sparse.eval]
  ring

theorem keyMoment2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2263) =
      Integer.Sparse.eval keyMomentRow2263 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1746) := by
    have ha : gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge = raw41838 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41838Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41838 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4478) := by
    have ha : gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge = raw41839 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41839Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41839 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2263, Integer.Sparse.eval]
  ring

theorem keyMoment2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2264) =
      Integer.Sparse.eval keyMomentRow2264 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1530) := by
    have ha : gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge = raw41840 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41840Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41840 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4184) := by
    have ha : gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge = raw41841 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41841Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41841 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2264, Integer.Sparse.eval]
  ring

theorem keyMoment2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2265) =
      Integer.Sparse.eval keyMomentRow2265 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1529) := by
    have ha : gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge = raw41842 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41842Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41842 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4162) := by
    have ha : gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge = raw41843 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41843Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41843 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2265, Integer.Sparse.eval]
  ring

theorem keyMoment2266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2266) =
      Integer.Sparse.eval keyMomentRow2266 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1687) := by
    have ha : gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge = raw41844 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41844Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41844 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4362) := by
    have ha : gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge = raw41845 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41845Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41845 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2266, Integer.Sparse.eval]
  ring

theorem keyMoment2267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2267) =
      Integer.Sparse.eval keyMomentRow2267 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1745) := by
    have ha : gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge = raw41846 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41846Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41846 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4464) := by
    have ha : gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge = raw41847 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41847Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41847 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2267, Integer.Sparse.eval]
  ring

theorem keyMoment2268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2268) =
      Integer.Sparse.eval keyMomentRow2268 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2286) := by
    have ha : gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge = raw41848 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41848Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41848 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4705) := by
    have ha : gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge = raw41849 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41849Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41849 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2268, Integer.Sparse.eval]
  ring

theorem keyMoment2269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2269) =
      Integer.Sparse.eval keyMomentRow2269 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1528) := by
    have ha : gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge = raw41850 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41850Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41850 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4157) := by
    have ha : gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge = raw41851 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41851Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41851 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2269, Integer.Sparse.eval]
  ring

theorem keyMoment2270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2270) =
      Integer.Sparse.eval keyMomentRow2270 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1686) := by
    have ha : gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge = raw41852 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41852Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41852 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4353) := by
    have ha : gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge = raw41853 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41853Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41853 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2270, Integer.Sparse.eval]
  ring

theorem keyMoment2271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2271) =
      Integer.Sparse.eval keyMomentRow2271 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1744) := by
    have ha : gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge = raw41854 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41854Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41854 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4442) := by
    have ha : gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge = raw41855 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41855Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41855 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2271, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

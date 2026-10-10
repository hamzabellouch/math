import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical326

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2208) =
      Integer.Sparse.eval keyMomentRow2208 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2160) := by
    have ha : gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge = raw41728 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41728Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41728 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4667) := by
    have ha : gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge = raw41729 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41729Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41729 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2208, Integer.Sparse.eval]
  ring

theorem keyMoment2209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2209) =
      Integer.Sparse.eval keyMomentRow2209 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2179) := by
    have ha : gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge = raw41730 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41730Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41730 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4765) := by
    have ha : gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge = raw41731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41731 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2209, Integer.Sparse.eval]
  ring

theorem keyMoment2210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2210) =
      Integer.Sparse.eval keyMomentRow2210 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2219) := by
    have ha : gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge = raw41732 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41732Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41732 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4793) := by
    have ha : gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge = raw41733 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41733Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41733 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2210, Integer.Sparse.eval]
  ring

theorem keyMoment2211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2211) =
      Integer.Sparse.eval keyMomentRow2211 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2160) := by
    have ha : gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge = raw41734 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41734Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41734 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4667) := by
    have ha : gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge = raw41735 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41735Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41735 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2211, Integer.Sparse.eval]
  ring

theorem keyMoment2212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2212) =
      Integer.Sparse.eval keyMomentRow2212 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2255) := by
    have ha : gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge = raw41736 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41736Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41736 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4892) := by
    have ha : gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge = raw41737 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41737Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41737 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2212, Integer.Sparse.eval]
  ring

theorem keyMoment2213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2213) =
      Integer.Sparse.eval keyMomentRow2213 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2254) := by
    have ha : gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge = raw41738 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41738Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41738 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4880) := by
    have ha : gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge = raw41739 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41739Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41739 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2213, Integer.Sparse.eval]
  ring

theorem keyMoment2214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2214) =
      Integer.Sparse.eval keyMomentRow2214 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2253) := by
    have ha : gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge = raw41740 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41740Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41740 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4891) := by
    have ha : gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge = raw41741 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41741Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41741 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2214, Integer.Sparse.eval]
  ring

theorem keyMoment2215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2215) =
      Integer.Sparse.eval keyMomentRow2215 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2251) := by
    have ha : gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge = raw41742 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41742Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41742 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4867) := by
    have ha : gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge = raw41743 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41743Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41743 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2215, Integer.Sparse.eval]
  ring

theorem keyMoment2216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2216) =
      Integer.Sparse.eval keyMomentRow2216 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2249) := by
    have ha : gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge = raw41744 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41744Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41744 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4700) := by
    have ha : gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge = raw41745 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41745Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41745 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2216, Integer.Sparse.eval]
  ring

theorem keyMoment2217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2217) =
      Integer.Sparse.eval keyMomentRow2217 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2196) := by
    have ha : gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge = raw41746 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41746Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41746 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4816) := by
    have ha : gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge = raw41747 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41747Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41747 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2217, Integer.Sparse.eval]
  ring

theorem keyMoment2218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2218) =
      Integer.Sparse.eval keyMomentRow2218 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2195) := by
    have ha : gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge = raw41748 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41748Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41748 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4803) := by
    have ha : gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge = raw41749 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41749Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41749 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2218, Integer.Sparse.eval]
  ring

theorem keyMoment2219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2219) =
      Integer.Sparse.eval keyMomentRow2219 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2194) := by
    have ha : gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge = raw41750 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41750Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41750 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4773) := by
    have ha : gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge = raw41751 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41751Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41751 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2219, Integer.Sparse.eval]
  ring

theorem keyMoment2220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2220) =
      Integer.Sparse.eval keyMomentRow2220 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2144) := by
    have ha : gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge = raw41752 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41752Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41752 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4665) := by
    have ha : gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge = raw41753 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41753Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41753 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2220, Integer.Sparse.eval]
  ring

theorem keyMoment2221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2221) =
      Integer.Sparse.eval keyMomentRow2221 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2248) := by
    have ha : gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge = raw41754 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41754Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41754 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4698) := by
    have ha : gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge = raw41755 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41755Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41755 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2221, Integer.Sparse.eval]
  ring

theorem keyMoment2222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2222) =
      Integer.Sparse.eval keyMomentRow2222 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2250) := by
    have ha : gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge = raw41756 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41756Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41756 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4852) := by
    have ha : gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge = raw41757 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41757Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41757 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2222, Integer.Sparse.eval]
  ring

theorem keyMoment2223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2223) =
      Integer.Sparse.eval keyMomentRow2223 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2252) := by
    have ha : gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge = raw41758 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41758Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41758 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge = raw41759 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41759Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41759 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2223, Integer.Sparse.eval]
  ring

theorem keyMoment2224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2224) =
      Integer.Sparse.eval keyMomentRow2224 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2280) := by
    have ha : gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge = raw41760 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41760Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41760 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4884) := by
    have ha : gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge = raw41761 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41761Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41761 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2224, Integer.Sparse.eval]
  ring

theorem keyMoment2225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2225) =
      Integer.Sparse.eval keyMomentRow2225 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2273) := by
    have ha : gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge = raw41762 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41762Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41762 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4704) := by
    have ha : gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge = raw41763 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41763Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41763 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2225, Integer.Sparse.eval]
  ring

theorem keyMoment2226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2226) =
      Integer.Sparse.eval keyMomentRow2226 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2217) := by
    have ha : gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge = raw41764 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41764Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41764 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4821) := by
    have ha : gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge = raw41765 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41765Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41765 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2226, Integer.Sparse.eval]
  ring

theorem keyMoment2227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2227) =
      Integer.Sparse.eval keyMomentRow2227 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2212) := by
    have ha : gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge = raw41766 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41766Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41766 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4776) := by
    have ha : gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge = raw41767 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41767Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41767 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2227, Integer.Sparse.eval]
  ring

theorem keyMoment2228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2228) =
      Integer.Sparse.eval keyMomentRow2228 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2155) := by
    have ha : gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge = raw41768 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41768Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41768 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4669) := by
    have ha : gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge = raw41769 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41769Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41769 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2228, Integer.Sparse.eval]
  ring

theorem keyMoment2229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2229) =
      Integer.Sparse.eval keyMomentRow2229 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2272) := by
    have ha : gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge = raw41770 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41770Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41770 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4703) := by
    have ha : gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge = raw41771 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41771Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41771 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2229, Integer.Sparse.eval]
  ring

theorem keyMoment2230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2230) =
      Integer.Sparse.eval keyMomentRow2230 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2274) := by
    have ha : gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge = raw41772 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41772Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41772 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4856) := by
    have ha : gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge = raw41773 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41773Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41773 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2230, Integer.Sparse.eval]
  ring

theorem keyMoment2231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2231) =
      Integer.Sparse.eval keyMomentRow2231 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2176) := by
    have ha : gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge = raw41774 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41774Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41774 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4756) := by
    have ha : gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge = raw41775 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41775Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41775 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2231, Integer.Sparse.eval]
  ring

theorem keyMoment2232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2232) =
      Integer.Sparse.eval keyMomentRow2232 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2211) := by
    have ha : gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge = raw41776 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41776Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41776 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4775) := by
    have ha : gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge = raw41777 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41777Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41777 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2232, Integer.Sparse.eval]
  ring

theorem keyMoment2233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2233) =
      Integer.Sparse.eval keyMomentRow2233 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2213) := by
    have ha : gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge = raw41778 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41778Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41778 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4795) := by
    have ha : gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge = raw41779 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41779Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41779 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2233, Integer.Sparse.eval]
  ring

theorem keyMoment2234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2234) =
      Integer.Sparse.eval keyMomentRow2234 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2154) := by
    have ha : gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge = raw41780 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41780Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41780 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4668) := by
    have ha : gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge = raw41781 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41781Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41781 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2234, Integer.Sparse.eval]
  ring

theorem keyMoment2235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2235) =
      Integer.Sparse.eval keyMomentRow2235 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2235) := by
    have ha : gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge = raw41782 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41782Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41782 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4886) := by
    have ha : gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge = raw41783 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41783Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41783 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2235, Integer.Sparse.eval]
  ring

theorem keyMoment2236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2236) =
      Integer.Sparse.eval keyMomentRow2236 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2234) := by
    have ha : gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge = raw41784 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41784Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41784 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4878) := by
    have ha : gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge = raw41785 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41785Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41785 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2236, Integer.Sparse.eval]
  ring

theorem keyMoment2237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2237) =
      Integer.Sparse.eval keyMomentRow2237 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2233) := by
    have ha : gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge = raw41786 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41786Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41786 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge = raw41787 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41787Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41787 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2237, Integer.Sparse.eval]
  ring

theorem keyMoment2238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2238) =
      Integer.Sparse.eval keyMomentRow2238 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2232) := by
    have ha : gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge = raw41788 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41788Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41788 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4863) := by
    have ha : gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge = raw41789 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41789Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41789 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2238, Integer.Sparse.eval]
  ring

theorem keyMoment2239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2239) =
      Integer.Sparse.eval keyMomentRow2239 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2231) := by
    have ha : gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge = raw41790 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41790Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41790 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4695) := by
    have ha : gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge = raw41791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41791 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2239, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

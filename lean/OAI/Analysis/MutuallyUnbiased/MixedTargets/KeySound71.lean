import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical327

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2272) =
      Integer.Sparse.eval keyMomentRow2272 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2223) := by
    have ha : gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge = raw41856 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41856Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41856 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4777) := by
    have ha : gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge = raw41857 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41857Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41857 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2272).leftCharge (GramAssembly.key 2272).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2272, Integer.Sparse.eval]
  ring

theorem keyMoment2273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2273) =
      Integer.Sparse.eval keyMomentRow2273 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1685) := by
    have ha : gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge = raw41858 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41858Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41858 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4336) := by
    have ha : gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge = raw41859 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41859Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41859 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2273).leftCharge (GramAssembly.key 2273).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2273, Integer.Sparse.eval]
  ring

theorem keyMoment2274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2274) =
      Integer.Sparse.eval keyMomentRow2274 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2164) := by
    have ha : gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge = raw41860 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41860Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41860 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4670) := by
    have ha : gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge = raw41861 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41861Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41861 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2274).leftCharge (GramAssembly.key 2274).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2274, Integer.Sparse.eval]
  ring

theorem keyMoment2275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2275) =
      Integer.Sparse.eval keyMomentRow2275 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1684) := by
    have ha : gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge = raw41862 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41862Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41862 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4331) := by
    have ha : gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge = raw41863 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41863Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41863 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2275).leftCharge (GramAssembly.key 2275).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2275, Integer.Sparse.eval]
  ring

theorem keyMoment2276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2276) =
      Integer.Sparse.eval keyMomentRow2276 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2181) := by
    have ha : gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge = raw41864 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41864Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41864 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4757) := by
    have ha : gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge = raw41865 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41865Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41865 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2276).leftCharge (GramAssembly.key 2276).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2276, Integer.Sparse.eval]
  ring

theorem keyMoment2277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2277) =
      Integer.Sparse.eval keyMomentRow2277 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1746) := by
    have ha : gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge = raw41866 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41866Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41866 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4478) := by
    have ha : gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge = raw41867 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41867Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41867 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2277).leftCharge (GramAssembly.key 2277).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2277, Integer.Sparse.eval]
  ring

theorem keyMoment2278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2278) =
      Integer.Sparse.eval keyMomentRow2278 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1745) := by
    have ha : gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge = raw41868 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41868Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41868 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4464) := by
    have ha : gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge = raw41869 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41869Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41869 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2278).leftCharge (GramAssembly.key 2278).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2278, Integer.Sparse.eval]
  ring

theorem keyMoment2279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2279) =
      Integer.Sparse.eval keyMomentRow2279 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1743) := by
    have ha : gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge = raw41870 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41870Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41870 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4375) := by
    have ha : gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge = raw41871 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41871Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41871 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2279).leftCharge (GramAssembly.key 2279).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2279, Integer.Sparse.eval]
  ring

theorem keyMoment2280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2280) =
      Integer.Sparse.eval keyMomentRow2280 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1685) := by
    have ha : gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge = raw41872 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41872Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41872 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4336) := by
    have ha : gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge = raw41873 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41873Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41873 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2280).leftCharge (GramAssembly.key 2280).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2280, Integer.Sparse.eval]
  ring

theorem keyMoment2281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2281) =
      Integer.Sparse.eval keyMomentRow2281 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1742) := by
    have ha : gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge = raw41874 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41874Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41874 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4371) := by
    have ha : gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge = raw41875 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41875Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41875 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2281).leftCharge (GramAssembly.key 2281).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2281, Integer.Sparse.eval]
  ring

theorem keyMoment2282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2282) =
      Integer.Sparse.eval keyMomentRow2282 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1744) := by
    have ha : gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge = raw41876 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41876Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41876 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4442) := by
    have ha : gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge = raw41877 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41877Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41877 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2282).leftCharge (GramAssembly.key 2282).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2282, Integer.Sparse.eval]
  ring

theorem keyMoment2283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2283) =
      Integer.Sparse.eval keyMomentRow2283 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1684) := by
    have ha : gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge = raw41878 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41878Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41878 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4331) := by
    have ha : gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge = raw41879 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41879Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41879 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2283).leftCharge (GramAssembly.key 2283).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2283, Integer.Sparse.eval]
  ring

theorem keyMoment2284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2284) =
      Integer.Sparse.eval keyMomentRow2284 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1715) := by
    have ha : gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge = raw41880 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41880Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41880 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4475) := by
    have ha : gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge = raw41881 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41881Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41881 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2284).leftCharge (GramAssembly.key 2284).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2284, Integer.Sparse.eval]
  ring

theorem keyMoment2285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2285) =
      Integer.Sparse.eval keyMomentRow2285 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1714) := by
    have ha : gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge = raw41882 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41882Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41882 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4459) := by
    have ha : gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge = raw41883 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41883Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41883 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2285).leftCharge (GramAssembly.key 2285).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2285, Integer.Sparse.eval]
  ring

theorem keyMoment2286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2286) =
      Integer.Sparse.eval keyMomentRow2286 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1712) := by
    have ha : gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge = raw41884 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41884Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41884 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4368) := by
    have ha : gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge = raw41885 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41885Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41885 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2286).leftCharge (GramAssembly.key 2286).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2286, Integer.Sparse.eval]
  ring

theorem keyMoment2287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2287) =
      Integer.Sparse.eval keyMomentRow2287 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1667) := by
    have ha : gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge = raw41886 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41886Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41886 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4328) := by
    have ha : gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge = raw41887 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41887Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41887 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2287).leftCharge (GramAssembly.key 2287).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2287, Integer.Sparse.eval]
  ring

theorem keyMoment2288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2288) =
      Integer.Sparse.eval keyMomentRow2288 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1711) := by
    have ha : gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge = raw41888 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41888Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41888 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4366) := by
    have ha : gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge = raw41889 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41889Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41889 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2288).leftCharge (GramAssembly.key 2288).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2288, Integer.Sparse.eval]
  ring

theorem keyMoment2289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2289) =
      Integer.Sparse.eval keyMomentRow2289 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1713) := by
    have ha : gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge = raw41890 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41890Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41890 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4439) := by
    have ha : gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge = raw41891 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41891Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41891 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2289).leftCharge (GramAssembly.key 2289).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2289, Integer.Sparse.eval]
  ring

theorem keyMoment2290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2290) =
      Integer.Sparse.eval keyMomentRow2290 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1740) := by
    have ha : gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge = raw41892 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41892Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41892 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4480) := by
    have ha : gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge = raw41893 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41893Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41893 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2290).leftCharge (GramAssembly.key 2290).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2290, Integer.Sparse.eval]
  ring

theorem keyMoment2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2291) =
      Integer.Sparse.eval keyMomentRow2291 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1735) := by
    have ha : gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge = raw41894 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41894Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41894 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4373) := by
    have ha : gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge = raw41895 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41895Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41895 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2291).leftCharge (GramAssembly.key 2291).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2291, Integer.Sparse.eval]
  ring

theorem keyMoment2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2292) =
      Integer.Sparse.eval keyMomentRow2292 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1679) := by
    have ha : gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge = raw41896 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41896Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41896 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4334) := by
    have ha : gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge = raw41897 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41897Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41897 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2292).leftCharge (GramAssembly.key 2292).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2292, Integer.Sparse.eval]
  ring

theorem keyMoment2293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2293) =
      Integer.Sparse.eval keyMomentRow2293 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1734) := by
    have ha : gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge = raw41898 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41898Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41898 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4372) := by
    have ha : gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge = raw41899 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41899Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41899 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2293).leftCharge (GramAssembly.key 2293).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2293, Integer.Sparse.eval]
  ring

theorem keyMoment2294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2294) =
      Integer.Sparse.eval keyMomentRow2294 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1736) := by
    have ha : gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge = raw41900 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41900Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41900 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4444) := by
    have ha : gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge = raw41901 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41901Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41901 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2294).leftCharge (GramAssembly.key 2294).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2294, Integer.Sparse.eval]
  ring

theorem keyMoment2295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2295) =
      Integer.Sparse.eval keyMomentRow2295 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1678) := by
    have ha : gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge = raw41902 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41902Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41902 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4332) := by
    have ha : gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge = raw41903 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41903Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41903 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2295).leftCharge (GramAssembly.key 2295).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2295, Integer.Sparse.eval]
  ring

theorem keyMoment2296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2296) =
      Integer.Sparse.eval keyMomentRow2296 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1699) := by
    have ha : gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge = raw41904 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41904Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41904 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4473) := by
    have ha : gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge = raw41905 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41905Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41905 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2296).leftCharge (GramAssembly.key 2296).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2296, Integer.Sparse.eval]
  ring

theorem keyMoment2297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2297) =
      Integer.Sparse.eval keyMomentRow2297 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1697) := by
    have ha : gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge = raw41906 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41906Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41906 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4363) := by
    have ha : gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge = raw41907 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41907Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41907 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2297).leftCharge (GramAssembly.key 2297).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2297, Integer.Sparse.eval]
  ring

theorem keyMoment2298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2298) =
      Integer.Sparse.eval keyMomentRow2298 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1709) := by
    have ha : gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge = raw41908 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41908Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41908 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4474) := by
    have ha : gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge = raw41909 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41909Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41909 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2298).leftCharge (GramAssembly.key 2298).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2298, Integer.Sparse.eval]
  ring

theorem keyMoment2299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2299) =
      Integer.Sparse.eval keyMomentRow2299 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1704) := by
    have ha : gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge = raw41910 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41910Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41910 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4365) := by
    have ha : gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge = raw41911 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41911Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41911 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2299).leftCharge (GramAssembly.key 2299).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2299, Integer.Sparse.eval]
  ring

theorem keyMoment2300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2300) =
      Integer.Sparse.eval keyMomentRow2300 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1703) := by
    have ha : gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge = raw41912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41912 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4364) := by
    have ha : gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge = raw41913 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41913Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41913 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2300).leftCharge (GramAssembly.key 2300).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2300, Integer.Sparse.eval]
  ring

theorem keyMoment2301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2301) =
      Integer.Sparse.eval keyMomentRow2301 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1729) := by
    have ha : gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge = raw41914 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41914Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41914 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4476) := by
    have ha : gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge = raw41915 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41915Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41915 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2301).leftCharge (GramAssembly.key 2301).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2301, Integer.Sparse.eval]
  ring

theorem keyMoment2302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2302) =
      Integer.Sparse.eval keyMomentRow2302 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1722) := by
    have ha : gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge = raw41916 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41916Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41916 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4370) := by
    have ha : gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge = raw41917 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41917Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41917 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2302).leftCharge (GramAssembly.key 2302).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2302, Integer.Sparse.eval]
  ring

theorem keyMoment2303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2303) =
      Integer.Sparse.eval keyMomentRow2303 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1672) := by
    have ha : gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge = raw41918 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41918Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41918 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4330) := by
    have ha : gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge = raw41919 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41919Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41919 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2303).leftCharge (GramAssembly.key 2303).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2303, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

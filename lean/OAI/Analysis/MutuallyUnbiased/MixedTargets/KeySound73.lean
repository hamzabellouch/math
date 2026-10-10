import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical328

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2336) =
      Integer.Sparse.eval keyMomentRow2336 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3109) := by
    have ha : gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge = raw41984 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41984Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41984 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5271) := by
    have ha : gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge = raw41985 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41985Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41985 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2336).leftCharge (GramAssembly.key 2336).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2336, Integer.Sparse.eval]
  ring

theorem keyMoment2337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2337) =
      Integer.Sparse.eval keyMomentRow2337 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3039) := by
    have ha : gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge = raw41986 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41986Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41986 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge = raw41987 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41987Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41987 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2337).leftCharge (GramAssembly.key 2337).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2337, Integer.Sparse.eval]
  ring

theorem keyMoment2338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2338) =
      Integer.Sparse.eval keyMomentRow2338 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge = raw41988 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41988Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41988 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge = raw41989 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41989Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41989 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2338).leftCharge (GramAssembly.key 2338).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2338, Integer.Sparse.eval]
  ring

theorem keyMoment2339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2339) =
      Integer.Sparse.eval keyMomentRow2339 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3088) := by
    have ha : gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge = raw41990 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41990Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41990 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5259) := by
    have ha : gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge = raw41991 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41991Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41991 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2339).leftCharge (GramAssembly.key 2339).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2339, Integer.Sparse.eval]
  ring

theorem keyMoment2340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2340) =
      Integer.Sparse.eval keyMomentRow2340 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3111) := by
    have ha : gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge = raw41992 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41992Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41992 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5273) := by
    have ha : gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge = raw41993 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41993Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41993 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2340).leftCharge (GramAssembly.key 2340).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2340, Integer.Sparse.eval]
  ring

theorem keyMoment2341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2341) =
      Integer.Sparse.eval keyMomentRow2341 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge = raw41994 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41994Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41994 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge = raw41995 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41995Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41995 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2341).leftCharge (GramAssembly.key 2341).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2341, Integer.Sparse.eval]
  ring

theorem keyMoment2342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2342) =
      Integer.Sparse.eval keyMomentRow2342 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3065) := by
    have ha : gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge = raw41996 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41996Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41996 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5250) := by
    have ha : gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge = raw41997 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41997Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41997 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2342).leftCharge (GramAssembly.key 2342).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2342, Integer.Sparse.eval]
  ring

theorem keyMoment2343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2343) =
      Integer.Sparse.eval keyMomentRow2343 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3087) := by
    have ha : gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge = raw41998 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41998Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41998 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5257) := by
    have ha : gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge = raw41999 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41999Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41999 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2343).leftCharge (GramAssembly.key 2343).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2343, Integer.Sparse.eval]
  ring

theorem keyMoment2344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2344) =
      Integer.Sparse.eval keyMomentRow2344 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge = raw42000 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42000Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42000 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge = raw42001 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42001Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42001 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2344).leftCharge (GramAssembly.key 2344).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2344, Integer.Sparse.eval]
  ring

theorem keyMoment2345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2345) =
      Integer.Sparse.eval keyMomentRow2345 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3103) := by
    have ha : gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge = raw42002 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42002Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42002 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5291) := by
    have ha : gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge = raw42003 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42003Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42003 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2345).leftCharge (GramAssembly.key 2345).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2345, Integer.Sparse.eval]
  ring

theorem keyMoment2346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2346) =
      Integer.Sparse.eval keyMomentRow2346 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3119) := by
    have ha : gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge = raw42004 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42004Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42004 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5304) := by
    have ha : gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge = raw42005 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42005Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42005 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2346).leftCharge (GramAssembly.key 2346).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2346, Integer.Sparse.eval]
  ring

theorem keyMoment2347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2347) =
      Integer.Sparse.eval keyMomentRow2347 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge = raw42006 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42006Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42006 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge = raw42007 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42007Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42007 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2347).leftCharge (GramAssembly.key 2347).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2347, Integer.Sparse.eval]
  ring

theorem keyMoment2348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2348) =
      Integer.Sparse.eval keyMomentRow2348 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge = raw42008 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42008Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42008 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge = raw42009 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42009Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42009 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2348).leftCharge (GramAssembly.key 2348).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2348, Integer.Sparse.eval]
  ring

theorem keyMoment2349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2349) =
      Integer.Sparse.eval keyMomentRow2349 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge = raw42010 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42010Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42010 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge = raw42011 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42011Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42011 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2349).leftCharge (GramAssembly.key 2349).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2349, Integer.Sparse.eval]
  ring

theorem keyMoment2350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2350) =
      Integer.Sparse.eval keyMomentRow2350 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3099) := by
    have ha : gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge = raw42012 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42012Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42012 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5290) := by
    have ha : gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge = raw42013 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42013Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42013 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2350).leftCharge (GramAssembly.key 2350).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2350, Integer.Sparse.eval]
  ring

theorem keyMoment2351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2351) =
      Integer.Sparse.eval keyMomentRow2351 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge = raw42014 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42014Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42014 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge = raw42015 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42015Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42015 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2351).leftCharge (GramAssembly.key 2351).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2351, Integer.Sparse.eval]
  ring

theorem keyMoment2352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2352) =
      Integer.Sparse.eval keyMomentRow2352 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge = raw42016 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42016Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42016 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge = raw42017 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42017Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42017 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2352).leftCharge (GramAssembly.key 2352).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2352, Integer.Sparse.eval]
  ring

theorem keyMoment2353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2353) =
      Integer.Sparse.eval keyMomentRow2353 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge = raw42018 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42018Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42018 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge = raw42019 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42019Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42019 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2353).leftCharge (GramAssembly.key 2353).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2353, Integer.Sparse.eval]
  ring

theorem keyMoment2354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2354) =
      Integer.Sparse.eval keyMomentRow2354 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1) := by
    have ha : gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge = raw42020 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42020Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42020 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4084) := by
    have ha : gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge = raw42021 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42021Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42021 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2354).leftCharge (GramAssembly.key 2354).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2354, Integer.Sparse.eval]
  ring

theorem keyMoment2355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2355) =
      Integer.Sparse.eval keyMomentRow2355 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3112) := by
    have ha : gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge = raw42022 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42022Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42022 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5274) := by
    have ha : gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge = raw42023 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42023Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42023 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2355).leftCharge (GramAssembly.key 2355).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2355, Integer.Sparse.eval]
  ring

theorem keyMoment2356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2356) =
      Integer.Sparse.eval keyMomentRow2356 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4) := by
    have ha : gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge = raw42024 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42024Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42024 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4092) := by
    have ha : gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge = raw42025 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42025Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42025 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2356).leftCharge (GramAssembly.key 2356).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2356, Integer.Sparse.eval]
  ring

theorem keyMoment2357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2357) =
      Integer.Sparse.eval keyMomentRow2357 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4006) := by
    have ha : gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge = raw42026 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42026Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42026 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5413) := by
    have ha : gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge = raw42027 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42027Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42027 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2357).leftCharge (GramAssembly.key 2357).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2357, Integer.Sparse.eval]
  ring

theorem keyMoment2358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2358) =
      Integer.Sparse.eval keyMomentRow2358 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2776) := by
    have ha : gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge = raw42028 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42028Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42028 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5302) := by
    have ha : gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge = raw42029 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42029Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42029 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2358).leftCharge (GramAssembly.key 2358).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2358, Integer.Sparse.eval]
  ring

theorem keyMoment2359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2359) =
      Integer.Sparse.eval keyMomentRow2359 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4035) := by
    have ha : gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge = raw42030 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42030Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42030 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5409) := by
    have ha : gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge = raw42031 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42031Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42031 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2359).leftCharge (GramAssembly.key 2359).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2359, Integer.Sparse.eval]
  ring

theorem keyMoment2360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2360) =
      Integer.Sparse.eval keyMomentRow2360 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3996) := by
    have ha : gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge = raw42032 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42032Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42032 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5410) := by
    have ha : gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge = raw42033 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42033Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42033 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2360).leftCharge (GramAssembly.key 2360).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2360, Integer.Sparse.eval]
  ring

theorem keyMoment2361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2361) =
      Integer.Sparse.eval keyMomentRow2361 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3883) := by
    have ha : gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge = raw42034 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42034Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42034 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5411) := by
    have ha : gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge = raw42035 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42035Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42035 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2361).leftCharge (GramAssembly.key 2361).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2361, Integer.Sparse.eval]
  ring

theorem keyMoment2362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2362) =
      Integer.Sparse.eval keyMomentRow2362 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3856) := by
    have ha : gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge = raw42036 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42036Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42036 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5412) := by
    have ha : gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge = raw42037 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42037Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42037 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2362).leftCharge (GramAssembly.key 2362).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2362, Integer.Sparse.eval]
  ring

theorem keyMoment2363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2363) =
      Integer.Sparse.eval keyMomentRow2363 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2753) := by
    have ha : gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge = raw42038 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42038Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42038 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5284) := by
    have ha : gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge = raw42039 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42039Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42039 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2363).leftCharge (GramAssembly.key 2363).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2363, Integer.Sparse.eval]
  ring

theorem keyMoment2364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2364) =
      Integer.Sparse.eval keyMomentRow2364 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3996) := by
    have ha : gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge = raw42040 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42040Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42040 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5410) := by
    have ha : gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge = raw42041 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42041Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42041 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2364).leftCharge (GramAssembly.key 2364).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2364, Integer.Sparse.eval]
  ring

theorem keyMoment2365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2365) =
      Integer.Sparse.eval keyMomentRow2365 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3) := by
    have ha : gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge = raw42042 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42042Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42042 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4091) := by
    have ha : gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge = raw42043 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42043Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42043 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2365).leftCharge (GramAssembly.key 2365).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2365, Integer.Sparse.eval]
  ring

theorem keyMoment2366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2366) =
      Integer.Sparse.eval keyMomentRow2366 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3847) := by
    have ha : gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge = raw42044 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42044Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42044 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5406) := by
    have ha : gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge = raw42045 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42045Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42045 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2366).leftCharge (GramAssembly.key 2366).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2366, Integer.Sparse.eval]
  ring

theorem keyMoment2367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2367) =
      Integer.Sparse.eval keyMomentRow2367 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3977) := by
    have ha : gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge = raw42046 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42046Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42046 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5405) := by
    have ha : gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge = raw42047 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42047Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42047 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2367).leftCharge (GramAssembly.key 2367).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2367, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

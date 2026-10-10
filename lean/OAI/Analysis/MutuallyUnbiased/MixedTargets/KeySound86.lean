import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys86
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical334

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2752) =
      Integer.Sparse.eval keyMomentRow2752 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3296) := by
    have ha : gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge = raw42816 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42816Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42816 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4607) := by
    have ha : gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge = raw42817 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42817Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42817 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2752).leftCharge (GramAssembly.key 2752).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2752, Integer.Sparse.eval]
  ring

theorem keyMoment2753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2753) =
      Integer.Sparse.eval keyMomentRow2753 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3289) := by
    have ha : gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge = raw42818 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42818Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42818 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4599) := by
    have ha : gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge = raw42819 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42819Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42819 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2753).leftCharge (GramAssembly.key 2753).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2753, Integer.Sparse.eval]
  ring

theorem keyMoment2754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2754) =
      Integer.Sparse.eval keyMomentRow2754 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3302) := by
    have ha : gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge = raw42820 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42820Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42820 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4609) := by
    have ha : gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge = raw42821 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42821Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42821 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2754).leftCharge (GramAssembly.key 2754).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2754, Integer.Sparse.eval]
  ring

theorem keyMoment2755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2755) =
      Integer.Sparse.eval keyMomentRow2755 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3294) := by
    have ha : gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge = raw42822 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42822Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42822 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4603) := by
    have ha : gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge = raw42823 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42823Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42823 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2755).leftCharge (GramAssembly.key 2755).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2755, Integer.Sparse.eval]
  ring

theorem keyMoment2756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2756) =
      Integer.Sparse.eval keyMomentRow2756 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3295) := by
    have ha : gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge = raw42824 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42824Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42824 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4592) := by
    have ha : gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge = raw42825 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42825Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42825 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2756).leftCharge (GramAssembly.key 2756).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2756, Integer.Sparse.eval]
  ring

theorem keyMoment2757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2757) =
      Integer.Sparse.eval keyMomentRow2757 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3288) := by
    have ha : gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge = raw42826 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42826Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42826 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4589) := by
    have ha : gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge = raw42827 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42827Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42827 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2757).leftCharge (GramAssembly.key 2757).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2757, Integer.Sparse.eval]
  ring

theorem keyMoment2758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2758) =
      Integer.Sparse.eval keyMomentRow2758 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3288) := by
    have ha : gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge = raw42828 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42828Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42828 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4589) := by
    have ha : gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge = raw42829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42829 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2758).leftCharge (GramAssembly.key 2758).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2758, Integer.Sparse.eval]
  ring

theorem keyMoment2759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2759) =
      Integer.Sparse.eval keyMomentRow2759 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3291) := by
    have ha : gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge = raw42830 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42830Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42830 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4591) := by
    have ha : gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge = raw42831 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42831Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42831 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2759).leftCharge (GramAssembly.key 2759).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2759, Integer.Sparse.eval]
  ring

theorem keyMoment2760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2760) =
      Integer.Sparse.eval keyMomentRow2760 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3290) := by
    have ha : gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge = raw42832 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42832Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42832 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4590) := by
    have ha : gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge = raw42833 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42833Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42833 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2760).leftCharge (GramAssembly.key 2760).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2760, Integer.Sparse.eval]
  ring

theorem keyMoment2761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2761) =
      Integer.Sparse.eval keyMomentRow2761 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3298) := by
    have ha : gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge = raw42834 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42834Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42834 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4594) := by
    have ha : gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge = raw42835 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42835Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42835 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2761).leftCharge (GramAssembly.key 2761).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2761, Integer.Sparse.eval]
  ring

theorem keyMoment2762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2762) =
      Integer.Sparse.eval keyMomentRow2762 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3291) := by
    have ha : gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge = raw42836 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42836Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42836 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4591) := by
    have ha : gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge = raw42837 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42837Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42837 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2762).leftCharge (GramAssembly.key 2762).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2762, Integer.Sparse.eval]
  ring

theorem keyMoment2763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2763) =
      Integer.Sparse.eval keyMomentRow2763 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3297) := by
    have ha : gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge = raw42838 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42838Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42838 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4593) := by
    have ha : gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge = raw42839 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42839Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42839 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2763).leftCharge (GramAssembly.key 2763).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2763, Integer.Sparse.eval]
  ring

theorem keyMoment2764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2764) =
      Integer.Sparse.eval keyMomentRow2764 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2149) := by
    have ha : gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge = raw42840 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42840Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42840 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4536) := by
    have ha : gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge = raw42841 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42841Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42841 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2764).leftCharge (GramAssembly.key 2764).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2764, Integer.Sparse.eval]
  ring

theorem keyMoment2765 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2765) =
      Integer.Sparse.eval keyMomentRow2765 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2172) := by
    have ha : gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge = raw42842 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42842Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42842 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4532) := by
    have ha : gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge = raw42843 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42843Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42843 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2765).leftCharge (GramAssembly.key 2765).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2765, Integer.Sparse.eval]
  ring

theorem keyMoment2766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2766) =
      Integer.Sparse.eval keyMomentRow2766 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3258) := by
    have ha : gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge = raw42844 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42844Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42844 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4529) := by
    have ha : gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge = raw42845 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42845Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42845 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2766).leftCharge (GramAssembly.key 2766).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2766, Integer.Sparse.eval]
  ring

theorem keyMoment2767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2767) =
      Integer.Sparse.eval keyMomentRow2767 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3268) := by
    have ha : gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge = raw42846 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42846Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42846 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4534) := by
    have ha : gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge = raw42847 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42847Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42847 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2767).leftCharge (GramAssembly.key 2767).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2767, Integer.Sparse.eval]
  ring

theorem keyMoment2768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2768) =
      Integer.Sparse.eval keyMomentRow2768 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3267) := by
    have ha : gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge = raw42848 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42848Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42848 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4533) := by
    have ha : gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge = raw42849 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42849Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42849 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2768).leftCharge (GramAssembly.key 2768).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2768, Integer.Sparse.eval]
  ring

theorem keyMoment2769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2769) =
      Integer.Sparse.eval keyMomentRow2769 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3255) := by
    have ha : gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge = raw42850 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42850Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42850 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4527) := by
    have ha : gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge = raw42851 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42851Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42851 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2769).leftCharge (GramAssembly.key 2769).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2769, Integer.Sparse.eval]
  ring

theorem keyMoment2770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2770) =
      Integer.Sparse.eval keyMomentRow2770 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3262) := by
    have ha : gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge = raw42852 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42852Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42852 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4531) := by
    have ha : gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge = raw42853 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42853Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42853 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2770).leftCharge (GramAssembly.key 2770).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2770, Integer.Sparse.eval]
  ring

theorem keyMoment2771 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2771) =
      Integer.Sparse.eval keyMomentRow2771 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3260) := by
    have ha : gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge = raw42854 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42854Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42854 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4528) := by
    have ha : gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge = raw42855 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42855Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42855 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2771).leftCharge (GramAssembly.key 2771).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2771, Integer.Sparse.eval]
  ring

theorem keyMoment2772 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2772) =
      Integer.Sparse.eval keyMomentRow2772 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3261) := by
    have ha : gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge = raw42856 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42856Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42856 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4530) := by
    have ha : gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge = raw42857 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42857Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42857 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2772).leftCharge (GramAssembly.key 2772).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2772, Integer.Sparse.eval]
  ring

theorem keyMoment2773 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2773) =
      Integer.Sparse.eval keyMomentRow2773 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1516) := by
    have ha : gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge = raw42858 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42858Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42858 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4156) := by
    have ha : gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge = raw42859 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42859Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42859 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2773).leftCharge (GramAssembly.key 2773).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2773, Integer.Sparse.eval]
  ring

theorem keyMoment2774 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2774) =
      Integer.Sparse.eval keyMomentRow2774 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1672) := by
    have ha : gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge = raw42860 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42860Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42860 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4330) := by
    have ha : gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge = raw42861 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42861Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42861 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2774).leftCharge (GramAssembly.key 2774).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2774, Integer.Sparse.eval]
  ring

theorem keyMoment2775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2775) =
      Integer.Sparse.eval keyMomentRow2775 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3272) := by
    have ha : gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge = raw42862 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42862Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42862 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4535) := by
    have ha : gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge = raw42863 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42863Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42863 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2775).leftCharge (GramAssembly.key 2775).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2775, Integer.Sparse.eval]
  ring

theorem keyMoment2776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2776) =
      Integer.Sparse.eval keyMomentRow2776 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2755) := by
    have ha : gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge = raw42864 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42864Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42864 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4890) := by
    have ha : gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge = raw42865 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42865Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42865 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2776).leftCharge (GramAssembly.key 2776).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2776, Integer.Sparse.eval]
  ring

theorem keyMoment2777 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2777) =
      Integer.Sparse.eval keyMomentRow2777 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2753) := by
    have ha : gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge = raw42866 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42866Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42866 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5284) := by
    have ha : gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge = raw42867 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42867Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42867 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2777).leftCharge (GramAssembly.key 2777).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2777, Integer.Sparse.eval]
  ring

theorem keyMoment2778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2778) =
      Integer.Sparse.eval keyMomentRow2778 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge = raw42868 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42868Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42868 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge = raw42869 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42869Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42869 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2778).leftCharge (GramAssembly.key 2778).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2778, Integer.Sparse.eval]
  ring

theorem keyMoment2779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2779) =
      Integer.Sparse.eval keyMomentRow2779 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge = raw42870 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42870Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42870 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge = raw42871 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42871Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42871 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2779).leftCharge (GramAssembly.key 2779).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2779, Integer.Sparse.eval]
  ring

theorem keyMoment2780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2780) =
      Integer.Sparse.eval keyMomentRow2780 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2662) := by
    have ha : gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge = raw42872 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42872Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42872 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5220) := by
    have ha : gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge = raw42873 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42873Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42873 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2780).leftCharge (GramAssembly.key 2780).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2780, Integer.Sparse.eval]
  ring

theorem keyMoment2781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2781) =
      Integer.Sparse.eval keyMomentRow2781 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2661) := by
    have ha : gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge = raw42874 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42874Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42874 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5219) := by
    have ha : gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge = raw42875 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42875Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42875 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2781).leftCharge (GramAssembly.key 2781).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2781, Integer.Sparse.eval]
  ring

theorem keyMoment2782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2782) =
      Integer.Sparse.eval keyMomentRow2782 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge = raw42876 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42876Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42876 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge = raw42877 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42877Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42877 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2782).leftCharge (GramAssembly.key 2782).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2782, Integer.Sparse.eval]
  ring

theorem keyMoment2783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2783) =
      Integer.Sparse.eval keyMomentRow2783 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge = raw42878 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42878Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42878 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge = raw42879 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42879Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42879 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2783).leftCharge (GramAssembly.key 2783).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2783, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

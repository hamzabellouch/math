import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical334

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2720) =
      Integer.Sparse.eval keyMomentRow2720 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3475) := by
    have ha : gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge = raw42752 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42752Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42752 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4965) := by
    have ha : gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge = raw42753 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42753Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42753 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2720).leftCharge (GramAssembly.key 2720).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2720, Integer.Sparse.eval]; ring

theorem keyMoment2721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2721) =
      Integer.Sparse.eval keyMomentRow2721 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3452) := by
    have ha : gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge = raw42754 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42754Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42754 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4954) := by
    have ha : gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge = raw42755 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42755Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42755 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2721).leftCharge (GramAssembly.key 2721).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2721, Integer.Sparse.eval]; ring

theorem keyMoment2722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2722) =
      Integer.Sparse.eval keyMomentRow2722 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3474) := by
    have ha : gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge = raw42756 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42756Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42756 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5044) := by
    have ha : gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge = raw42757 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42757Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42757 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2722).leftCharge (GramAssembly.key 2722).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2722, Integer.Sparse.eval]; ring

theorem keyMoment2723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2723) =
      Integer.Sparse.eval keyMomentRow2723 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3476) := by
    have ha : gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge = raw42758 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42758Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42758 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5067) := by
    have ha : gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge = raw42759 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42759Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42759 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2723).leftCharge (GramAssembly.key 2723).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2723, Integer.Sparse.eval]; ring

theorem keyMoment2724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2724) =
      Integer.Sparse.eval keyMomentRow2724 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3461) := by
    have ha : gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge = raw42760 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42760Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42760 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5085) := by
    have ha : gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge = raw42761 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42761Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42761 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2724).leftCharge (GramAssembly.key 2724).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2724, Integer.Sparse.eval]; ring

theorem keyMoment2725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2725) =
      Integer.Sparse.eval keyMomentRow2725 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3458) := by
    have ha : gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge = raw42762 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42762Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42762 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5041) := by
    have ha : gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge = raw42763 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42763Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42763 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2725).leftCharge (GramAssembly.key 2725).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2725, Integer.Sparse.eval]; ring

theorem keyMoment2726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2726) =
      Integer.Sparse.eval keyMomentRow2726 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3472) := by
    have ha : gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge = raw42764 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42764Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42764 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5087) := by
    have ha : gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge = raw42765 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42765Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42765 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2726).leftCharge (GramAssembly.key 2726).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2726, Integer.Sparse.eval]; ring

theorem keyMoment2727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2727) =
      Integer.Sparse.eval keyMomentRow2727 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3266) := by
    have ha : gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge = raw42766 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42766Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42766 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4547) := by
    have ha : gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge = raw42767 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42767Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42767 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2727).leftCharge (GramAssembly.key 2727).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2727, Integer.Sparse.eval]; ring

theorem keyMoment2728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2728) =
      Integer.Sparse.eval keyMomentRow2728 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3260) := by
    have ha : gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge = raw42768 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42768Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42768 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4528) := by
    have ha : gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge = raw42769 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42769Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42769 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2728).leftCharge (GramAssembly.key 2728).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2728, Integer.Sparse.eval]; ring

theorem keyMoment2729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2729) =
      Integer.Sparse.eval keyMomentRow2729 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3451) := by
    have ha : gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge = raw42770 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42770Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42770 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5034) := by
    have ha : gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge = raw42771 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42771Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42771 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2729).leftCharge (GramAssembly.key 2729).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2729, Integer.Sparse.eval]; ring

theorem keyMoment2730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2730) =
      Integer.Sparse.eval keyMomentRow2730 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3466) := by
    have ha : gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge = raw42772 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42772Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42772 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5065) := by
    have ha : gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge = raw42773 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42773Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42773 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2730).leftCharge (GramAssembly.key 2730).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2730, Integer.Sparse.eval]; ring

theorem keyMoment2731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2731) =
      Integer.Sparse.eval keyMomentRow2731 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3465) := by
    have ha : gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge = raw42774 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42774Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42774 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5043) := by
    have ha : gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge = raw42775 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42775Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42775 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2731).leftCharge (GramAssembly.key 2731).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2731, Integer.Sparse.eval]; ring

theorem keyMoment2732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2732) =
      Integer.Sparse.eval keyMomentRow2732 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1729) := by
    have ha : gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge = raw42776 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42776Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42776 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4476) := by
    have ha : gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge = raw42777 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42777Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42777 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2732).leftCharge (GramAssembly.key 2732).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2732, Integer.Sparse.eval]; ring

theorem keyMoment2733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2733) =
      Integer.Sparse.eval keyMomentRow2733 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1520) := by
    have ha : gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge = raw42778 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42778Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42778 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4178) := by
    have ha : gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge = raw42779 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42779Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42779 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2733).leftCharge (GramAssembly.key 2733).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2733, Integer.Sparse.eval]; ring

theorem keyMoment2734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2734) =
      Integer.Sparse.eval keyMomentRow2734 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1514) := by
    have ha : gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge = raw42780 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42780Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42780 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4153) := by
    have ha : gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge = raw42781 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42781Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42781 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2734).leftCharge (GramAssembly.key 2734).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2734, Integer.Sparse.eval]; ring

theorem keyMoment2735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2735) =
      Integer.Sparse.eval keyMomentRow2735 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1676) := by
    have ha : gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge = raw42782 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42782Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42782 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4347) := by
    have ha : gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge = raw42783 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42783Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42783 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2735).leftCharge (GramAssembly.key 2735).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2735, Integer.Sparse.eval]; ring

theorem keyMoment2736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2736) =
      Integer.Sparse.eval keyMomentRow2736 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1723) := by
    have ha : gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge = raw42784 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42784Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42784 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4440) := by
    have ha : gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge = raw42785 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42785Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42785 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2736).leftCharge (GramAssembly.key 2736).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2736, Integer.Sparse.eval]; ring

theorem keyMoment2737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2737) =
      Integer.Sparse.eval keyMomentRow2737 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3413) := by
    have ha : gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge = raw42786 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42786Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42786 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4944) := by
    have ha : gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge = raw42787 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42787Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42787 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2737).leftCharge (GramAssembly.key 2737).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2737, Integer.Sparse.eval]; ring

theorem keyMoment2738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2738) =
      Integer.Sparse.eval keyMomentRow2738 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1670) := by
    have ha : gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge = raw42788 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42788Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42788 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4327) := by
    have ha : gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge = raw42789 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42789Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42789 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2738).leftCharge (GramAssembly.key 2738).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2738, Integer.Sparse.eval]; ring

theorem keyMoment2739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2739) =
      Integer.Sparse.eval keyMomentRow2739 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3408) := by
    have ha : gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge = raw42790 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42790Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42790 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4930) := by
    have ha : gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge = raw42791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42791 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2739).leftCharge (GramAssembly.key 2739).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2739, Integer.Sparse.eval]; ring

theorem keyMoment2740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2740) =
      Integer.Sparse.eval keyMomentRow2740 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2164) := by
    have ha : gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge = raw42792 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42792Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42792 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4670) := by
    have ha : gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge = raw42793 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42793Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42793 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2740).leftCharge (GramAssembly.key 2740).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2740, Integer.Sparse.eval]; ring

theorem keyMoment2741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2741) =
      Integer.Sparse.eval keyMomentRow2741 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2181) := by
    have ha : gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge = raw42794 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42794Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42794 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4757) := by
    have ha : gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge = raw42795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42795 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2741).leftCharge (GramAssembly.key 2741).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2741, Integer.Sparse.eval]; ring

theorem keyMoment2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2742) =
      Integer.Sparse.eval keyMomentRow2742 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3406) := by
    have ha : gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge = raw42796 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42796Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42796 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4931) := by
    have ha : gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge = raw42797 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42797Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42797 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2742).leftCharge (GramAssembly.key 2742).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2742, Integer.Sparse.eval]; ring

theorem keyMoment2743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2743) =
      Integer.Sparse.eval keyMomentRow2743 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3415) := by
    have ha : gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge = raw42798 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42798Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42798 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4934) := by
    have ha : gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge = raw42799 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42799Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42799 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2743).leftCharge (GramAssembly.key 2743).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2743, Integer.Sparse.eval]; ring

theorem keyMoment2744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2744) =
      Integer.Sparse.eval keyMomentRow2744 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3414) := by
    have ha : gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge = raw42800 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42800Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42800 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4933) := by
    have ha : gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge = raw42801 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42801Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42801 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2744).leftCharge (GramAssembly.key 2744).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2744, Integer.Sparse.eval]; ring

theorem keyMoment2745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2745) =
      Integer.Sparse.eval keyMomentRow2745 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3272) := by
    have ha : gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge = raw42802 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42802Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42802 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4535) := by
    have ha : gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge = raw42803 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42803Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42803 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2745).leftCharge (GramAssembly.key 2745).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2745, Integer.Sparse.eval]; ring

theorem keyMoment2746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2746) =
      Integer.Sparse.eval keyMomentRow2746 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3408) := by
    have ha : gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge = raw42804 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42804Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42804 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4930) := by
    have ha : gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge = raw42805 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42805Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42805 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2746).leftCharge (GramAssembly.key 2746).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2746, Integer.Sparse.eval]; ring

theorem keyMoment2747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2747) =
      Integer.Sparse.eval keyMomentRow2747 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1533) := by
    have ha : gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge = raw42806 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42806Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42806 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4161) := by
    have ha : gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge = raw42807 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42807Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42807 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2747).leftCharge (GramAssembly.key 2747).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2747, Integer.Sparse.eval]; ring

theorem keyMoment2748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2748) =
      Integer.Sparse.eval keyMomentRow2748 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1689) := by
    have ha : gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge = raw42808 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42808Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42808 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4335) := by
    have ha : gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge = raw42809 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42809Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42809 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2748).leftCharge (GramAssembly.key 2748).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2748, Integer.Sparse.eval]; ring

theorem keyMoment2749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2749) =
      Integer.Sparse.eval keyMomentRow2749 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3419) := by
    have ha : gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge = raw42810 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42810Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42810 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4935) := by
    have ha : gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge = raw42811 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42811Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42811 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2749).leftCharge (GramAssembly.key 2749).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2749, Integer.Sparse.eval]; ring

theorem keyMoment2750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2750) =
      Integer.Sparse.eval keyMomentRow2750 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2683) := by
    have ha : gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge = raw42812 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42812Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42812 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4611) := by
    have ha : gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge = raw42813 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42813Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42813 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2750).leftCharge (GramAssembly.key 2750).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2750, Integer.Sparse.eval]; ring

theorem keyMoment2751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2751) =
      Integer.Sparse.eval keyMomentRow2751 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2702) := by
    have ha : gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge = raw42814 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42814Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42814 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4600) := by
    have ha : gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge = raw42815 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42815Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42815 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2751).leftCharge (GramAssembly.key 2751).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2751, Integer.Sparse.eval]; ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

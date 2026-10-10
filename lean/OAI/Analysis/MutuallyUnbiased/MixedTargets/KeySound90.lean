import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical336

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2880 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2880) =
      Integer.Sparse.eval keyMomentRow2880 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3255) := by
    have ha : gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge = raw43072 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43072Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43072 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4527) := by
    have ha : gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge = raw43073 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43073Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43073 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2880).leftCharge (GramAssembly.key 2880).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2880, Integer.Sparse.eval]; ring

theorem keyMoment2881 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2881) =
      Integer.Sparse.eval keyMomentRow2881 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1505) := by
    have ha : gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge = raw43074 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43074Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43074 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4151) := by
    have ha : gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge = raw43075 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43075Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43075 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2881).leftCharge (GramAssembly.key 2881).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2881, Integer.Sparse.eval]; ring

theorem keyMoment2882 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2882) =
      Integer.Sparse.eval keyMomentRow2882 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2148) := by
    have ha : gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge = raw43076 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43076Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43076 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4666) := by
    have ha : gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge = raw43077 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43077Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43077 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2882).leftCharge (GramAssembly.key 2882).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2882, Integer.Sparse.eval]; ring

theorem keyMoment2883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2883) =
      Integer.Sparse.eval keyMomentRow2883 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3511) := by
    have ha : gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge = raw43078 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43078Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43078 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4958) := by
    have ha : gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge = raw43079 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43079Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43079 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2883).leftCharge (GramAssembly.key 2883).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2883, Integer.Sparse.eval]; ring

theorem keyMoment2884 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2884) =
      Integer.Sparse.eval keyMomentRow2884 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3261) := by
    have ha : gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge = raw43080 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43080Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43080 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4530) := by
    have ha : gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge = raw43081 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43081Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43081 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2884).leftCharge (GramAssembly.key 2884).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2884, Integer.Sparse.eval]; ring

theorem keyMoment2885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2885) =
      Integer.Sparse.eval keyMomentRow2885 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1515) := by
    have ha : gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge = raw43082 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43082Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43082 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4155) := by
    have ha : gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge = raw43083 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43083Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43083 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2885).leftCharge (GramAssembly.key 2885).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2885, Integer.Sparse.eval]; ring

end MUB6.Certificate.MixedTargetSemantics

end OAI

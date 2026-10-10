import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical314

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 800) =
      Integer.Sparse.eval keyMomentRow800 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 800).leftCharge (GramAssembly.key 800).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 93) := by
    have ha : gramCharges (GramAssembly.key 800).leftCharge (GramAssembly.key 800).rightCharge = raw40247 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40247Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40247 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 800).leftCharge (GramAssembly.key 800).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow800, Integer.Sparse.eval]

theorem keyMoment801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 801) =
      Integer.Sparse.eval keyMomentRow801 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 801).leftCharge (GramAssembly.key 801).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 509) := by
    have ha : gramCharges (GramAssembly.key 801).leftCharge (GramAssembly.key 801).rightCharge = raw40248 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40248Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40248 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 801).leftCharge (GramAssembly.key 801).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow801, Integer.Sparse.eval]

theorem keyMoment802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 802) =
      Integer.Sparse.eval keyMomentRow802 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 802).leftCharge (GramAssembly.key 802).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 63) := by
    have ha : gramCharges (GramAssembly.key 802).leftCharge (GramAssembly.key 802).rightCharge = raw40249 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40249Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40249 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 802).leftCharge (GramAssembly.key 802).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow802, Integer.Sparse.eval]

theorem keyMoment803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 803) =
      Integer.Sparse.eval keyMomentRow803 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 803).leftCharge (GramAssembly.key 803).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 247) := by
    have ha : gramCharges (GramAssembly.key 803).leftCharge (GramAssembly.key 803).rightCharge = raw40250 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40250Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40250 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 803).leftCharge (GramAssembly.key 803).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow803, Integer.Sparse.eval]

theorem keyMoment804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 804) =
      Integer.Sparse.eval keyMomentRow804 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 804).leftCharge (GramAssembly.key 804).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 175) := by
    have ha : gramCharges (GramAssembly.key 804).leftCharge (GramAssembly.key 804).rightCharge = raw40251 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40251Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40251 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 804).leftCharge (GramAssembly.key 804).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow804, Integer.Sparse.eval]

theorem keyMoment805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 805) =
      Integer.Sparse.eval keyMomentRow805 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 805).leftCharge (GramAssembly.key 805).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 222) := by
    have ha : gramCharges (GramAssembly.key 805).leftCharge (GramAssembly.key 805).rightCharge = raw40252 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40252Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40252 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 805).leftCharge (GramAssembly.key 805).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow805, Integer.Sparse.eval]

theorem keyMoment806 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 806) =
      Integer.Sparse.eval keyMomentRow806 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 806).leftCharge (GramAssembly.key 806).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 332) := by
    have ha : gramCharges (GramAssembly.key 806).leftCharge (GramAssembly.key 806).rightCharge = raw40253 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40253Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40253 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 806).leftCharge (GramAssembly.key 806).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow806, Integer.Sparse.eval]

theorem keyMoment807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 807) =
      Integer.Sparse.eval keyMomentRow807 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 807).leftCharge (GramAssembly.key 807).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 343) := by
    have ha : gramCharges (GramAssembly.key 807).leftCharge (GramAssembly.key 807).rightCharge = raw40254 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40254Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40254 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 807).leftCharge (GramAssembly.key 807).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow807, Integer.Sparse.eval]

theorem keyMoment808 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 808) =
      Integer.Sparse.eval keyMomentRow808 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 808).leftCharge (GramAssembly.key 808).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 285) := by
    have ha : gramCharges (GramAssembly.key 808).leftCharge (GramAssembly.key 808).rightCharge = raw40255 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40255Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40255 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 808).leftCharge (GramAssembly.key 808).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow808, Integer.Sparse.eval]

theorem keyMoment809 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 809) =
      Integer.Sparse.eval keyMomentRow809 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 809).leftCharge (GramAssembly.key 809).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 325) := by
    have ha : gramCharges (GramAssembly.key 809).leftCharge (GramAssembly.key 809).rightCharge = raw40256 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40256Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40256 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 809).leftCharge (GramAssembly.key 809).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow809, Integer.Sparse.eval]

theorem keyMoment810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 810) =
      Integer.Sparse.eval keyMomentRow810 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 810).leftCharge (GramAssembly.key 810).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 293) := by
    have ha : gramCharges (GramAssembly.key 810).leftCharge (GramAssembly.key 810).rightCharge = raw40257 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40257Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40257 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 810).leftCharge (GramAssembly.key 810).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow810, Integer.Sparse.eval]

theorem keyMoment811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 811) =
      Integer.Sparse.eval keyMomentRow811 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 811).leftCharge (GramAssembly.key 811).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 339) := by
    have ha : gramCharges (GramAssembly.key 811).leftCharge (GramAssembly.key 811).rightCharge = raw40258 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40258Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40258 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 811).leftCharge (GramAssembly.key 811).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow811, Integer.Sparse.eval]

theorem keyMoment812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 812) =
      Integer.Sparse.eval keyMomentRow812 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 812).leftCharge (GramAssembly.key 812).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 294) := by
    have ha : gramCharges (GramAssembly.key 812).leftCharge (GramAssembly.key 812).rightCharge = raw40259 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40259Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40259 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 812).leftCharge (GramAssembly.key 812).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow812, Integer.Sparse.eval]

theorem keyMoment813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 813) =
      Integer.Sparse.eval keyMomentRow813 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 813).leftCharge (GramAssembly.key 813).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 321) := by
    have ha : gramCharges (GramAssembly.key 813).leftCharge (GramAssembly.key 813).rightCharge = raw40260 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40260Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40260 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 813).leftCharge (GramAssembly.key 813).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow813, Integer.Sparse.eval]

theorem keyMoment814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 814) =
      Integer.Sparse.eval keyMomentRow814 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 814).leftCharge (GramAssembly.key 814).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 341) := by
    have ha : gramCharges (GramAssembly.key 814).leftCharge (GramAssembly.key 814).rightCharge = raw40261 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40261Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40261 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 814).leftCharge (GramAssembly.key 814).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow814, Integer.Sparse.eval]

theorem keyMoment815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 815) =
      Integer.Sparse.eval keyMomentRow815 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 815).leftCharge (GramAssembly.key 815).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 303) := by
    have ha : gramCharges (GramAssembly.key 815).leftCharge (GramAssembly.key 815).rightCharge = raw40262 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40262Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40262 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 815).leftCharge (GramAssembly.key 815).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow815, Integer.Sparse.eval]

theorem keyMoment816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 816) =
      Integer.Sparse.eval keyMomentRow816 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 816).leftCharge (GramAssembly.key 816).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 291) := by
    have ha : gramCharges (GramAssembly.key 816).leftCharge (GramAssembly.key 816).rightCharge = raw40263 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40263Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40263 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 816).leftCharge (GramAssembly.key 816).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow816, Integer.Sparse.eval]

theorem keyMoment817 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 817) =
      Integer.Sparse.eval keyMomentRow817 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 817).leftCharge (GramAssembly.key 817).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 158) := by
    have ha : gramCharges (GramAssembly.key 817).leftCharge (GramAssembly.key 817).rightCharge = raw40264 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40264Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40264 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 817).leftCharge (GramAssembly.key 817).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow817, Integer.Sparse.eval]

theorem keyMoment818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 818) =
      Integer.Sparse.eval keyMomentRow818 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 818).leftCharge (GramAssembly.key 818).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 28) := by
    have ha : gramCharges (GramAssembly.key 818).leftCharge (GramAssembly.key 818).rightCharge = raw40265 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40265Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40265 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 818).leftCharge (GramAssembly.key 818).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow818, Integer.Sparse.eval]

theorem keyMoment819 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 819) =
      Integer.Sparse.eval keyMomentRow819 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 819).leftCharge (GramAssembly.key 819).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 94) := by
    have ha : gramCharges (GramAssembly.key 819).leftCharge (GramAssembly.key 819).rightCharge = raw40266 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40266Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40266 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 819).leftCharge (GramAssembly.key 819).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow819, Integer.Sparse.eval]

theorem keyMoment820 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 820) =
      Integer.Sparse.eval keyMomentRow820 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 820).leftCharge (GramAssembly.key 820).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 71) := by
    have ha : gramCharges (GramAssembly.key 820).leftCharge (GramAssembly.key 820).rightCharge = raw40267 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40267Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40267 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 820).leftCharge (GramAssembly.key 820).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow820, Integer.Sparse.eval]

theorem keyMoment821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 821) =
      Integer.Sparse.eval keyMomentRow821 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 821).leftCharge (GramAssembly.key 821).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 68) := by
    have ha : gramCharges (GramAssembly.key 821).leftCharge (GramAssembly.key 821).rightCharge = raw40268 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40268Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40268 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 821).leftCharge (GramAssembly.key 821).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow821, Integer.Sparse.eval]

theorem keyMoment822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 822) =
      Integer.Sparse.eval keyMomentRow822 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 822).leftCharge (GramAssembly.key 822).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 72) := by
    have ha : gramCharges (GramAssembly.key 822).leftCharge (GramAssembly.key 822).rightCharge = raw40269 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40269Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40269 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 822).leftCharge (GramAssembly.key 822).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow822, Integer.Sparse.eval]

theorem keyMoment823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 823) =
      Integer.Sparse.eval keyMomentRow823 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 823).leftCharge (GramAssembly.key 823).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 70) := by
    have ha : gramCharges (GramAssembly.key 823).leftCharge (GramAssembly.key 823).rightCharge = raw40270 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40270Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40270 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 823).leftCharge (GramAssembly.key 823).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow823, Integer.Sparse.eval]

theorem keyMoment824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 824) =
      Integer.Sparse.eval keyMomentRow824 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 824).leftCharge (GramAssembly.key 824).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 252) := by
    have ha : gramCharges (GramAssembly.key 824).leftCharge (GramAssembly.key 824).rightCharge = raw40271 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40271Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40271 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 824).leftCharge (GramAssembly.key 824).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow824, Integer.Sparse.eval]

theorem keyMoment825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 825) =
      Integer.Sparse.eval keyMomentRow825 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 825).leftCharge (GramAssembly.key 825).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 183) := by
    have ha : gramCharges (GramAssembly.key 825).leftCharge (GramAssembly.key 825).rightCharge = raw40272 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40272Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40272 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 825).leftCharge (GramAssembly.key 825).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow825, Integer.Sparse.eval]

theorem keyMoment826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 826) =
      Integer.Sparse.eval keyMomentRow826 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 826).leftCharge (GramAssembly.key 826).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 227) := by
    have ha : gramCharges (GramAssembly.key 826).leftCharge (GramAssembly.key 826).rightCharge = raw40273 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40273Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40273 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 826).leftCharge (GramAssembly.key 826).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow826, Integer.Sparse.eval]

theorem keyMoment827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 827) =
      Integer.Sparse.eval keyMomentRow827 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 827).leftCharge (GramAssembly.key 827).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 210) := by
    have ha : gramCharges (GramAssembly.key 827).leftCharge (GramAssembly.key 827).rightCharge = raw40274 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40274Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40274 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 827).leftCharge (GramAssembly.key 827).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow827, Integer.Sparse.eval]

theorem keyMoment828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 828) =
      Integer.Sparse.eval keyMomentRow828 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 828).leftCharge (GramAssembly.key 828).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 452) := by
    have ha : gramCharges (GramAssembly.key 828).leftCharge (GramAssembly.key 828).rightCharge = raw40275 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40275Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40275 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 828).leftCharge (GramAssembly.key 828).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow828, Integer.Sparse.eval]

theorem keyMoment829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 829) =
      Integer.Sparse.eval keyMomentRow829 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 829).leftCharge (GramAssembly.key 829).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 508) := by
    have ha : gramCharges (GramAssembly.key 829).leftCharge (GramAssembly.key 829).rightCharge = raw40276 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40276Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40276 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 829).leftCharge (GramAssembly.key 829).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow829, Integer.Sparse.eval]

theorem keyMoment830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 830) =
      Integer.Sparse.eval keyMomentRow830 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 830).leftCharge (GramAssembly.key 830).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 509) := by
    have ha : gramCharges (GramAssembly.key 830).leftCharge (GramAssembly.key 830).rightCharge = raw40277 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40277Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40277 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 830).leftCharge (GramAssembly.key 830).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow830, Integer.Sparse.eval]

theorem keyMoment831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 831) =
      Integer.Sparse.eval keyMomentRow831 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 831).leftCharge (GramAssembly.key 831).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 161) := by
    have ha : gramCharges (GramAssembly.key 831).leftCharge (GramAssembly.key 831).rightCharge = raw40278 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40278Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40278 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 831).leftCharge (GramAssembly.key 831).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow831, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

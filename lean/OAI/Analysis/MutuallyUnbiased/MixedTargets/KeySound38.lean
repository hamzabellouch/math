import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical317

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1216) =
      Integer.Sparse.eval keyMomentRow1216 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1216).leftCharge (GramAssembly.key 1216).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3908) := by
    have ha : gramCharges (GramAssembly.key 1216).leftCharge (GramAssembly.key 1216).rightCharge = raw40648 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40648Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40648 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1216).leftCharge (GramAssembly.key 1216).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1216, Integer.Sparse.eval]

theorem keyMoment1217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1217) =
      Integer.Sparse.eval keyMomentRow1217 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1217).leftCharge (GramAssembly.key 1217).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3814) := by
    have ha : gramCharges (GramAssembly.key 1217).leftCharge (GramAssembly.key 1217).rightCharge = raw40649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40649 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1217).leftCharge (GramAssembly.key 1217).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1217, Integer.Sparse.eval]

theorem keyMoment1218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1218) =
      Integer.Sparse.eval keyMomentRow1218 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1218).leftCharge (GramAssembly.key 1218).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3903) := by
    have ha : gramCharges (GramAssembly.key 1218).leftCharge (GramAssembly.key 1218).rightCharge = raw40650 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40650Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40650 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1218).leftCharge (GramAssembly.key 1218).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1218, Integer.Sparse.eval]

theorem keyMoment1219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1219) =
      Integer.Sparse.eval keyMomentRow1219 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1219).leftCharge (GramAssembly.key 1219).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3904) := by
    have ha : gramCharges (GramAssembly.key 1219).leftCharge (GramAssembly.key 1219).rightCharge = raw40651 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40651Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40651 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1219).leftCharge (GramAssembly.key 1219).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1219, Integer.Sparse.eval]

theorem keyMoment1220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1220) =
      Integer.Sparse.eval keyMomentRow1220 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1220).leftCharge (GramAssembly.key 1220).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3906) := by
    have ha : gramCharges (GramAssembly.key 1220).leftCharge (GramAssembly.key 1220).rightCharge = raw40652 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40652Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40652 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1220).leftCharge (GramAssembly.key 1220).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1220, Integer.Sparse.eval]

theorem keyMoment1221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1221) =
      Integer.Sparse.eval keyMomentRow1221 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1221).leftCharge (GramAssembly.key 1221).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2277) := by
    have ha : gramCharges (GramAssembly.key 1221).leftCharge (GramAssembly.key 1221).rightCharge = raw40653 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40653Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40653 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1221).leftCharge (GramAssembly.key 1221).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1221, Integer.Sparse.eval]

theorem keyMoment1222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1222) =
      Integer.Sparse.eval keyMomentRow1222 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1222).leftCharge (GramAssembly.key 1222).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3901) := by
    have ha : gramCharges (GramAssembly.key 1222).leftCharge (GramAssembly.key 1222).rightCharge = raw40654 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40654Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40654 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1222).leftCharge (GramAssembly.key 1222).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1222, Integer.Sparse.eval]

theorem keyMoment1223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1223) =
      Integer.Sparse.eval keyMomentRow1223 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1223).leftCharge (GramAssembly.key 1223).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3812) := by
    have ha : gramCharges (GramAssembly.key 1223).leftCharge (GramAssembly.key 1223).rightCharge = raw40655 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40655Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40655 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1223).leftCharge (GramAssembly.key 1223).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1223, Integer.Sparse.eval]

theorem keyMoment1224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1224) =
      Integer.Sparse.eval keyMomentRow1224 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1224).leftCharge (GramAssembly.key 1224).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2281) := by
    have ha : gramCharges (GramAssembly.key 1224).leftCharge (GramAssembly.key 1224).rightCharge = raw40656 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40656Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40656 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1224).leftCharge (GramAssembly.key 1224).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1224, Integer.Sparse.eval]

theorem keyMoment1225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1225) =
      Integer.Sparse.eval keyMomentRow1225 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1225).leftCharge (GramAssembly.key 1225).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3633) := by
    have ha : gramCharges (GramAssembly.key 1225).leftCharge (GramAssembly.key 1225).rightCharge = raw40657 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40657Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40657 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1225).leftCharge (GramAssembly.key 1225).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1225, Integer.Sparse.eval]

theorem keyMoment1226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1226) =
      Integer.Sparse.eval keyMomentRow1226 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1226).leftCharge (GramAssembly.key 1226).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3054) := by
    have ha : gramCharges (GramAssembly.key 1226).leftCharge (GramAssembly.key 1226).rightCharge = raw40658 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40658Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40658 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1226).leftCharge (GramAssembly.key 1226).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1226, Integer.Sparse.eval]

theorem keyMoment1227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1227) =
      Integer.Sparse.eval keyMomentRow1227 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1227).leftCharge (GramAssembly.key 1227).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3913) := by
    have ha : gramCharges (GramAssembly.key 1227).leftCharge (GramAssembly.key 1227).rightCharge = raw40659 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40659Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40659 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1227).leftCharge (GramAssembly.key 1227).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1227, Integer.Sparse.eval]

theorem keyMoment1228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1228) =
      Integer.Sparse.eval keyMomentRow1228 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1228).leftCharge (GramAssembly.key 1228).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3907) := by
    have ha : gramCharges (GramAssembly.key 1228).leftCharge (GramAssembly.key 1228).rightCharge = raw40660 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40660Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40660 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1228).leftCharge (GramAssembly.key 1228).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1228, Integer.Sparse.eval]

theorem keyMoment1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1229) =
      Integer.Sparse.eval keyMomentRow1229 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1229).leftCharge (GramAssembly.key 1229).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2278) := by
    have ha : gramCharges (GramAssembly.key 1229).leftCharge (GramAssembly.key 1229).rightCharge = raw40661 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40661Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40661 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1229).leftCharge (GramAssembly.key 1229).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1229, Integer.Sparse.eval]

theorem keyMoment1230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1230) =
      Integer.Sparse.eval keyMomentRow1230 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1230).leftCharge (GramAssembly.key 1230).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3910) := by
    have ha : gramCharges (GramAssembly.key 1230).leftCharge (GramAssembly.key 1230).rightCharge = raw40662 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40662Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40662 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1230).leftCharge (GramAssembly.key 1230).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1230, Integer.Sparse.eval]

theorem keyMoment1231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1231) =
      Integer.Sparse.eval keyMomentRow1231 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1231).leftCharge (GramAssembly.key 1231).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3813) := by
    have ha : gramCharges (GramAssembly.key 1231).leftCharge (GramAssembly.key 1231).rightCharge = raw40663 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40663Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40663 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1231).leftCharge (GramAssembly.key 1231).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1231, Integer.Sparse.eval]

theorem keyMoment1232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1232) =
      Integer.Sparse.eval keyMomentRow1232 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1232).leftCharge (GramAssembly.key 1232).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2293) := by
    have ha : gramCharges (GramAssembly.key 1232).leftCharge (GramAssembly.key 1232).rightCharge = raw40664 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40664Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40664 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1232).leftCharge (GramAssembly.key 1232).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1232, Integer.Sparse.eval]

theorem keyMoment1233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1233) =
      Integer.Sparse.eval keyMomentRow1233 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1233).leftCharge (GramAssembly.key 1233).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2743) := by
    have ha : gramCharges (GramAssembly.key 1233).leftCharge (GramAssembly.key 1233).rightCharge = raw40665 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40665Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40665 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1233).leftCharge (GramAssembly.key 1233).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1233, Integer.Sparse.eval]

theorem keyMoment1234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1234) =
      Integer.Sparse.eval keyMomentRow1234 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1234).leftCharge (GramAssembly.key 1234).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 1234).leftCharge (GramAssembly.key 1234).rightCharge = raw40666 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40666Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40666 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1234).leftCharge (GramAssembly.key 1234).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1234, Integer.Sparse.eval]

theorem keyMoment1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1235) =
      Integer.Sparse.eval keyMomentRow1235 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1235).leftCharge (GramAssembly.key 1235).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3817) := by
    have ha : gramCharges (GramAssembly.key 1235).leftCharge (GramAssembly.key 1235).rightCharge = raw40667 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40667Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40667 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1235).leftCharge (GramAssembly.key 1235).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1235, Integer.Sparse.eval]

theorem keyMoment1236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1236) =
      Integer.Sparse.eval keyMomentRow1236 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1236).leftCharge (GramAssembly.key 1236).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3963) := by
    have ha : gramCharges (GramAssembly.key 1236).leftCharge (GramAssembly.key 1236).rightCharge = raw40668 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40668Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40668 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1236).leftCharge (GramAssembly.key 1236).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1236, Integer.Sparse.eval]

theorem keyMoment1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1237) =
      Integer.Sparse.eval keyMomentRow1237 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1237).leftCharge (GramAssembly.key 1237).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 1237).leftCharge (GramAssembly.key 1237).rightCharge = raw5922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw5922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical5922 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1237).leftCharge (GramAssembly.key 1237).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1237, Integer.Sparse.eval]

theorem keyMoment1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1238) =
      Integer.Sparse.eval keyMomentRow1238 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1238).leftCharge (GramAssembly.key 1238).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 1238).leftCharge (GramAssembly.key 1238).rightCharge = raw40669 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40669Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40669 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1238).leftCharge (GramAssembly.key 1238).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1238, Integer.Sparse.eval]

theorem keyMoment1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1239) =
      Integer.Sparse.eval keyMomentRow1239 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1239).leftCharge (GramAssembly.key 1239).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3845) := by
    have ha : gramCharges (GramAssembly.key 1239).leftCharge (GramAssembly.key 1239).rightCharge = raw40670 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40670Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40670 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1239).leftCharge (GramAssembly.key 1239).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1239, Integer.Sparse.eval]

theorem keyMoment1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1240) =
      Integer.Sparse.eval keyMomentRow1240 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1240).leftCharge (GramAssembly.key 1240).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3958) := by
    have ha : gramCharges (GramAssembly.key 1240).leftCharge (GramAssembly.key 1240).rightCharge = raw40671 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40671Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40671 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1240).leftCharge (GramAssembly.key 1240).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1240, Integer.Sparse.eval]

theorem keyMoment1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1241) =
      Integer.Sparse.eval keyMomentRow1241 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1241).leftCharge (GramAssembly.key 1241).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 1241).leftCharge (GramAssembly.key 1241).rightCharge = raw6278 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw6278Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical6278 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1241).leftCharge (GramAssembly.key 1241).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1241, Integer.Sparse.eval]

theorem keyMoment1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1242) =
      Integer.Sparse.eval keyMomentRow1242 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1242).leftCharge (GramAssembly.key 1242).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 1242).leftCharge (GramAssembly.key 1242).rightCharge = raw6608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw6608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical6608 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1242).leftCharge (GramAssembly.key 1242).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1242, Integer.Sparse.eval]

theorem keyMoment1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1243) =
      Integer.Sparse.eval keyMomentRow1243 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1243).leftCharge (GramAssembly.key 1243).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 1243).leftCharge (GramAssembly.key 1243).rightCharge = raw6961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw6961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical6961 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1243).leftCharge (GramAssembly.key 1243).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1243, Integer.Sparse.eval]

theorem keyMoment1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1244) =
      Integer.Sparse.eval keyMomentRow1244 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1244).leftCharge (GramAssembly.key 1244).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3961) := by
    have ha : gramCharges (GramAssembly.key 1244).leftCharge (GramAssembly.key 1244).rightCharge = raw40672 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40672Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40672 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1244).leftCharge (GramAssembly.key 1244).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1244, Integer.Sparse.eval]

theorem keyMoment1245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1245) =
      Integer.Sparse.eval keyMomentRow1245 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1245).leftCharge (GramAssembly.key 1245).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3962) := by
    have ha : gramCharges (GramAssembly.key 1245).leftCharge (GramAssembly.key 1245).rightCharge = raw40673 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40673Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40673 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1245).leftCharge (GramAssembly.key 1245).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1245, Integer.Sparse.eval]

theorem keyMoment1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1246) =
      Integer.Sparse.eval keyMomentRow1246 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1246).leftCharge (GramAssembly.key 1246).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3953) := by
    have ha : gramCharges (GramAssembly.key 1246).leftCharge (GramAssembly.key 1246).rightCharge = raw40674 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40674Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40674 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1246).leftCharge (GramAssembly.key 1246).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1246, Integer.Sparse.eval]

theorem keyMoment1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1247) =
      Integer.Sparse.eval keyMomentRow1247 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1247).leftCharge (GramAssembly.key 1247).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 1247).leftCharge (GramAssembly.key 1247).rightCharge = raw7439 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw7439Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical7439 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1247).leftCharge (GramAssembly.key 1247).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1247, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

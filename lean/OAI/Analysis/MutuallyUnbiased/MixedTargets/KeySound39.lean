import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical93
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical134
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical317
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical318

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1248) =
      Integer.Sparse.eval keyMomentRow1248 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1248).leftCharge (GramAssembly.key 1248).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3956) := by
    have ha : gramCharges (GramAssembly.key 1248).leftCharge (GramAssembly.key 1248).rightCharge = raw40675 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40675Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40675 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1248).leftCharge (GramAssembly.key 1248).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1248, Integer.Sparse.eval]

theorem keyMoment1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1249) =
      Integer.Sparse.eval keyMomentRow1249 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1249).leftCharge (GramAssembly.key 1249).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3957) := by
    have ha : gramCharges (GramAssembly.key 1249).leftCharge (GramAssembly.key 1249).rightCharge = raw40676 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40676Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40676 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1249).leftCharge (GramAssembly.key 1249).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1249, Integer.Sparse.eval]

theorem keyMoment1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1250) =
      Integer.Sparse.eval keyMomentRow1250 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1250).leftCharge (GramAssembly.key 1250).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 1250).leftCharge (GramAssembly.key 1250).rightCharge = raw11912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw11912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical11912 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1250).leftCharge (GramAssembly.key 1250).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1250, Integer.Sparse.eval]

theorem keyMoment1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1251) =
      Integer.Sparse.eval keyMomentRow1251 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1251).leftCharge (GramAssembly.key 1251).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2265) := by
    have ha : gramCharges (GramAssembly.key 1251).leftCharge (GramAssembly.key 1251).rightCharge = raw40677 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40677Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40677 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1251).leftCharge (GramAssembly.key 1251).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1251, Integer.Sparse.eval]

theorem keyMoment1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1252) =
      Integer.Sparse.eval keyMomentRow1252 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1252).leftCharge (GramAssembly.key 1252).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3808) := by
    have ha : gramCharges (GramAssembly.key 1252).leftCharge (GramAssembly.key 1252).rightCharge = raw40678 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40678Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40678 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1252).leftCharge (GramAssembly.key 1252).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1252, Integer.Sparse.eval]

theorem keyMoment1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1253) =
      Integer.Sparse.eval keyMomentRow1253 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1253).leftCharge (GramAssembly.key 1253).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3958) := by
    have ha : gramCharges (GramAssembly.key 1253).leftCharge (GramAssembly.key 1253).rightCharge = raw40679 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40679Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40679 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1253).leftCharge (GramAssembly.key 1253).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1253, Integer.Sparse.eval]

theorem keyMoment1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1254) =
      Integer.Sparse.eval keyMomentRow1254 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1254).leftCharge (GramAssembly.key 1254).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 1254).leftCharge (GramAssembly.key 1254).rightCharge = raw40680 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40680Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40680 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1254).leftCharge (GramAssembly.key 1254).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1254, Integer.Sparse.eval]

theorem keyMoment1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1255) =
      Integer.Sparse.eval keyMomentRow1255 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1255).leftCharge (GramAssembly.key 1255).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 1255).leftCharge (GramAssembly.key 1255).rightCharge = raw40681 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40681Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40681 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1255).leftCharge (GramAssembly.key 1255).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1255, Integer.Sparse.eval]

theorem keyMoment1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1256) =
      Integer.Sparse.eval keyMomentRow1256 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1256).leftCharge (GramAssembly.key 1256).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 1256).leftCharge (GramAssembly.key 1256).rightCharge = raw40682 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40682Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40682 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1256).leftCharge (GramAssembly.key 1256).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1256, Integer.Sparse.eval]

theorem keyMoment1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1257) =
      Integer.Sparse.eval keyMomentRow1257 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1257).leftCharge (GramAssembly.key 1257).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 1257).leftCharge (GramAssembly.key 1257).rightCharge = raw40683 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40683Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40683 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1257).leftCharge (GramAssembly.key 1257).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1257, Integer.Sparse.eval]

theorem keyMoment1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1258) =
      Integer.Sparse.eval keyMomentRow1258 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1258).leftCharge (GramAssembly.key 1258).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 1258).leftCharge (GramAssembly.key 1258).rightCharge = raw40684 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40684Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40684 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1258).leftCharge (GramAssembly.key 1258).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1258, Integer.Sparse.eval]

theorem keyMoment1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1259) =
      Integer.Sparse.eval keyMomentRow1259 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1259).leftCharge (GramAssembly.key 1259).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2278) := by
    have ha : gramCharges (GramAssembly.key 1259).leftCharge (GramAssembly.key 1259).rightCharge = raw40685 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40685Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40685 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1259).leftCharge (GramAssembly.key 1259).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1259, Integer.Sparse.eval]

theorem keyMoment1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1260) =
      Integer.Sparse.eval keyMomentRow1260 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1260).leftCharge (GramAssembly.key 1260).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 1260).leftCharge (GramAssembly.key 1260).rightCharge = raw40686 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40686Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40686 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1260).leftCharge (GramAssembly.key 1260).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1260, Integer.Sparse.eval]

theorem keyMoment1261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1261) =
      Integer.Sparse.eval keyMomentRow1261 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1261).leftCharge (GramAssembly.key 1261).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3044) := by
    have ha : gramCharges (GramAssembly.key 1261).leftCharge (GramAssembly.key 1261).rightCharge = raw40687 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40687Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40687 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1261).leftCharge (GramAssembly.key 1261).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1261, Integer.Sparse.eval]

theorem keyMoment1262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1262) =
      Integer.Sparse.eval keyMomentRow1262 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1262).leftCharge (GramAssembly.key 1262).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3813) := by
    have ha : gramCharges (GramAssembly.key 1262).leftCharge (GramAssembly.key 1262).rightCharge = raw40688 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40688Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40688 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1262).leftCharge (GramAssembly.key 1262).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1262, Integer.Sparse.eval]

theorem keyMoment1263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1263) =
      Integer.Sparse.eval keyMomentRow1263 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1263).leftCharge (GramAssembly.key 1263).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3884) := by
    have ha : gramCharges (GramAssembly.key 1263).leftCharge (GramAssembly.key 1263).rightCharge = raw40689 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40689Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40689 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1263).leftCharge (GramAssembly.key 1263).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1263, Integer.Sparse.eval]

theorem keyMoment1264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1264) =
      Integer.Sparse.eval keyMomentRow1264 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1264).leftCharge (GramAssembly.key 1264).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3506) := by
    have ha : gramCharges (GramAssembly.key 1264).leftCharge (GramAssembly.key 1264).rightCharge = raw40690 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40690Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40690 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1264).leftCharge (GramAssembly.key 1264).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1264, Integer.Sparse.eval]

theorem keyMoment1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1265) =
      Integer.Sparse.eval keyMomentRow1265 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1265).leftCharge (GramAssembly.key 1265).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3068) := by
    have ha : gramCharges (GramAssembly.key 1265).leftCharge (GramAssembly.key 1265).rightCharge = raw40691 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40691Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40691 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1265).leftCharge (GramAssembly.key 1265).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1265, Integer.Sparse.eval]

theorem keyMoment1266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1266) =
      Integer.Sparse.eval keyMomentRow1266 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1266).leftCharge (GramAssembly.key 1266).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 1266).leftCharge (GramAssembly.key 1266).rightCharge = raw40692 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40692Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40692 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1266).leftCharge (GramAssembly.key 1266).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1266, Integer.Sparse.eval]

theorem keyMoment1267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1267) =
      Integer.Sparse.eval keyMomentRow1267 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1267).leftCharge (GramAssembly.key 1267).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 1267).leftCharge (GramAssembly.key 1267).rightCharge = raw40693 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40693Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40693 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1267).leftCharge (GramAssembly.key 1267).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1267, Integer.Sparse.eval]

theorem keyMoment1268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1268) =
      Integer.Sparse.eval keyMomentRow1268 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1268).leftCharge (GramAssembly.key 1268).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3730) := by
    have ha : gramCharges (GramAssembly.key 1268).leftCharge (GramAssembly.key 1268).rightCharge = raw40694 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40694Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40694 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1268).leftCharge (GramAssembly.key 1268).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1268, Integer.Sparse.eval]

theorem keyMoment1269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1269) =
      Integer.Sparse.eval keyMomentRow1269 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1269).leftCharge (GramAssembly.key 1269).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3826) := by
    have ha : gramCharges (GramAssembly.key 1269).leftCharge (GramAssembly.key 1269).rightCharge = raw40695 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40695Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40695 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1269).leftCharge (GramAssembly.key 1269).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1269, Integer.Sparse.eval]

theorem keyMoment1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1270) =
      Integer.Sparse.eval keyMomentRow1270 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1270).leftCharge (GramAssembly.key 1270).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3723) := by
    have ha : gramCharges (GramAssembly.key 1270).leftCharge (GramAssembly.key 1270).rightCharge = raw40696 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40696Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40696 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1270).leftCharge (GramAssembly.key 1270).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1270, Integer.Sparse.eval]

theorem keyMoment1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1271) =
      Integer.Sparse.eval keyMomentRow1271 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1271).leftCharge (GramAssembly.key 1271).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 1271).leftCharge (GramAssembly.key 1271).rightCharge = raw40697 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40697Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40697 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1271).leftCharge (GramAssembly.key 1271).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1271, Integer.Sparse.eval]

theorem keyMoment1272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1272) =
      Integer.Sparse.eval keyMomentRow1272 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1272).leftCharge (GramAssembly.key 1272).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3909) := by
    have ha : gramCharges (GramAssembly.key 1272).leftCharge (GramAssembly.key 1272).rightCharge = raw40698 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40698Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40698 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1272).leftCharge (GramAssembly.key 1272).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1272, Integer.Sparse.eval]

theorem keyMoment1273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1273) =
      Integer.Sparse.eval keyMomentRow1273 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1273).leftCharge (GramAssembly.key 1273).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2244) := by
    have ha : gramCharges (GramAssembly.key 1273).leftCharge (GramAssembly.key 1273).rightCharge = raw17178 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw17178Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical17178 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1273).leftCharge (GramAssembly.key 1273).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1273, Integer.Sparse.eval]

theorem keyMoment1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1274) =
      Integer.Sparse.eval keyMomentRow1274 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1274).leftCharge (GramAssembly.key 1274).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2709) := by
    have ha : gramCharges (GramAssembly.key 1274).leftCharge (GramAssembly.key 1274).rightCharge = raw40699 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40699Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40699 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1274).leftCharge (GramAssembly.key 1274).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1274, Integer.Sparse.eval]

theorem keyMoment1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1275) =
      Integer.Sparse.eval keyMomentRow1275 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1275).leftCharge (GramAssembly.key 1275).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3029) := by
    have ha : gramCharges (GramAssembly.key 1275).leftCharge (GramAssembly.key 1275).rightCharge = raw40700 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40700Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40700 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1275).leftCharge (GramAssembly.key 1275).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1275, Integer.Sparse.eval]

theorem keyMoment1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1276) =
      Integer.Sparse.eval keyMomentRow1276 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1276).leftCharge (GramAssembly.key 1276).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3800) := by
    have ha : gramCharges (GramAssembly.key 1276).leftCharge (GramAssembly.key 1276).rightCharge = raw40701 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40701Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40701 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1276).leftCharge (GramAssembly.key 1276).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1276, Integer.Sparse.eval]

theorem keyMoment1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1277) =
      Integer.Sparse.eval keyMomentRow1277 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1277).leftCharge (GramAssembly.key 1277).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3953) := by
    have ha : gramCharges (GramAssembly.key 1277).leftCharge (GramAssembly.key 1277).rightCharge = raw40702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40702 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1277).leftCharge (GramAssembly.key 1277).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1277, Integer.Sparse.eval]

theorem keyMoment1278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1278) =
      Integer.Sparse.eval keyMomentRow1278 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1278).leftCharge (GramAssembly.key 1278).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3505) := by
    have ha : gramCharges (GramAssembly.key 1278).leftCharge (GramAssembly.key 1278).rightCharge = raw40703 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40703Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40703 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1278).leftCharge (GramAssembly.key 1278).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1278, Integer.Sparse.eval]

theorem keyMoment1279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1279) =
      Integer.Sparse.eval keyMomentRow1279 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1279).leftCharge (GramAssembly.key 1279).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2952) := by
    have ha : gramCharges (GramAssembly.key 1279).leftCharge (GramAssembly.key 1279).rightCharge = raw40704 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40704Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40704 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1279).leftCharge (GramAssembly.key 1279).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1279, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical318

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1280) =
      Integer.Sparse.eval keyMomentRow1280 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1280).leftCharge (GramAssembly.key 1280).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2951) := by
    have ha : gramCharges (GramAssembly.key 1280).leftCharge (GramAssembly.key 1280).rightCharge = raw40705 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40705Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40705 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1280).leftCharge (GramAssembly.key 1280).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1280, Integer.Sparse.eval]

theorem keyMoment1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1281) =
      Integer.Sparse.eval keyMomentRow1281 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1281).leftCharge (GramAssembly.key 1281).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3827) := by
    have ha : gramCharges (GramAssembly.key 1281).leftCharge (GramAssembly.key 1281).rightCharge = raw40706 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40706Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40706 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1281).leftCharge (GramAssembly.key 1281).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1281, Integer.Sparse.eval]

theorem keyMoment1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1282) =
      Integer.Sparse.eval keyMomentRow1282 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1282).leftCharge (GramAssembly.key 1282).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2933) := by
    have ha : gramCharges (GramAssembly.key 1282).leftCharge (GramAssembly.key 1282).rightCharge = raw40707 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40707Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40707 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1282).leftCharge (GramAssembly.key 1282).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1282, Integer.Sparse.eval]

theorem keyMoment1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1283) =
      Integer.Sparse.eval keyMomentRow1283 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1283).leftCharge (GramAssembly.key 1283).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1292) := by
    have ha : gramCharges (GramAssembly.key 1283).leftCharge (GramAssembly.key 1283).rightCharge = raw40708 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40708Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40708 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1283).leftCharge (GramAssembly.key 1283).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1283, Integer.Sparse.eval]

theorem keyMoment1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1284) =
      Integer.Sparse.eval keyMomentRow1284 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1284).leftCharge (GramAssembly.key 1284).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 1284).leftCharge (GramAssembly.key 1284).rightCharge = raw40709 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40709Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40709 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1284).leftCharge (GramAssembly.key 1284).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1284, Integer.Sparse.eval]

theorem keyMoment1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1285) =
      Integer.Sparse.eval keyMomentRow1285 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1285).leftCharge (GramAssembly.key 1285).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1291) := by
    have ha : gramCharges (GramAssembly.key 1285).leftCharge (GramAssembly.key 1285).rightCharge = raw40710 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40710Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40710 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1285).leftCharge (GramAssembly.key 1285).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1285, Integer.Sparse.eval]

theorem keyMoment1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1286) =
      Integer.Sparse.eval keyMomentRow1286 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1286).leftCharge (GramAssembly.key 1286).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2632) := by
    have ha : gramCharges (GramAssembly.key 1286).leftCharge (GramAssembly.key 1286).rightCharge = raw40711 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40711Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40711 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1286).leftCharge (GramAssembly.key 1286).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1286, Integer.Sparse.eval]

theorem keyMoment1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1287) =
      Integer.Sparse.eval keyMomentRow1287 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1287).leftCharge (GramAssembly.key 1287).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1261) := by
    have ha : gramCharges (GramAssembly.key 1287).leftCharge (GramAssembly.key 1287).rightCharge = raw40712 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40712Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40712 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1287).leftCharge (GramAssembly.key 1287).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1287, Integer.Sparse.eval]

theorem keyMoment1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1288) =
      Integer.Sparse.eval keyMomentRow1288 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1288).leftCharge (GramAssembly.key 1288).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2631) := by
    have ha : gramCharges (GramAssembly.key 1288).leftCharge (GramAssembly.key 1288).rightCharge = raw40713 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40713Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40713 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1288).leftCharge (GramAssembly.key 1288).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1288, Integer.Sparse.eval]

theorem keyMoment1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1289) =
      Integer.Sparse.eval keyMomentRow1289 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1289).leftCharge (GramAssembly.key 1289).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1260) := by
    have ha : gramCharges (GramAssembly.key 1289).leftCharge (GramAssembly.key 1289).rightCharge = raw40714 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40714Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40714 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1289).leftCharge (GramAssembly.key 1289).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1289, Integer.Sparse.eval]

theorem keyMoment1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1290) =
      Integer.Sparse.eval keyMomentRow1290 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1290).leftCharge (GramAssembly.key 1290).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2587) := by
    have ha : gramCharges (GramAssembly.key 1290).leftCharge (GramAssembly.key 1290).rightCharge = raw40715 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40715Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40715 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1290).leftCharge (GramAssembly.key 1290).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1290, Integer.Sparse.eval]

theorem keyMoment1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1291) =
      Integer.Sparse.eval keyMomentRow1291 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1291).leftCharge (GramAssembly.key 1291).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 1291).leftCharge (GramAssembly.key 1291).rightCharge = raw40716 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40716Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40716 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1291).leftCharge (GramAssembly.key 1291).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1291, Integer.Sparse.eval]

theorem keyMoment1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1292) =
      Integer.Sparse.eval keyMomentRow1292 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1292).leftCharge (GramAssembly.key 1292).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2566) := by
    have ha : gramCharges (GramAssembly.key 1292).leftCharge (GramAssembly.key 1292).rightCharge = raw40717 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40717Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40717 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1292).leftCharge (GramAssembly.key 1292).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1292, Integer.Sparse.eval]

theorem keyMoment1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1293) =
      Integer.Sparse.eval keyMomentRow1293 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1293).leftCharge (GramAssembly.key 1293).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 1293).leftCharge (GramAssembly.key 1293).rightCharge = raw40718 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40718Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40718 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1293).leftCharge (GramAssembly.key 1293).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1293, Integer.Sparse.eval]

theorem keyMoment1294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1294) =
      Integer.Sparse.eval keyMomentRow1294 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1294).leftCharge (GramAssembly.key 1294).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3092) := by
    have ha : gramCharges (GramAssembly.key 1294).leftCharge (GramAssembly.key 1294).rightCharge = raw40719 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40719Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40719 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1294).leftCharge (GramAssembly.key 1294).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1294, Integer.Sparse.eval]

theorem keyMoment1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1295) =
      Integer.Sparse.eval keyMomentRow1295 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1295).leftCharge (GramAssembly.key 1295).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3854) := by
    have ha : gramCharges (GramAssembly.key 1295).leftCharge (GramAssembly.key 1295).rightCharge = raw40720 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40720Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40720 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1295).leftCharge (GramAssembly.key 1295).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1295, Integer.Sparse.eval]

theorem keyMoment1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1296) =
      Integer.Sparse.eval keyMomentRow1296 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1296).leftCharge (GramAssembly.key 1296).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 1296).leftCharge (GramAssembly.key 1296).rightCharge = raw40721 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40721Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40721 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1296).leftCharge (GramAssembly.key 1296).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1296, Integer.Sparse.eval]

theorem keyMoment1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1297) =
      Integer.Sparse.eval keyMomentRow1297 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1297).leftCharge (GramAssembly.key 1297).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3733) := by
    have ha : gramCharges (GramAssembly.key 1297).leftCharge (GramAssembly.key 1297).rightCharge = raw40722 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40722Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40722 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1297).leftCharge (GramAssembly.key 1297).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1297, Integer.Sparse.eval]

theorem keyMoment1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1298) =
      Integer.Sparse.eval keyMomentRow1298 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1298).leftCharge (GramAssembly.key 1298).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3827) := by
    have ha : gramCharges (GramAssembly.key 1298).leftCharge (GramAssembly.key 1298).rightCharge = raw40723 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40723Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40723 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1298).leftCharge (GramAssembly.key 1298).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1298, Integer.Sparse.eval]

theorem keyMoment1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1299) =
      Integer.Sparse.eval keyMomentRow1299 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1299).leftCharge (GramAssembly.key 1299).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3724) := by
    have ha : gramCharges (GramAssembly.key 1299).leftCharge (GramAssembly.key 1299).rightCharge = raw40724 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40724Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40724 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1299).leftCharge (GramAssembly.key 1299).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1299, Integer.Sparse.eval]

theorem keyMoment1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1300) =
      Integer.Sparse.eval keyMomentRow1300 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1300).leftCharge (GramAssembly.key 1300).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3819) := by
    have ha : gramCharges (GramAssembly.key 1300).leftCharge (GramAssembly.key 1300).rightCharge = raw40725 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40725Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40725 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1300).leftCharge (GramAssembly.key 1300).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1300, Integer.Sparse.eval]

theorem keyMoment1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1301) =
      Integer.Sparse.eval keyMomentRow1301 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1301).leftCharge (GramAssembly.key 1301).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 1301).leftCharge (GramAssembly.key 1301).rightCharge = raw40726 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40726Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40726 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1301).leftCharge (GramAssembly.key 1301).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1301, Integer.Sparse.eval]

theorem keyMoment1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1302) =
      Integer.Sparse.eval keyMomentRow1302 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1302).leftCharge (GramAssembly.key 1302).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 1302).leftCharge (GramAssembly.key 1302).rightCharge = raw16795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw16795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical16795 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1302).leftCharge (GramAssembly.key 1302).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1302, Integer.Sparse.eval]

theorem keyMoment1303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1303) =
      Integer.Sparse.eval keyMomentRow1303 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1303).leftCharge (GramAssembly.key 1303).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3949) := by
    have ha : gramCharges (GramAssembly.key 1303).leftCharge (GramAssembly.key 1303).rightCharge = raw40727 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40727Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40727 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1303).leftCharge (GramAssembly.key 1303).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1303, Integer.Sparse.eval]

theorem keyMoment1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1304) =
      Integer.Sparse.eval keyMomentRow1304 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1304).leftCharge (GramAssembly.key 1304).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2955) := by
    have ha : gramCharges (GramAssembly.key 1304).leftCharge (GramAssembly.key 1304).rightCharge = raw40728 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40728Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40728 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1304).leftCharge (GramAssembly.key 1304).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1304, Integer.Sparse.eval]

theorem keyMoment1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1305) =
      Integer.Sparse.eval keyMomentRow1305 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1305).leftCharge (GramAssembly.key 1305).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 1305).leftCharge (GramAssembly.key 1305).rightCharge = raw40729 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40729Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40729 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1305).leftCharge (GramAssembly.key 1305).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1305, Integer.Sparse.eval]

theorem keyMoment1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1306) =
      Integer.Sparse.eval keyMomentRow1306 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1306).leftCharge (GramAssembly.key 1306).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1295) := by
    have ha : gramCharges (GramAssembly.key 1306).leftCharge (GramAssembly.key 1306).rightCharge = raw40730 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40730Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40730 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1306).leftCharge (GramAssembly.key 1306).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1306, Integer.Sparse.eval]

theorem keyMoment1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1307) =
      Integer.Sparse.eval keyMomentRow1307 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1307).leftCharge (GramAssembly.key 1307).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2633) := by
    have ha : gramCharges (GramAssembly.key 1307).leftCharge (GramAssembly.key 1307).rightCharge = raw40731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40731 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1307).leftCharge (GramAssembly.key 1307).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1307, Integer.Sparse.eval]

theorem keyMoment1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1308) =
      Integer.Sparse.eval keyMomentRow1308 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1308).leftCharge (GramAssembly.key 1308).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1262) := by
    have ha : gramCharges (GramAssembly.key 1308).leftCharge (GramAssembly.key 1308).rightCharge = raw40732 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40732Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40732 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1308).leftCharge (GramAssembly.key 1308).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1308, Integer.Sparse.eval]

theorem keyMoment1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1309) =
      Integer.Sparse.eval keyMomentRow1309 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1309).leftCharge (GramAssembly.key 1309).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2591) := by
    have ha : gramCharges (GramAssembly.key 1309).leftCharge (GramAssembly.key 1309).rightCharge = raw40733 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40733Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40733 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1309).leftCharge (GramAssembly.key 1309).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1309, Integer.Sparse.eval]

theorem keyMoment1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1310) =
      Integer.Sparse.eval keyMomentRow1310 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1310).leftCharge (GramAssembly.key 1310).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 1310).leftCharge (GramAssembly.key 1310).rightCharge = raw40734 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40734Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40734 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1310).leftCharge (GramAssembly.key 1310).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1310, Integer.Sparse.eval]

theorem keyMoment1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1311) =
      Integer.Sparse.eval keyMomentRow1311 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1311).leftCharge (GramAssembly.key 1311).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2643) := by
    have ha : gramCharges (GramAssembly.key 1311).leftCharge (GramAssembly.key 1311).rightCharge = raw40735 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40735Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40735 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1311).leftCharge (GramAssembly.key 1311).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1311, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

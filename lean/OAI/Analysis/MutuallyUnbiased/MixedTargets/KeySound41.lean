import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical318

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1312) =
      Integer.Sparse.eval keyMomentRow1312 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1312).leftCharge (GramAssembly.key 1312).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2632) := by
    have ha : gramCharges (GramAssembly.key 1312).leftCharge (GramAssembly.key 1312).rightCharge = raw40736 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40736Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40736 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1312).leftCharge (GramAssembly.key 1312).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1312, Integer.Sparse.eval]

theorem keyMoment1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1313) =
      Integer.Sparse.eval keyMomentRow1313 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1313).leftCharge (GramAssembly.key 1313).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2620) := by
    have ha : gramCharges (GramAssembly.key 1313).leftCharge (GramAssembly.key 1313).rightCharge = raw40737 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40737Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40737 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1313).leftCharge (GramAssembly.key 1313).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1313, Integer.Sparse.eval]

theorem keyMoment1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1314) =
      Integer.Sparse.eval keyMomentRow1314 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1314).leftCharge (GramAssembly.key 1314).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2614) := by
    have ha : gramCharges (GramAssembly.key 1314).leftCharge (GramAssembly.key 1314).rightCharge = raw40738 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40738Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40738 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1314).leftCharge (GramAssembly.key 1314).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1314, Integer.Sparse.eval]

theorem keyMoment1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1315) =
      Integer.Sparse.eval keyMomentRow1315 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1315).leftCharge (GramAssembly.key 1315).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2641) := by
    have ha : gramCharges (GramAssembly.key 1315).leftCharge (GramAssembly.key 1315).rightCharge = raw40739 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40739Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40739 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1315).leftCharge (GramAssembly.key 1315).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1315, Integer.Sparse.eval]

theorem keyMoment1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1316) =
      Integer.Sparse.eval keyMomentRow1316 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1316).leftCharge (GramAssembly.key 1316).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2631) := by
    have ha : gramCharges (GramAssembly.key 1316).leftCharge (GramAssembly.key 1316).rightCharge = raw40740 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40740Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40740 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1316).leftCharge (GramAssembly.key 1316).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1316, Integer.Sparse.eval]

theorem keyMoment1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1317) =
      Integer.Sparse.eval keyMomentRow1317 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1317).leftCharge (GramAssembly.key 1317).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2617) := by
    have ha : gramCharges (GramAssembly.key 1317).leftCharge (GramAssembly.key 1317).rightCharge = raw40741 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40741Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40741 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1317).leftCharge (GramAssembly.key 1317).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1317, Integer.Sparse.eval]

theorem keyMoment1318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1318) =
      Integer.Sparse.eval keyMomentRow1318 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1318).leftCharge (GramAssembly.key 1318).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2633) := by
    have ha : gramCharges (GramAssembly.key 1318).leftCharge (GramAssembly.key 1318).rightCharge = raw40742 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40742Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40742 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1318).leftCharge (GramAssembly.key 1318).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1318, Integer.Sparse.eval]

theorem keyMoment1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1319) =
      Integer.Sparse.eval keyMomentRow1319 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1319).leftCharge (GramAssembly.key 1319).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2618) := by
    have ha : gramCharges (GramAssembly.key 1319).leftCharge (GramAssembly.key 1319).rightCharge = raw40743 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40743Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40743 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1319).leftCharge (GramAssembly.key 1319).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1319, Integer.Sparse.eval]

theorem keyMoment1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1320) =
      Integer.Sparse.eval keyMomentRow1320 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1320).leftCharge (GramAssembly.key 1320).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2635) := by
    have ha : gramCharges (GramAssembly.key 1320).leftCharge (GramAssembly.key 1320).rightCharge = raw40744 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40744Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40744 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1320).leftCharge (GramAssembly.key 1320).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1320, Integer.Sparse.eval]

theorem keyMoment1321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1321) =
      Integer.Sparse.eval keyMomentRow1321 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1321).leftCharge (GramAssembly.key 1321).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1264) := by
    have ha : gramCharges (GramAssembly.key 1321).leftCharge (GramAssembly.key 1321).rightCharge = raw40745 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40745Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40745 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1321).leftCharge (GramAssembly.key 1321).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1321, Integer.Sparse.eval]

theorem keyMoment1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1322) =
      Integer.Sparse.eval keyMomentRow1322 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1322).leftCharge (GramAssembly.key 1322).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2569) := by
    have ha : gramCharges (GramAssembly.key 1322).leftCharge (GramAssembly.key 1322).rightCharge = raw40746 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40746Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40746 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1322).leftCharge (GramAssembly.key 1322).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1322, Integer.Sparse.eval]

theorem keyMoment1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1323) =
      Integer.Sparse.eval keyMomentRow1323 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1323).leftCharge (GramAssembly.key 1323).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3633) := by
    have ha : gramCharges (GramAssembly.key 1323).leftCharge (GramAssembly.key 1323).rightCharge = raw40747 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40747Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40747 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1323).leftCharge (GramAssembly.key 1323).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1323, Integer.Sparse.eval]

theorem keyMoment1324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1324) =
      Integer.Sparse.eval keyMomentRow1324 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1324).leftCharge (GramAssembly.key 1324).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3907) := by
    have ha : gramCharges (GramAssembly.key 1324).leftCharge (GramAssembly.key 1324).rightCharge = raw40748 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40748Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40748 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1324).leftCharge (GramAssembly.key 1324).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1324, Integer.Sparse.eval]

theorem keyMoment1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1325) =
      Integer.Sparse.eval keyMomentRow1325 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1325).leftCharge (GramAssembly.key 1325).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3886) := by
    have ha : gramCharges (GramAssembly.key 1325).leftCharge (GramAssembly.key 1325).rightCharge = raw40749 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40749Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40749 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1325).leftCharge (GramAssembly.key 1325).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1325, Integer.Sparse.eval]

theorem keyMoment1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1326) =
      Integer.Sparse.eval keyMomentRow1326 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1326).leftCharge (GramAssembly.key 1326).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2115) := by
    have ha : gramCharges (GramAssembly.key 1326).leftCharge (GramAssembly.key 1326).rightCharge = raw40750 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40750Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40750 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1326).leftCharge (GramAssembly.key 1326).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1326, Integer.Sparse.eval]

theorem keyMoment1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1327) =
      Integer.Sparse.eval keyMomentRow1327 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1327).leftCharge (GramAssembly.key 1327).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3582) := by
    have ha : gramCharges (GramAssembly.key 1327).leftCharge (GramAssembly.key 1327).rightCharge = raw40751 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40751Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40751 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1327).leftCharge (GramAssembly.key 1327).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1327, Integer.Sparse.eval]

theorem keyMoment1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1328) =
      Integer.Sparse.eval keyMomentRow1328 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1328).leftCharge (GramAssembly.key 1328).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3913) := by
    have ha : gramCharges (GramAssembly.key 1328).leftCharge (GramAssembly.key 1328).rightCharge = raw40752 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40752Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40752 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1328).leftCharge (GramAssembly.key 1328).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1328, Integer.Sparse.eval]

theorem keyMoment1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1329) =
      Integer.Sparse.eval keyMomentRow1329 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1329).leftCharge (GramAssembly.key 1329).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3885) := by
    have ha : gramCharges (GramAssembly.key 1329).leftCharge (GramAssembly.key 1329).rightCharge = raw40753 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40753Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40753 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1329).leftCharge (GramAssembly.key 1329).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1329, Integer.Sparse.eval]

theorem keyMoment1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1330) =
      Integer.Sparse.eval keyMomentRow1330 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1330).leftCharge (GramAssembly.key 1330).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3732) := by
    have ha : gramCharges (GramAssembly.key 1330).leftCharge (GramAssembly.key 1330).rightCharge = raw40754 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40754Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40754 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1330).leftCharge (GramAssembly.key 1330).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1330, Integer.Sparse.eval]

theorem keyMoment1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1331) =
      Integer.Sparse.eval keyMomentRow1331 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1331).leftCharge (GramAssembly.key 1331).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3857) := by
    have ha : gramCharges (GramAssembly.key 1331).leftCharge (GramAssembly.key 1331).rightCharge = raw40755 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40755Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40755 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1331).leftCharge (GramAssembly.key 1331).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1331, Integer.Sparse.eval]

theorem keyMoment1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1332) =
      Integer.Sparse.eval keyMomentRow1332 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1332).leftCharge (GramAssembly.key 1332).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3910) := by
    have ha : gramCharges (GramAssembly.key 1332).leftCharge (GramAssembly.key 1332).rightCharge = raw40756 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40756Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40756 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1332).leftCharge (GramAssembly.key 1332).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1332, Integer.Sparse.eval]

theorem keyMoment1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1333) =
      Integer.Sparse.eval keyMomentRow1333 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1333).leftCharge (GramAssembly.key 1333).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3850) := by
    have ha : gramCharges (GramAssembly.key 1333).leftCharge (GramAssembly.key 1333).rightCharge = raw40757 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40757Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40757 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1333).leftCharge (GramAssembly.key 1333).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1333, Integer.Sparse.eval]

theorem keyMoment1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1334) =
      Integer.Sparse.eval keyMomentRow1334 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1334).leftCharge (GramAssembly.key 1334).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2106) := by
    have ha : gramCharges (GramAssembly.key 1334).leftCharge (GramAssembly.key 1334).rightCharge = raw40758 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40758Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40758 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1334).leftCharge (GramAssembly.key 1334).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1334, Integer.Sparse.eval]

theorem keyMoment1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1335) =
      Integer.Sparse.eval keyMomentRow1335 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1335).leftCharge (GramAssembly.key 1335).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3731) := by
    have ha : gramCharges (GramAssembly.key 1335).leftCharge (GramAssembly.key 1335).rightCharge = raw40759 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40759Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40759 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1335).leftCharge (GramAssembly.key 1335).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1335, Integer.Sparse.eval]

theorem keyMoment1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1336) =
      Integer.Sparse.eval keyMomentRow1336 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1336).leftCharge (GramAssembly.key 1336).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3849) := by
    have ha : gramCharges (GramAssembly.key 1336).leftCharge (GramAssembly.key 1336).rightCharge = raw40760 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40760Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40760 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1336).leftCharge (GramAssembly.key 1336).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1336, Integer.Sparse.eval]

theorem keyMoment1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1337) =
      Integer.Sparse.eval keyMomentRow1337 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1337).leftCharge (GramAssembly.key 1337).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3786) := by
    have ha : gramCharges (GramAssembly.key 1337).leftCharge (GramAssembly.key 1337).rightCharge = raw40761 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40761Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40761 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1337).leftCharge (GramAssembly.key 1337).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1337, Integer.Sparse.eval]

theorem keyMoment1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1338) =
      Integer.Sparse.eval keyMomentRow1338 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1338).leftCharge (GramAssembly.key 1338).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3623) := by
    have ha : gramCharges (GramAssembly.key 1338).leftCharge (GramAssembly.key 1338).rightCharge = raw40762 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40762Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40762 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1338).leftCharge (GramAssembly.key 1338).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1338, Integer.Sparse.eval]

theorem keyMoment1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1339) =
      Integer.Sparse.eval keyMomentRow1339 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1339).leftCharge (GramAssembly.key 1339).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3885) := by
    have ha : gramCharges (GramAssembly.key 1339).leftCharge (GramAssembly.key 1339).rightCharge = raw40763 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40763Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40763 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1339).leftCharge (GramAssembly.key 1339).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1339, Integer.Sparse.eval]

theorem keyMoment1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1340) =
      Integer.Sparse.eval keyMomentRow1340 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1340).leftCharge (GramAssembly.key 1340).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2110) := by
    have ha : gramCharges (GramAssembly.key 1340).leftCharge (GramAssembly.key 1340).rightCharge = raw40764 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40764Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40764 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1340).leftCharge (GramAssembly.key 1340).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1340, Integer.Sparse.eval]

theorem keyMoment1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1341) =
      Integer.Sparse.eval keyMomentRow1341 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1341).leftCharge (GramAssembly.key 1341).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4010) := by
    have ha : gramCharges (GramAssembly.key 1341).leftCharge (GramAssembly.key 1341).rightCharge = raw40765 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40765Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40765 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1341).leftCharge (GramAssembly.key 1341).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1341, Integer.Sparse.eval]

theorem keyMoment1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1342) =
      Integer.Sparse.eval keyMomentRow1342 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1342).leftCharge (GramAssembly.key 1342).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3789) := by
    have ha : gramCharges (GramAssembly.key 1342).leftCharge (GramAssembly.key 1342).rightCharge = raw40766 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40766Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40766 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1342).leftCharge (GramAssembly.key 1342).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1342, Integer.Sparse.eval]

theorem keyMoment1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1343) =
      Integer.Sparse.eval keyMomentRow1343 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1343).leftCharge (GramAssembly.key 1343).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3875) := by
    have ha : gramCharges (GramAssembly.key 1343).leftCharge (GramAssembly.key 1343).rightCharge = raw40767 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40767Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40767 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1343).leftCharge (GramAssembly.key 1343).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1343, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

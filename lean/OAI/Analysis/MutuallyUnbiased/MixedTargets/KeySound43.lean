import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical104
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical145
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical318

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1376) =
      Integer.Sparse.eval keyMomentRow1376 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1376).leftCharge (GramAssembly.key 1376).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 1376).leftCharge (GramAssembly.key 1376).rightCharge = raw40800 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40800Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40800 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1376).leftCharge (GramAssembly.key 1376).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1376, Integer.Sparse.eval]

theorem keyMoment1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1377) =
      Integer.Sparse.eval keyMomentRow1377 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1377).leftCharge (GramAssembly.key 1377).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3809) := by
    have ha : gramCharges (GramAssembly.key 1377).leftCharge (GramAssembly.key 1377).rightCharge = raw18571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw18571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical18571 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1377).leftCharge (GramAssembly.key 1377).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1377, Integer.Sparse.eval]

theorem keyMoment1378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1378) =
      Integer.Sparse.eval keyMomentRow1378 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1378).leftCharge (GramAssembly.key 1378).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 1378).leftCharge (GramAssembly.key 1378).rightCharge = raw40801 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40801Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40801 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1378).leftCharge (GramAssembly.key 1378).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1378, Integer.Sparse.eval]

theorem keyMoment1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1379) =
      Integer.Sparse.eval keyMomentRow1379 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1379).leftCharge (GramAssembly.key 1379).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3395) := by
    have ha : gramCharges (GramAssembly.key 1379).leftCharge (GramAssembly.key 1379).rightCharge = raw40802 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40802Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40802 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1379).leftCharge (GramAssembly.key 1379).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1379, Integer.Sparse.eval]

theorem keyMoment1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1380) =
      Integer.Sparse.eval keyMomentRow1380 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1380).leftCharge (GramAssembly.key 1380).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3066) := by
    have ha : gramCharges (GramAssembly.key 1380).leftCharge (GramAssembly.key 1380).rightCharge = raw40803 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40803Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40803 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1380).leftCharge (GramAssembly.key 1380).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1380, Integer.Sparse.eval]

theorem keyMoment1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1381) =
      Integer.Sparse.eval keyMomentRow1381 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1381).leftCharge (GramAssembly.key 1381).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 1381).leftCharge (GramAssembly.key 1381).rightCharge = raw40804 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40804Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40804 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1381).leftCharge (GramAssembly.key 1381).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1381, Integer.Sparse.eval]

theorem keyMoment1382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1382) =
      Integer.Sparse.eval keyMomentRow1382 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1382).leftCharge (GramAssembly.key 1382).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 1382).leftCharge (GramAssembly.key 1382).rightCharge = raw40805 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40805Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40805 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1382).leftCharge (GramAssembly.key 1382).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1382, Integer.Sparse.eval]

theorem keyMoment1383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1383) =
      Integer.Sparse.eval keyMomentRow1383 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1383).leftCharge (GramAssembly.key 1383).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4022) := by
    have ha : gramCharges (GramAssembly.key 1383).leftCharge (GramAssembly.key 1383).rightCharge = raw40806 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40806Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40806 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1383).leftCharge (GramAssembly.key 1383).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1383, Integer.Sparse.eval]

theorem keyMoment1384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1384) =
      Integer.Sparse.eval keyMomentRow1384 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1384).leftCharge (GramAssembly.key 1384).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3730) := by
    have ha : gramCharges (GramAssembly.key 1384).leftCharge (GramAssembly.key 1384).rightCharge = raw40807 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40807Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40807 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1384).leftCharge (GramAssembly.key 1384).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1384, Integer.Sparse.eval]

theorem keyMoment1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1385) =
      Integer.Sparse.eval keyMomentRow1385 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1385).leftCharge (GramAssembly.key 1385).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3722) := by
    have ha : gramCharges (GramAssembly.key 1385).leftCharge (GramAssembly.key 1385).rightCharge = raw40808 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40808Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40808 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1385).leftCharge (GramAssembly.key 1385).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1385, Integer.Sparse.eval]

theorem keyMoment1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1386) =
      Integer.Sparse.eval keyMomentRow1386 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1386).leftCharge (GramAssembly.key 1386).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4024) := by
    have ha : gramCharges (GramAssembly.key 1386).leftCharge (GramAssembly.key 1386).rightCharge = raw40809 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40809Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40809 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1386).leftCharge (GramAssembly.key 1386).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1386, Integer.Sparse.eval]

theorem keyMoment1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1387) =
      Integer.Sparse.eval keyMomentRow1387 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1387).leftCharge (GramAssembly.key 1387).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4025) := by
    have ha : gramCharges (GramAssembly.key 1387).leftCharge (GramAssembly.key 1387).rightCharge = raw13405 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw13405Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical13405 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1387).leftCharge (GramAssembly.key 1387).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1387, Integer.Sparse.eval]

theorem keyMoment1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1388) =
      Integer.Sparse.eval keyMomentRow1388 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1388).leftCharge (GramAssembly.key 1388).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 1388).leftCharge (GramAssembly.key 1388).rightCharge = raw40810 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40810Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40810 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1388).leftCharge (GramAssembly.key 1388).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1388, Integer.Sparse.eval]

theorem keyMoment1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1389) =
      Integer.Sparse.eval keyMomentRow1389 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1389).leftCharge (GramAssembly.key 1389).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2888) := by
    have ha : gramCharges (GramAssembly.key 1389).leftCharge (GramAssembly.key 1389).rightCharge = raw40811 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40811Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40811 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1389).leftCharge (GramAssembly.key 1389).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1389, Integer.Sparse.eval]

theorem keyMoment1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1390) =
      Integer.Sparse.eval keyMomentRow1390 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1390).leftCharge (GramAssembly.key 1390).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 1390).leftCharge (GramAssembly.key 1390).rightCharge = raw40812 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40812Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40812 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1390).leftCharge (GramAssembly.key 1390).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1390, Integer.Sparse.eval]

theorem keyMoment1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1391) =
      Integer.Sparse.eval keyMomentRow1391 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1391).leftCharge (GramAssembly.key 1391).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2885) := by
    have ha : gramCharges (GramAssembly.key 1391).leftCharge (GramAssembly.key 1391).rightCharge = raw40813 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40813Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40813 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1391).leftCharge (GramAssembly.key 1391).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1391, Integer.Sparse.eval]

theorem keyMoment1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1392) =
      Integer.Sparse.eval keyMomentRow1392 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1392).leftCharge (GramAssembly.key 1392).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3733) := by
    have ha : gramCharges (GramAssembly.key 1392).leftCharge (GramAssembly.key 1392).rightCharge = raw40814 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40814Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40814 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1392).leftCharge (GramAssembly.key 1392).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1392, Integer.Sparse.eval]

theorem keyMoment1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1393) =
      Integer.Sparse.eval keyMomentRow1393 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1393).leftCharge (GramAssembly.key 1393).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2867) := by
    have ha : gramCharges (GramAssembly.key 1393).leftCharge (GramAssembly.key 1393).rightCharge = raw40815 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40815Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40815 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1393).leftCharge (GramAssembly.key 1393).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1393, Integer.Sparse.eval]

theorem keyMoment1394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1394) =
      Integer.Sparse.eval keyMomentRow1394 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1394).leftCharge (GramAssembly.key 1394).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3949) := by
    have ha : gramCharges (GramAssembly.key 1394).leftCharge (GramAssembly.key 1394).rightCharge = raw40816 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40816Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40816 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1394).leftCharge (GramAssembly.key 1394).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1394, Integer.Sparse.eval]

theorem keyMoment1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1395) =
      Integer.Sparse.eval keyMomentRow1395 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1395).leftCharge (GramAssembly.key 1395).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2864) := by
    have ha : gramCharges (GramAssembly.key 1395).leftCharge (GramAssembly.key 1395).rightCharge = raw40817 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40817Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40817 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1395).leftCharge (GramAssembly.key 1395).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1395, Integer.Sparse.eval]

theorem keyMoment1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1396) =
      Integer.Sparse.eval keyMomentRow1396 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1396).leftCharge (GramAssembly.key 1396).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3946) := by
    have ha : gramCharges (GramAssembly.key 1396).leftCharge (GramAssembly.key 1396).rightCharge = raw40818 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40818Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40818 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1396).leftCharge (GramAssembly.key 1396).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1396, Integer.Sparse.eval]

theorem keyMoment1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1397) =
      Integer.Sparse.eval keyMomentRow1397 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1397).leftCharge (GramAssembly.key 1397).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 1397).leftCharge (GramAssembly.key 1397).rightCharge = raw40819 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40819Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40819 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1397).leftCharge (GramAssembly.key 1397).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1397, Integer.Sparse.eval]

theorem keyMoment1398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1398) =
      Integer.Sparse.eval keyMomentRow1398 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1398).leftCharge (GramAssembly.key 1398).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3720) := by
    have ha : gramCharges (GramAssembly.key 1398).leftCharge (GramAssembly.key 1398).rightCharge = raw40820 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40820Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40820 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1398).leftCharge (GramAssembly.key 1398).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1398, Integer.Sparse.eval]

theorem keyMoment1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1399) =
      Integer.Sparse.eval keyMomentRow1399 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1399).leftCharge (GramAssembly.key 1399).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2279) := by
    have ha : gramCharges (GramAssembly.key 1399).leftCharge (GramAssembly.key 1399).rightCharge = raw40821 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40821Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40821 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1399).leftCharge (GramAssembly.key 1399).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1399, Integer.Sparse.eval]

theorem keyMoment1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1400) =
      Integer.Sparse.eval keyMomentRow1400 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1400).leftCharge (GramAssembly.key 1400).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 1400).leftCharge (GramAssembly.key 1400).rightCharge = raw40822 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40822Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40822 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1400).leftCharge (GramAssembly.key 1400).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1400, Integer.Sparse.eval]

theorem keyMoment1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1401) =
      Integer.Sparse.eval keyMomentRow1401 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1401).leftCharge (GramAssembly.key 1401).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3045) := by
    have ha : gramCharges (GramAssembly.key 1401).leftCharge (GramAssembly.key 1401).rightCharge = raw40823 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40823Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40823 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1401).leftCharge (GramAssembly.key 1401).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1401, Integer.Sparse.eval]

theorem keyMoment1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1402) =
      Integer.Sparse.eval keyMomentRow1402 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1402).leftCharge (GramAssembly.key 1402).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 1402).leftCharge (GramAssembly.key 1402).rightCharge = raw40824 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40824Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40824 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1402).leftCharge (GramAssembly.key 1402).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1402, Integer.Sparse.eval]

theorem keyMoment1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1403) =
      Integer.Sparse.eval keyMomentRow1403 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1403).leftCharge (GramAssembly.key 1403).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3814) := by
    have ha : gramCharges (GramAssembly.key 1403).leftCharge (GramAssembly.key 1403).rightCharge = raw40825 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40825Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40825 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1403).leftCharge (GramAssembly.key 1403).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1403, Integer.Sparse.eval]

theorem keyMoment1404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1404) =
      Integer.Sparse.eval keyMomentRow1404 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1404).leftCharge (GramAssembly.key 1404).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 1404).leftCharge (GramAssembly.key 1404).rightCharge = raw40826 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40826Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40826 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1404).leftCharge (GramAssembly.key 1404).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1404, Integer.Sparse.eval]

theorem keyMoment1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1405) =
      Integer.Sparse.eval keyMomentRow1405 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1405).leftCharge (GramAssembly.key 1405).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3379) := by
    have ha : gramCharges (GramAssembly.key 1405).leftCharge (GramAssembly.key 1405).rightCharge = raw40827 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40827Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40827 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1405).leftCharge (GramAssembly.key 1405).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1405, Integer.Sparse.eval]

theorem keyMoment1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1406) =
      Integer.Sparse.eval keyMomentRow1406 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1406).leftCharge (GramAssembly.key 1406).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3069) := by
    have ha : gramCharges (GramAssembly.key 1406).leftCharge (GramAssembly.key 1406).rightCharge = raw40828 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40828Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40828 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1406).leftCharge (GramAssembly.key 1406).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1406, Integer.Sparse.eval]

theorem keyMoment1407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1407) =
      Integer.Sparse.eval keyMomentRow1407 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1407).leftCharge (GramAssembly.key 1407).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3841) := by
    have ha : gramCharges (GramAssembly.key 1407).leftCharge (GramAssembly.key 1407).rightCharge = raw40829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40829 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1407).leftCharge (GramAssembly.key 1407).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1407, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

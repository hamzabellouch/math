import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical318

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1344) =
      Integer.Sparse.eval keyMomentRow1344 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1344).leftCharge (GramAssembly.key 1344).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2105) := by
    have ha : gramCharges (GramAssembly.key 1344).leftCharge (GramAssembly.key 1344).rightCharge = raw40768 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40768Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40768 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1344).leftCharge (GramAssembly.key 1344).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1344, Integer.Sparse.eval]

theorem keyMoment1345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1345) =
      Integer.Sparse.eval keyMomentRow1345 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1345).leftCharge (GramAssembly.key 1345).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2112) := by
    have ha : gramCharges (GramAssembly.key 1345).leftCharge (GramAssembly.key 1345).rightCharge = raw40769 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40769Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40769 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1345).leftCharge (GramAssembly.key 1345).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1345, Integer.Sparse.eval]

theorem keyMoment1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1346) =
      Integer.Sparse.eval keyMomentRow1346 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1346).leftCharge (GramAssembly.key 1346).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2954) := by
    have ha : gramCharges (GramAssembly.key 1346).leftCharge (GramAssembly.key 1346).rightCharge = raw40770 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40770Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40770 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1346).leftCharge (GramAssembly.key 1346).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1346, Integer.Sparse.eval]

theorem keyMoment1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1347) =
      Integer.Sparse.eval keyMomentRow1347 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1347).leftCharge (GramAssembly.key 1347).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3876) := by
    have ha : gramCharges (GramAssembly.key 1347).leftCharge (GramAssembly.key 1347).rightCharge = raw40771 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40771Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40771 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1347).leftCharge (GramAssembly.key 1347).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1347, Integer.Sparse.eval]

theorem keyMoment1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1348) =
      Integer.Sparse.eval keyMomentRow1348 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1348).leftCharge (GramAssembly.key 1348).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3787) := by
    have ha : gramCharges (GramAssembly.key 1348).leftCharge (GramAssembly.key 1348).rightCharge = raw40772 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40772Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40772 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1348).leftCharge (GramAssembly.key 1348).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1348, Integer.Sparse.eval]

theorem keyMoment1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1349) =
      Integer.Sparse.eval keyMomentRow1349 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1349).leftCharge (GramAssembly.key 1349).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1297) := by
    have ha : gramCharges (GramAssembly.key 1349).leftCharge (GramAssembly.key 1349).rightCharge = raw40773 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40773Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40773 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1349).leftCharge (GramAssembly.key 1349).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1349, Integer.Sparse.eval]

theorem keyMoment1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1350) =
      Integer.Sparse.eval keyMomentRow1350 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1350).leftCharge (GramAssembly.key 1350).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2783) := by
    have ha : gramCharges (GramAssembly.key 1350).leftCharge (GramAssembly.key 1350).rightCharge = raw40774 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40774Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40774 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1350).leftCharge (GramAssembly.key 1350).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1350, Integer.Sparse.eval]

theorem keyMoment1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1351) =
      Integer.Sparse.eval keyMomentRow1351 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1351).leftCharge (GramAssembly.key 1351).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1294) := by
    have ha : gramCharges (GramAssembly.key 1351).leftCharge (GramAssembly.key 1351).rightCharge = raw40775 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40775Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40775 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1351).leftCharge (GramAssembly.key 1351).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1351, Integer.Sparse.eval]

theorem keyMoment1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1352) =
      Integer.Sparse.eval keyMomentRow1352 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1352).leftCharge (GramAssembly.key 1352).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2782) := by
    have ha : gramCharges (GramAssembly.key 1352).leftCharge (GramAssembly.key 1352).rightCharge = raw40776 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40776Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40776 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1352).leftCharge (GramAssembly.key 1352).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1352, Integer.Sparse.eval]

theorem keyMoment1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1353) =
      Integer.Sparse.eval keyMomentRow1353 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1353).leftCharge (GramAssembly.key 1353).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2765) := by
    have ha : gramCharges (GramAssembly.key 1353).leftCharge (GramAssembly.key 1353).rightCharge = raw40777 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40777Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40777 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1353).leftCharge (GramAssembly.key 1353).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1353, Integer.Sparse.eval]

theorem keyMoment1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1354) =
      Integer.Sparse.eval keyMomentRow1354 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1354).leftCharge (GramAssembly.key 1354).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2109) := by
    have ha : gramCharges (GramAssembly.key 1354).leftCharge (GramAssembly.key 1354).rightCharge = raw40778 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40778Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40778 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1354).leftCharge (GramAssembly.key 1354).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1354, Integer.Sparse.eval]

theorem keyMoment1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1355) =
      Integer.Sparse.eval keyMomentRow1355 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1355).leftCharge (GramAssembly.key 1355).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2116) := by
    have ha : gramCharges (GramAssembly.key 1355).leftCharge (GramAssembly.key 1355).rightCharge = raw40779 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40779Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40779 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1355).leftCharge (GramAssembly.key 1355).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1355, Integer.Sparse.eval]

theorem keyMoment1356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1356) =
      Integer.Sparse.eval keyMomentRow1356 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1356).leftCharge (GramAssembly.key 1356).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2764) := by
    have ha : gramCharges (GramAssembly.key 1356).leftCharge (GramAssembly.key 1356).rightCharge = raw40780 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40780Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40780 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1356).leftCharge (GramAssembly.key 1356).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1356, Integer.Sparse.eval]

theorem keyMoment1357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1357) =
      Integer.Sparse.eval keyMomentRow1357 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1357).leftCharge (GramAssembly.key 1357).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2590) := by
    have ha : gramCharges (GramAssembly.key 1357).leftCharge (GramAssembly.key 1357).rightCharge = raw40781 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40781Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40781 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1357).leftCharge (GramAssembly.key 1357).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1357, Integer.Sparse.eval]

theorem keyMoment1358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1358) =
      Integer.Sparse.eval keyMomentRow1358 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1358).leftCharge (GramAssembly.key 1358).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2589) := by
    have ha : gramCharges (GramAssembly.key 1358).leftCharge (GramAssembly.key 1358).rightCharge = raw40782 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40782Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40782 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1358).leftCharge (GramAssembly.key 1358).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1358, Integer.Sparse.eval]

theorem keyMoment1359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1359) =
      Integer.Sparse.eval keyMomentRow1359 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1359).leftCharge (GramAssembly.key 1359).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2294) := by
    have ha : gramCharges (GramAssembly.key 1359).leftCharge (GramAssembly.key 1359).rightCharge = raw40783 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40783Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40783 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1359).leftCharge (GramAssembly.key 1359).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1359, Integer.Sparse.eval]

theorem keyMoment1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1360) =
      Integer.Sparse.eval keyMomentRow1360 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1360).leftCharge (GramAssembly.key 1360).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 1360).leftCharge (GramAssembly.key 1360).rightCharge = raw40784 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40784Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40784 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1360).leftCharge (GramAssembly.key 1360).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1360, Integer.Sparse.eval]

theorem keyMoment1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1361) =
      Integer.Sparse.eval keyMomentRow1361 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1361).leftCharge (GramAssembly.key 1361).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3056) := by
    have ha : gramCharges (GramAssembly.key 1361).leftCharge (GramAssembly.key 1361).rightCharge = raw40785 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40785Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40785 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1361).leftCharge (GramAssembly.key 1361).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1361, Integer.Sparse.eval]

theorem keyMoment1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1362) =
      Integer.Sparse.eval keyMomentRow1362 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1362).leftCharge (GramAssembly.key 1362).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3626) := by
    have ha : gramCharges (GramAssembly.key 1362).leftCharge (GramAssembly.key 1362).rightCharge = raw40786 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40786Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40786 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1362).leftCharge (GramAssembly.key 1362).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1362, Integer.Sparse.eval]

theorem keyMoment1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1363) =
      Integer.Sparse.eval keyMomentRow1363 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1363).leftCharge (GramAssembly.key 1363).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 1363).leftCharge (GramAssembly.key 1363).rightCharge = raw40787 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40787Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40787 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1363).leftCharge (GramAssembly.key 1363).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1363, Integer.Sparse.eval]

theorem keyMoment1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1364) =
      Integer.Sparse.eval keyMomentRow1364 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1364).leftCharge (GramAssembly.key 1364).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3396) := by
    have ha : gramCharges (GramAssembly.key 1364).leftCharge (GramAssembly.key 1364).rightCharge = raw40788 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40788Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40788 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1364).leftCharge (GramAssembly.key 1364).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1364, Integer.Sparse.eval]

theorem keyMoment1365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1365) =
      Integer.Sparse.eval keyMomentRow1365 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1365).leftCharge (GramAssembly.key 1365).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3079) := by
    have ha : gramCharges (GramAssembly.key 1365).leftCharge (GramAssembly.key 1365).rightCharge = raw40789 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40789Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40789 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1365).leftCharge (GramAssembly.key 1365).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1365, Integer.Sparse.eval]

theorem keyMoment1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1366) =
      Integer.Sparse.eval keyMomentRow1366 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1366).leftCharge (GramAssembly.key 1366).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 1366).leftCharge (GramAssembly.key 1366).rightCharge = raw40790 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40790Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40790 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1366).leftCharge (GramAssembly.key 1366).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1366, Integer.Sparse.eval]

theorem keyMoment1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1367) =
      Integer.Sparse.eval keyMomentRow1367 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1367).leftCharge (GramAssembly.key 1367).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 1367).leftCharge (GramAssembly.key 1367).rightCharge = raw40791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40791 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1367).leftCharge (GramAssembly.key 1367).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1367, Integer.Sparse.eval]

theorem keyMoment1368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1368) =
      Integer.Sparse.eval keyMomentRow1368 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1368).leftCharge (GramAssembly.key 1368).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3395) := by
    have ha : gramCharges (GramAssembly.key 1368).leftCharge (GramAssembly.key 1368).rightCharge = raw40792 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40792Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40792 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1368).leftCharge (GramAssembly.key 1368).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1368, Integer.Sparse.eval]

theorem keyMoment1369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1369) =
      Integer.Sparse.eval keyMomentRow1369 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1369).leftCharge (GramAssembly.key 1369).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3506) := by
    have ha : gramCharges (GramAssembly.key 1369).leftCharge (GramAssembly.key 1369).rightCharge = raw40793 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40793Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40793 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1369).leftCharge (GramAssembly.key 1369).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1369, Integer.Sparse.eval]

theorem keyMoment1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1370) =
      Integer.Sparse.eval keyMomentRow1370 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1370).leftCharge (GramAssembly.key 1370).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3379) := by
    have ha : gramCharges (GramAssembly.key 1370).leftCharge (GramAssembly.key 1370).rightCharge = raw40794 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40794Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40794 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1370).leftCharge (GramAssembly.key 1370).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1370, Integer.Sparse.eval]

theorem keyMoment1371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1371) =
      Integer.Sparse.eval keyMomentRow1371 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1371).leftCharge (GramAssembly.key 1371).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3505) := by
    have ha : gramCharges (GramAssembly.key 1371).leftCharge (GramAssembly.key 1371).rightCharge = raw40795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40795 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1371).leftCharge (GramAssembly.key 1371).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1371, Integer.Sparse.eval]

theorem keyMoment1372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1372) =
      Integer.Sparse.eval keyMomentRow1372 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1372).leftCharge (GramAssembly.key 1372).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3378) := by
    have ha : gramCharges (GramAssembly.key 1372).leftCharge (GramAssembly.key 1372).rightCharge = raw40796 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40796Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40796 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1372).leftCharge (GramAssembly.key 1372).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1372, Integer.Sparse.eval]

theorem keyMoment1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1373) =
      Integer.Sparse.eval keyMomentRow1373 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1373).leftCharge (GramAssembly.key 1373).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2266) := by
    have ha : gramCharges (GramAssembly.key 1373).leftCharge (GramAssembly.key 1373).rightCharge = raw40797 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40797Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40797 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1373).leftCharge (GramAssembly.key 1373).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1373, Integer.Sparse.eval]

theorem keyMoment1374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1374) =
      Integer.Sparse.eval keyMomentRow1374 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1374).leftCharge (GramAssembly.key 1374).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 1374).leftCharge (GramAssembly.key 1374).rightCharge = raw40798 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40798Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40798 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1374).leftCharge (GramAssembly.key 1374).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1374, Integer.Sparse.eval]

theorem keyMoment1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1375) =
      Integer.Sparse.eval keyMomentRow1375 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1375).leftCharge (GramAssembly.key 1375).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3040) := by
    have ha : gramCharges (GramAssembly.key 1375).leftCharge (GramAssembly.key 1375).rightCharge = raw40799 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40799Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40799 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1375).leftCharge (GramAssembly.key 1375).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1375, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

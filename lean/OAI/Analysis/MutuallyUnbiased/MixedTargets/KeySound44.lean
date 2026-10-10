import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical101
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical121
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical123
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical318
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical319

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1408) =
      Integer.Sparse.eval keyMomentRow1408 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1408).leftCharge (GramAssembly.key 1408).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 1408).leftCharge (GramAssembly.key 1408).rightCharge = raw40830 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40830Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40830 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1408).leftCharge (GramAssembly.key 1408).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1408, Integer.Sparse.eval]

theorem keyMoment1409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1409) =
      Integer.Sparse.eval keyMomentRow1409 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1409).leftCharge (GramAssembly.key 1409).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3722) := by
    have ha : gramCharges (GramAssembly.key 1409).leftCharge (GramAssembly.key 1409).rightCharge = raw40831 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40831Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40831 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1409).leftCharge (GramAssembly.key 1409).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1409, Integer.Sparse.eval]

theorem keyMoment1410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1410) =
      Integer.Sparse.eval keyMomentRow1410 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1410).leftCharge (GramAssembly.key 1410).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3723) := by
    have ha : gramCharges (GramAssembly.key 1410).leftCharge (GramAssembly.key 1410).rightCharge = raw40832 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40832Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40832 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1410).leftCharge (GramAssembly.key 1410).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1410, Integer.Sparse.eval]

theorem keyMoment1411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1411) =
      Integer.Sparse.eval keyMomentRow1411 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1411).leftCharge (GramAssembly.key 1411).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3715) := by
    have ha : gramCharges (GramAssembly.key 1411).leftCharge (GramAssembly.key 1411).rightCharge = raw40833 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40833Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40833 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1411).leftCharge (GramAssembly.key 1411).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1411, Integer.Sparse.eval]

theorem keyMoment1412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1412) =
      Integer.Sparse.eval keyMomentRow1412 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1412).leftCharge (GramAssembly.key 1412).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 1412).leftCharge (GramAssembly.key 1412).rightCharge = raw40834 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40834Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40834 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1412).leftCharge (GramAssembly.key 1412).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1412, Integer.Sparse.eval]

theorem keyMoment1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1413) =
      Integer.Sparse.eval keyMomentRow1413 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1413).leftCharge (GramAssembly.key 1413).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3899) := by
    have ha : gramCharges (GramAssembly.key 1413).leftCharge (GramAssembly.key 1413).rightCharge = raw12968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw12968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical12968 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1413).leftCharge (GramAssembly.key 1413).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1413, Integer.Sparse.eval]

theorem keyMoment1414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1414) =
      Integer.Sparse.eval keyMomentRow1414 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1414).leftCharge (GramAssembly.key 1414).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2245) := by
    have ha : gramCharges (GramAssembly.key 1414).leftCharge (GramAssembly.key 1414).rightCharge = raw15791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw15791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical15791 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1414).leftCharge (GramAssembly.key 1414).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1414, Integer.Sparse.eval]

theorem keyMoment1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1415) =
      Integer.Sparse.eval keyMomentRow1415 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1415).leftCharge (GramAssembly.key 1415).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 1415).leftCharge (GramAssembly.key 1415).rightCharge = raw15508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw15508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical15508 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1415).leftCharge (GramAssembly.key 1415).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1415, Integer.Sparse.eval]

theorem keyMoment1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1416) =
      Integer.Sparse.eval keyMomentRow1416 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1416).leftCharge (GramAssembly.key 1416).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3030) := by
    have ha : gramCharges (GramAssembly.key 1416).leftCharge (GramAssembly.key 1416).rightCharge = raw40835 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40835Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40835 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1416).leftCharge (GramAssembly.key 1416).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1416, Integer.Sparse.eval]

theorem keyMoment1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1417) =
      Integer.Sparse.eval keyMomentRow1417 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1417).leftCharge (GramAssembly.key 1417).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3378) := by
    have ha : gramCharges (GramAssembly.key 1417).leftCharge (GramAssembly.key 1417).rightCharge = raw40836 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40836Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40836 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1417).leftCharge (GramAssembly.key 1417).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1417, Integer.Sparse.eval]

theorem keyMoment1418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1418) =
      Integer.Sparse.eval keyMomentRow1418 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1418).leftCharge (GramAssembly.key 1418).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2930) := by
    have ha : gramCharges (GramAssembly.key 1418).leftCharge (GramAssembly.key 1418).rightCharge = raw40837 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40837Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40837 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1418).leftCharge (GramAssembly.key 1418).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1418, Integer.Sparse.eval]

theorem keyMoment1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1419) =
      Integer.Sparse.eval keyMomentRow1419 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1419).leftCharge (GramAssembly.key 1419).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2928) := by
    have ha : gramCharges (GramAssembly.key 1419).leftCharge (GramAssembly.key 1419).rightCharge = raw40838 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40838Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40838 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1419).leftCharge (GramAssembly.key 1419).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1419, Integer.Sparse.eval]

theorem keyMoment1420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1420) =
      Integer.Sparse.eval keyMomentRow1420 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1420).leftCharge (GramAssembly.key 1420).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2916) := by
    have ha : gramCharges (GramAssembly.key 1420).leftCharge (GramAssembly.key 1420).rightCharge = raw40839 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40839Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40839 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1420).leftCharge (GramAssembly.key 1420).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1420, Integer.Sparse.eval]

theorem keyMoment1421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1421) =
      Integer.Sparse.eval keyMomentRow1421 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1421).leftCharge (GramAssembly.key 1421).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 1421).leftCharge (GramAssembly.key 1421).rightCharge = raw7731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw7731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical7731 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1421).leftCharge (GramAssembly.key 1421).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1421, Integer.Sparse.eval]

theorem keyMoment1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1422) =
      Integer.Sparse.eval keyMomentRow1422 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1422).leftCharge (GramAssembly.key 1422).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1245) := by
    have ha : gramCharges (GramAssembly.key 1422).leftCharge (GramAssembly.key 1422).rightCharge = raw40840 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40840Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40840 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1422).leftCharge (GramAssembly.key 1422).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1422, Integer.Sparse.eval]

theorem keyMoment1423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1423) =
      Integer.Sparse.eval keyMomentRow1423 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1423).leftCharge (GramAssembly.key 1423).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 1423).leftCharge (GramAssembly.key 1423).rightCharge = raw40841 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40841Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40841 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1423).leftCharge (GramAssembly.key 1423).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1423, Integer.Sparse.eval]

theorem keyMoment1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1424) =
      Integer.Sparse.eval keyMomentRow1424 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1424).leftCharge (GramAssembly.key 1424).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1241) := by
    have ha : gramCharges (GramAssembly.key 1424).leftCharge (GramAssembly.key 1424).rightCharge = raw40842 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40842Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40842 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1424).leftCharge (GramAssembly.key 1424).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1424, Integer.Sparse.eval]

theorem keyMoment1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1425) =
      Integer.Sparse.eval keyMomentRow1425 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1425).leftCharge (GramAssembly.key 1425).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2620) := by
    have ha : gramCharges (GramAssembly.key 1425).leftCharge (GramAssembly.key 1425).rightCharge = raw40843 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40843Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40843 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1425).leftCharge (GramAssembly.key 1425).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1425, Integer.Sparse.eval]

theorem keyMoment1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1426) =
      Integer.Sparse.eval keyMomentRow1426 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1426).leftCharge (GramAssembly.key 1426).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1219) := by
    have ha : gramCharges (GramAssembly.key 1426).leftCharge (GramAssembly.key 1426).rightCharge = raw40844 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40844Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40844 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1426).leftCharge (GramAssembly.key 1426).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1426, Integer.Sparse.eval]

theorem keyMoment1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1427) =
      Integer.Sparse.eval keyMomentRow1427 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1427).leftCharge (GramAssembly.key 1427).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2617) := by
    have ha : gramCharges (GramAssembly.key 1427).leftCharge (GramAssembly.key 1427).rightCharge = raw40845 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40845Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40845 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1427).leftCharge (GramAssembly.key 1427).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1427, Integer.Sparse.eval]

theorem keyMoment1428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1428) =
      Integer.Sparse.eval keyMomentRow1428 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1428).leftCharge (GramAssembly.key 1428).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1216) := by
    have ha : gramCharges (GramAssembly.key 1428).leftCharge (GramAssembly.key 1428).rightCharge = raw40846 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40846Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40846 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1428).leftCharge (GramAssembly.key 1428).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1428, Integer.Sparse.eval]

theorem keyMoment1429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1429) =
      Integer.Sparse.eval keyMomentRow1429 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1429).leftCharge (GramAssembly.key 1429).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2557) := by
    have ha : gramCharges (GramAssembly.key 1429).leftCharge (GramAssembly.key 1429).rightCharge = raw40847 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40847Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40847 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1429).leftCharge (GramAssembly.key 1429).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1429, Integer.Sparse.eval]

theorem keyMoment1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1430) =
      Integer.Sparse.eval keyMomentRow1430 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1430).leftCharge (GramAssembly.key 1430).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 1430).leftCharge (GramAssembly.key 1430).rightCharge = raw40848 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40848Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40848 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1430).leftCharge (GramAssembly.key 1430).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1430, Integer.Sparse.eval]

theorem keyMoment1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1431) =
      Integer.Sparse.eval keyMomentRow1431 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1431).leftCharge (GramAssembly.key 1431).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2545) := by
    have ha : gramCharges (GramAssembly.key 1431).leftCharge (GramAssembly.key 1431).rightCharge = raw40849 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40849Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40849 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1431).leftCharge (GramAssembly.key 1431).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1431, Integer.Sparse.eval]

theorem keyMoment1432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1432) =
      Integer.Sparse.eval keyMomentRow1432 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1432).leftCharge (GramAssembly.key 1432).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2284) := by
    have ha : gramCharges (GramAssembly.key 1432).leftCharge (GramAssembly.key 1432).rightCharge = raw40850 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40850Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40850 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1432).leftCharge (GramAssembly.key 1432).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1432, Integer.Sparse.eval]

theorem keyMoment1433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1433) =
      Integer.Sparse.eval keyMomentRow1433 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1433).leftCharge (GramAssembly.key 1433).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2133) := by
    have ha : gramCharges (GramAssembly.key 1433).leftCharge (GramAssembly.key 1433).rightCharge = raw40851 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40851Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40851 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1433).leftCharge (GramAssembly.key 1433).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1433, Integer.Sparse.eval]

theorem keyMoment1434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1434) =
      Integer.Sparse.eval keyMomentRow1434 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1434).leftCharge (GramAssembly.key 1434).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1826) := by
    have ha : gramCharges (GramAssembly.key 1434).leftCharge (GramAssembly.key 1434).rightCharge = raw40852 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40852Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40852 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1434).leftCharge (GramAssembly.key 1434).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1434, Integer.Sparse.eval]

theorem keyMoment1435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1435) =
      Integer.Sparse.eval keyMomentRow1435 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1435).leftCharge (GramAssembly.key 1435).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2253) := by
    have ha : gramCharges (GramAssembly.key 1435).leftCharge (GramAssembly.key 1435).rightCharge = raw40853 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40853Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40853 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1435).leftCharge (GramAssembly.key 1435).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1435, Integer.Sparse.eval]

theorem keyMoment1436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1436) =
      Integer.Sparse.eval keyMomentRow1436 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1436).leftCharge (GramAssembly.key 1436).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2108) := by
    have ha : gramCharges (GramAssembly.key 1436).leftCharge (GramAssembly.key 1436).rightCharge = raw40854 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40854Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40854 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1436).leftCharge (GramAssembly.key 1436).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1436, Integer.Sparse.eval]

theorem keyMoment1437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1437) =
      Integer.Sparse.eval keyMomentRow1437 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1437).leftCharge (GramAssembly.key 1437).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1809) := by
    have ha : gramCharges (GramAssembly.key 1437).leftCharge (GramAssembly.key 1437).rightCharge = raw40855 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40855Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40855 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1437).leftCharge (GramAssembly.key 1437).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1437, Integer.Sparse.eval]

theorem keyMoment1438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1438) =
      Integer.Sparse.eval keyMomentRow1438 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1438).leftCharge (GramAssembly.key 1438).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1824) := by
    have ha : gramCharges (GramAssembly.key 1438).leftCharge (GramAssembly.key 1438).rightCharge = raw40856 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40856Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40856 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1438).leftCharge (GramAssembly.key 1438).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1438, Integer.Sparse.eval]

theorem keyMoment1439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1439) =
      Integer.Sparse.eval keyMomentRow1439 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1439).leftCharge (GramAssembly.key 1439).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2089) := by
    have ha : gramCharges (GramAssembly.key 1439).leftCharge (GramAssembly.key 1439).rightCharge = raw40857 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40857Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40857 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1439).leftCharge (GramAssembly.key 1439).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1439, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

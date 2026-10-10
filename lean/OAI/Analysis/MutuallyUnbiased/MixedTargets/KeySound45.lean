import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical319

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1440) =
      Integer.Sparse.eval keyMomentRow1440 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1440).leftCharge (GramAssembly.key 1440).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1806) := by
    have ha : gramCharges (GramAssembly.key 1440).leftCharge (GramAssembly.key 1440).rightCharge = raw40858 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40858Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40858 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1440).leftCharge (GramAssembly.key 1440).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1440, Integer.Sparse.eval]

theorem keyMoment1441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1441) =
      Integer.Sparse.eval keyMomentRow1441 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1441).leftCharge (GramAssembly.key 1441).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1791) := by
    have ha : gramCharges (GramAssembly.key 1441).leftCharge (GramAssembly.key 1441).rightCharge = raw40859 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40859Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40859 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1441).leftCharge (GramAssembly.key 1441).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1441, Integer.Sparse.eval]

theorem keyMoment1442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1442) =
      Integer.Sparse.eval keyMomentRow1442 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1442).leftCharge (GramAssembly.key 1442).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2253) := by
    have ha : gramCharges (GramAssembly.key 1442).leftCharge (GramAssembly.key 1442).rightCharge = raw40860 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40860Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40860 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1442).leftCharge (GramAssembly.key 1442).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1442, Integer.Sparse.eval]

theorem keyMoment1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1443) =
      Integer.Sparse.eval keyMomentRow1443 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1443).leftCharge (GramAssembly.key 1443).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2714) := by
    have ha : gramCharges (GramAssembly.key 1443).leftCharge (GramAssembly.key 1443).rightCharge = raw40861 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40861Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40861 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1443).leftCharge (GramAssembly.key 1443).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1443, Integer.Sparse.eval]

theorem keyMoment1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1444) =
      Integer.Sparse.eval keyMomentRow1444 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1444).leftCharge (GramAssembly.key 1444).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3032) := by
    have ha : gramCharges (GramAssembly.key 1444).leftCharge (GramAssembly.key 1444).rightCharge = raw40862 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40862Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40862 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1444).leftCharge (GramAssembly.key 1444).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1444, Integer.Sparse.eval]

theorem keyMoment1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1445) =
      Integer.Sparse.eval keyMomentRow1445 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1445).leftCharge (GramAssembly.key 1445).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3803) := by
    have ha : gramCharges (GramAssembly.key 1445).leftCharge (GramAssembly.key 1445).rightCharge = raw40863 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40863Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40863 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1445).leftCharge (GramAssembly.key 1445).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1445, Integer.Sparse.eval]

theorem keyMoment1446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1446) =
      Integer.Sparse.eval keyMomentRow1446 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1446).leftCharge (GramAssembly.key 1446).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3788) := by
    have ha : gramCharges (GramAssembly.key 1446).leftCharge (GramAssembly.key 1446).rightCharge = raw40864 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40864Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40864 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1446).leftCharge (GramAssembly.key 1446).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1446, Integer.Sparse.eval]

theorem keyMoment1447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1447) =
      Integer.Sparse.eval keyMomentRow1447 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1447).leftCharge (GramAssembly.key 1447).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3365) := by
    have ha : gramCharges (GramAssembly.key 1447).leftCharge (GramAssembly.key 1447).rightCharge = raw40865 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40865Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40865 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1447).leftCharge (GramAssembly.key 1447).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1447, Integer.Sparse.eval]

theorem keyMoment1448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1448) =
      Integer.Sparse.eval keyMomentRow1448 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1448).leftCharge (GramAssembly.key 1448).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3577) := by
    have ha : gramCharges (GramAssembly.key 1448).leftCharge (GramAssembly.key 1448).rightCharge = raw40866 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40866Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40866 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1448).leftCharge (GramAssembly.key 1448).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1448, Integer.Sparse.eval]

theorem keyMoment1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1449) =
      Integer.Sparse.eval keyMomentRow1449 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1449).leftCharge (GramAssembly.key 1449).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2812) := by
    have ha : gramCharges (GramAssembly.key 1449).leftCharge (GramAssembly.key 1449).rightCharge = raw40867 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40867Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40867 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1449).leftCharge (GramAssembly.key 1449).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1449, Integer.Sparse.eval]

theorem keyMoment1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1450) =
      Integer.Sparse.eval keyMomentRow1450 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1450).leftCharge (GramAssembly.key 1450).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3698) := by
    have ha : gramCharges (GramAssembly.key 1450).leftCharge (GramAssembly.key 1450).rightCharge = raw40868 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40868Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40868 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1450).leftCharge (GramAssembly.key 1450).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1450, Integer.Sparse.eval]

theorem keyMoment1451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1451) =
      Integer.Sparse.eval keyMomentRow1451 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1451).leftCharge (GramAssembly.key 1451).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2810) := by
    have ha : gramCharges (GramAssembly.key 1451).leftCharge (GramAssembly.key 1451).rightCharge = raw40869 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40869Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40869 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1451).leftCharge (GramAssembly.key 1451).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1451, Integer.Sparse.eval]

theorem keyMoment1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1452) =
      Integer.Sparse.eval keyMomentRow1452 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1452).leftCharge (GramAssembly.key 1452).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3674) := by
    have ha : gramCharges (GramAssembly.key 1452).leftCharge (GramAssembly.key 1452).rightCharge = raw40870 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40870Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40870 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1452).leftCharge (GramAssembly.key 1452).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1452, Integer.Sparse.eval]

theorem keyMoment1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1453) =
      Integer.Sparse.eval keyMomentRow1453 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1453).leftCharge (GramAssembly.key 1453).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2798) := by
    have ha : gramCharges (GramAssembly.key 1453).leftCharge (GramAssembly.key 1453).rightCharge = raw40871 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40871Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40871 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1453).leftCharge (GramAssembly.key 1453).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1453, Integer.Sparse.eval]

theorem keyMoment1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1454) =
      Integer.Sparse.eval keyMomentRow1454 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1454).leftCharge (GramAssembly.key 1454).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2233) := by
    have ha : gramCharges (GramAssembly.key 1454).leftCharge (GramAssembly.key 1454).rightCharge = raw40872 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40872Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40872 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1454).leftCharge (GramAssembly.key 1454).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1454, Integer.Sparse.eval]

theorem keyMoment1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1455) =
      Integer.Sparse.eval keyMomentRow1455 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1455).leftCharge (GramAssembly.key 1455).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2892) := by
    have ha : gramCharges (GramAssembly.key 1455).leftCharge (GramAssembly.key 1455).rightCharge = raw40873 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40873Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40873 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1455).leftCharge (GramAssembly.key 1455).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1455, Integer.Sparse.eval]

theorem keyMoment1456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1456) =
      Integer.Sparse.eval keyMomentRow1456 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1456).leftCharge (GramAssembly.key 1456).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2513) := by
    have ha : gramCharges (GramAssembly.key 1456).leftCharge (GramAssembly.key 1456).rightCharge = raw40874 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40874Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40874 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1456).leftCharge (GramAssembly.key 1456).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1456, Integer.Sparse.eval]

theorem keyMoment1457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1457) =
      Integer.Sparse.eval keyMomentRow1457 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1457).leftCharge (GramAssembly.key 1457).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1133) := by
    have ha : gramCharges (GramAssembly.key 1457).leftCharge (GramAssembly.key 1457).rightCharge = raw40875 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40875Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40875 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1457).leftCharge (GramAssembly.key 1457).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1457, Integer.Sparse.eval]

theorem keyMoment1458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1458) =
      Integer.Sparse.eval keyMomentRow1458 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1458).leftCharge (GramAssembly.key 1458).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2494) := by
    have ha : gramCharges (GramAssembly.key 1458).leftCharge (GramAssembly.key 1458).rightCharge = raw40876 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40876Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40876 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1458).leftCharge (GramAssembly.key 1458).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1458, Integer.Sparse.eval]

theorem keyMoment1459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1459) =
      Integer.Sparse.eval keyMomentRow1459 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1459).leftCharge (GramAssembly.key 1459).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1130) := by
    have ha : gramCharges (GramAssembly.key 1459).leftCharge (GramAssembly.key 1459).rightCharge = raw40877 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40877Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40877 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1459).leftCharge (GramAssembly.key 1459).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1459, Integer.Sparse.eval]

theorem keyMoment1460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1460) =
      Integer.Sparse.eval keyMomentRow1460 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1460).leftCharge (GramAssembly.key 1460).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2438) := by
    have ha : gramCharges (GramAssembly.key 1460).leftCharge (GramAssembly.key 1460).rightCharge = raw40878 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40878Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40878 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1460).leftCharge (GramAssembly.key 1460).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1460, Integer.Sparse.eval]

theorem keyMoment1461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1461) =
      Integer.Sparse.eval keyMomentRow1461 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1461).leftCharge (GramAssembly.key 1461).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1113) := by
    have ha : gramCharges (GramAssembly.key 1461).leftCharge (GramAssembly.key 1461).rightCharge = raw40879 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40879Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40879 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1461).leftCharge (GramAssembly.key 1461).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1461, Integer.Sparse.eval]

theorem keyMoment1462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1462) =
      Integer.Sparse.eval keyMomentRow1462 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1462).leftCharge (GramAssembly.key 1462).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 607) := by
    have ha : gramCharges (GramAssembly.key 1462).leftCharge (GramAssembly.key 1462).rightCharge = raw40880 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40880Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40880 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1462).leftCharge (GramAssembly.key 1462).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1462, Integer.Sparse.eval]

theorem keyMoment1463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1463) =
      Integer.Sparse.eval keyMomentRow1463 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1463).leftCharge (GramAssembly.key 1463).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1058) := by
    have ha : gramCharges (GramAssembly.key 1463).leftCharge (GramAssembly.key 1463).rightCharge = raw40881 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40881Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40881 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1463).leftCharge (GramAssembly.key 1463).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1463, Integer.Sparse.eval]

theorem keyMoment1464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1464) =
      Integer.Sparse.eval keyMomentRow1464 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1464).leftCharge (GramAssembly.key 1464).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 604) := by
    have ha : gramCharges (GramAssembly.key 1464).leftCharge (GramAssembly.key 1464).rightCharge = raw40882 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40882Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40882 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1464).leftCharge (GramAssembly.key 1464).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1464, Integer.Sparse.eval]

theorem keyMoment1465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1465) =
      Integer.Sparse.eval keyMomentRow1465 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1465).leftCharge (GramAssembly.key 1465).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 946) := by
    have ha : gramCharges (GramAssembly.key 1465).leftCharge (GramAssembly.key 1465).rightCharge = raw40883 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40883Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40883 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1465).leftCharge (GramAssembly.key 1465).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1465, Integer.Sparse.eval]

theorem keyMoment1466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1466) =
      Integer.Sparse.eval keyMomentRow1466 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1466).leftCharge (GramAssembly.key 1466).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 582) := by
    have ha : gramCharges (GramAssembly.key 1466).leftCharge (GramAssembly.key 1466).rightCharge = raw40884 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40884Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40884 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1466).leftCharge (GramAssembly.key 1466).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1466, Integer.Sparse.eval]

theorem keyMoment1467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1467) =
      Integer.Sparse.eval keyMomentRow1467 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1467).leftCharge (GramAssembly.key 1467).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 944) := by
    have ha : gramCharges (GramAssembly.key 1467).leftCharge (GramAssembly.key 1467).rightCharge = raw40885 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40885Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40885 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1467).leftCharge (GramAssembly.key 1467).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1467, Integer.Sparse.eval]

theorem keyMoment1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1468) =
      Integer.Sparse.eval keyMomentRow1468 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1468).leftCharge (GramAssembly.key 1468).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 580) := by
    have ha : gramCharges (GramAssembly.key 1468).leftCharge (GramAssembly.key 1468).rightCharge = raw40886 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40886Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40886 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1468).leftCharge (GramAssembly.key 1468).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1468, Integer.Sparse.eval]

theorem keyMoment1469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1469) =
      Integer.Sparse.eval keyMomentRow1469 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1469).leftCharge (GramAssembly.key 1469).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2138) := by
    have ha : gramCharges (GramAssembly.key 1469).leftCharge (GramAssembly.key 1469).rightCharge = raw40887 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40887Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40887 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1469).leftCharge (GramAssembly.key 1469).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1469, Integer.Sparse.eval]

theorem keyMoment1470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1470) =
      Integer.Sparse.eval keyMomentRow1470 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1470).leftCharge (GramAssembly.key 1470).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1829) := by
    have ha : gramCharges (GramAssembly.key 1470).leftCharge (GramAssembly.key 1470).rightCharge = raw40888 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40888Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40888 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1470).leftCharge (GramAssembly.key 1470).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1470, Integer.Sparse.eval]

theorem keyMoment1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1471) =
      Integer.Sparse.eval keyMomentRow1471 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1471).leftCharge (GramAssembly.key 1471).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2039) := by
    have ha : gramCharges (GramAssembly.key 1471).leftCharge (GramAssembly.key 1471).rightCharge = raw40889 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40889Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40889 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1471).leftCharge (GramAssembly.key 1471).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1471, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

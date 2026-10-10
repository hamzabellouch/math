import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical319

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1504) =
      Integer.Sparse.eval keyMomentRow1504 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1504).leftCharge (GramAssembly.key 1504).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2350) := by
    have ha : gramCharges (GramAssembly.key 1504).leftCharge (GramAssembly.key 1504).rightCharge = raw40922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40922 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1504).leftCharge (GramAssembly.key 1504).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1504, Integer.Sparse.eval]

theorem keyMoment1505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1505) =
      Integer.Sparse.eval keyMomentRow1505 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1505).leftCharge (GramAssembly.key 1505).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2356) := by
    have ha : gramCharges (GramAssembly.key 1505).leftCharge (GramAssembly.key 1505).rightCharge = raw40923 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40923Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40923 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1505).leftCharge (GramAssembly.key 1505).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1505, Integer.Sparse.eval]

theorem keyMoment1506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1506) =
      Integer.Sparse.eval keyMomentRow1506 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1506).leftCharge (GramAssembly.key 1506).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2352) := by
    have ha : gramCharges (GramAssembly.key 1506).leftCharge (GramAssembly.key 1506).rightCharge = raw40924 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40924Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40924 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1506).leftCharge (GramAssembly.key 1506).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1506, Integer.Sparse.eval]

theorem keyMoment1507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1507) =
      Integer.Sparse.eval keyMomentRow1507 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1507).leftCharge (GramAssembly.key 1507).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2348) := by
    have ha : gramCharges (GramAssembly.key 1507).leftCharge (GramAssembly.key 1507).rightCharge = raw40925 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40925Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40925 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1507).leftCharge (GramAssembly.key 1507).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1507, Integer.Sparse.eval]

theorem keyMoment1508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1508) =
      Integer.Sparse.eval keyMomentRow1508 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1508).leftCharge (GramAssembly.key 1508).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2361) := by
    have ha : gramCharges (GramAssembly.key 1508).leftCharge (GramAssembly.key 1508).rightCharge = raw40926 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40926Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40926 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1508).leftCharge (GramAssembly.key 1508).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1508, Integer.Sparse.eval]

theorem keyMoment1509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1509) =
      Integer.Sparse.eval keyMomentRow1509 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1509).leftCharge (GramAssembly.key 1509).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2349) := by
    have ha : gramCharges (GramAssembly.key 1509).leftCharge (GramAssembly.key 1509).rightCharge = raw40927 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40927Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40927 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1509).leftCharge (GramAssembly.key 1509).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1509, Integer.Sparse.eval]

theorem keyMoment1510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1510) =
      Integer.Sparse.eval keyMomentRow1510 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1510).leftCharge (GramAssembly.key 1510).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2355) := by
    have ha : gramCharges (GramAssembly.key 1510).leftCharge (GramAssembly.key 1510).rightCharge = raw40928 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40928Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40928 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1510).leftCharge (GramAssembly.key 1510).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1510, Integer.Sparse.eval]

theorem keyMoment1511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1511) =
      Integer.Sparse.eval keyMomentRow1511 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1511).leftCharge (GramAssembly.key 1511).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1119) := by
    have ha : gramCharges (GramAssembly.key 1511).leftCharge (GramAssembly.key 1511).rightCharge = raw40929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40929 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1511).leftCharge (GramAssembly.key 1511).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1511, Integer.Sparse.eval]

theorem keyMoment1512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1512) =
      Integer.Sparse.eval keyMomentRow1512 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1512).leftCharge (GramAssembly.key 1512).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2347) := by
    have ha : gramCharges (GramAssembly.key 1512).leftCharge (GramAssembly.key 1512).rightCharge = raw40930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40930 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1512).leftCharge (GramAssembly.key 1512).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1512, Integer.Sparse.eval]

theorem keyMoment1513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1513) =
      Integer.Sparse.eval keyMomentRow1513 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1513).leftCharge (GramAssembly.key 1513).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 952) := by
    have ha : gramCharges (GramAssembly.key 1513).leftCharge (GramAssembly.key 1513).rightCharge = raw40931 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40931Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40931 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1513).leftCharge (GramAssembly.key 1513).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1513, Integer.Sparse.eval]

theorem keyMoment1514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1514) =
      Integer.Sparse.eval keyMomentRow1514 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1514).leftCharge (GramAssembly.key 1514).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 588) := by
    have ha : gramCharges (GramAssembly.key 1514).leftCharge (GramAssembly.key 1514).rightCharge = raw40932 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40932Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40932 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1514).leftCharge (GramAssembly.key 1514).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1514, Integer.Sparse.eval]

theorem keyMoment1515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1515) =
      Integer.Sparse.eval keyMomentRow1515 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1515).leftCharge (GramAssembly.key 1515).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2294) := by
    have ha : gramCharges (GramAssembly.key 1515).leftCharge (GramAssembly.key 1515).rightCharge = raw40933 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40933Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40933 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1515).leftCharge (GramAssembly.key 1515).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1515, Integer.Sparse.eval]

theorem keyMoment1516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1516) =
      Integer.Sparse.eval keyMomentRow1516 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1516).leftCharge (GramAssembly.key 1516).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2279) := by
    have ha : gramCharges (GramAssembly.key 1516).leftCharge (GramAssembly.key 1516).rightCharge = raw40934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40934 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1516).leftCharge (GramAssembly.key 1516).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1516, Integer.Sparse.eval]

theorem keyMoment1517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1517) =
      Integer.Sparse.eval keyMomentRow1517 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1517).leftCharge (GramAssembly.key 1517).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2115) := by
    have ha : gramCharges (GramAssembly.key 1517).leftCharge (GramAssembly.key 1517).rightCharge = raw40935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40935 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1517).leftCharge (GramAssembly.key 1517).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1517, Integer.Sparse.eval]

theorem keyMoment1518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1518) =
      Integer.Sparse.eval keyMomentRow1518 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1518).leftCharge (GramAssembly.key 1518).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1817) := by
    have ha : gramCharges (GramAssembly.key 1518).leftCharge (GramAssembly.key 1518).rightCharge = raw40936 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40936Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40936 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1518).leftCharge (GramAssembly.key 1518).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1518, Integer.Sparse.eval]

theorem keyMoment1519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1519) =
      Integer.Sparse.eval keyMomentRow1519 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1519).leftCharge (GramAssembly.key 1519).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2266) := by
    have ha : gramCharges (GramAssembly.key 1519).leftCharge (GramAssembly.key 1519).rightCharge = raw40937 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40937Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40937 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1519).leftCharge (GramAssembly.key 1519).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1519, Integer.Sparse.eval]

theorem keyMoment1520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1520) =
      Integer.Sparse.eval keyMomentRow1520 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1520).leftCharge (GramAssembly.key 1520).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2110) := by
    have ha : gramCharges (GramAssembly.key 1520).leftCharge (GramAssembly.key 1520).rightCharge = raw40938 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40938Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40938 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1520).leftCharge (GramAssembly.key 1520).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1520, Integer.Sparse.eval]

theorem keyMoment1521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1521) =
      Integer.Sparse.eval keyMomentRow1521 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1521).leftCharge (GramAssembly.key 1521).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1814) := by
    have ha : gramCharges (GramAssembly.key 1521).leftCharge (GramAssembly.key 1521).rightCharge = raw40939 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40939Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40939 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1521).leftCharge (GramAssembly.key 1521).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1521, Integer.Sparse.eval]

theorem keyMoment1522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1522) =
      Integer.Sparse.eval keyMomentRow1522 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1522).leftCharge (GramAssembly.key 1522).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2058) := by
    have ha : gramCharges (GramAssembly.key 1522).leftCharge (GramAssembly.key 1522).rightCharge = raw40940 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40940Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40940 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1522).leftCharge (GramAssembly.key 1522).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1522, Integer.Sparse.eval]

theorem keyMoment1523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1523) =
      Integer.Sparse.eval keyMomentRow1523 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1523).leftCharge (GramAssembly.key 1523).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2245) := by
    have ha : gramCharges (GramAssembly.key 1523).leftCharge (GramAssembly.key 1523).rightCharge = raw40941 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40941Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40941 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1523).leftCharge (GramAssembly.key 1523).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1523, Integer.Sparse.eval]

theorem keyMoment1524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1524) =
      Integer.Sparse.eval keyMomentRow1524 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1524).leftCharge (GramAssembly.key 1524).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2028) := by
    have ha : gramCharges (GramAssembly.key 1524).leftCharge (GramAssembly.key 1524).rightCharge = raw40942 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40942Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40942 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1524).leftCharge (GramAssembly.key 1524).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1524, Integer.Sparse.eval]

theorem keyMoment1525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1525) =
      Integer.Sparse.eval keyMomentRow1525 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1525).leftCharge (GramAssembly.key 1525).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1804) := by
    have ha : gramCharges (GramAssembly.key 1525).leftCharge (GramAssembly.key 1525).rightCharge = raw40943 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40943Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40943 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1525).leftCharge (GramAssembly.key 1525).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1525, Integer.Sparse.eval]

theorem keyMoment1526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1526) =
      Integer.Sparse.eval keyMomentRow1526 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1526).leftCharge (GramAssembly.key 1526).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1811) := by
    have ha : gramCharges (GramAssembly.key 1526).leftCharge (GramAssembly.key 1526).rightCharge = raw40944 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40944Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40944 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1526).leftCharge (GramAssembly.key 1526).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1526, Integer.Sparse.eval]

theorem keyMoment1527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1527) =
      Integer.Sparse.eval keyMomentRow1527 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1527).leftCharge (GramAssembly.key 1527).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2023) := by
    have ha : gramCharges (GramAssembly.key 1527).leftCharge (GramAssembly.key 1527).rightCharge = raw40945 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40945Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40945 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1527).leftCharge (GramAssembly.key 1527).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1527, Integer.Sparse.eval]

theorem keyMoment1528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1528) =
      Integer.Sparse.eval keyMomentRow1528 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1528).leftCharge (GramAssembly.key 1528).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1966) := by
    have ha : gramCharges (GramAssembly.key 1528).leftCharge (GramAssembly.key 1528).rightCharge = raw40946 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40946Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40946 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1528).leftCharge (GramAssembly.key 1528).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1528, Integer.Sparse.eval]

theorem keyMoment1529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1529) =
      Integer.Sparse.eval keyMomentRow1529 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1529).leftCharge (GramAssembly.key 1529).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3626) := by
    have ha : gramCharges (GramAssembly.key 1529).leftCharge (GramAssembly.key 1529).rightCharge = raw40947 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40947Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40947 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1529).leftCharge (GramAssembly.key 1529).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1529, Integer.Sparse.eval]

theorem keyMoment1530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1530) =
      Integer.Sparse.eval keyMomentRow1530 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1530).leftCharge (GramAssembly.key 1530).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3814) := by
    have ha : gramCharges (GramAssembly.key 1530).leftCharge (GramAssembly.key 1530).rightCharge = raw40948 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40948Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40948 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1530).leftCharge (GramAssembly.key 1530).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1530, Integer.Sparse.eval]

theorem keyMoment1531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1531) =
      Integer.Sparse.eval keyMomentRow1531 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1531).leftCharge (GramAssembly.key 1531).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3732) := by
    have ha : gramCharges (GramAssembly.key 1531).leftCharge (GramAssembly.key 1531).rightCharge = raw40949 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40949Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40949 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1531).leftCharge (GramAssembly.key 1531).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1531, Integer.Sparse.eval]

theorem keyMoment1532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1532) =
      Integer.Sparse.eval keyMomentRow1532 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1532).leftCharge (GramAssembly.key 1532).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1814) := by
    have ha : gramCharges (GramAssembly.key 1532).leftCharge (GramAssembly.key 1532).rightCharge = raw40950 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40950Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40950 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1532).leftCharge (GramAssembly.key 1532).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1532, Integer.Sparse.eval]

theorem keyMoment1533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1533) =
      Integer.Sparse.eval keyMomentRow1533 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1533).leftCharge (GramAssembly.key 1533).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3809) := by
    have ha : gramCharges (GramAssembly.key 1533).leftCharge (GramAssembly.key 1533).rightCharge = raw40951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40951 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1533).leftCharge (GramAssembly.key 1533).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1533, Integer.Sparse.eval]

theorem keyMoment1534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1534) =
      Integer.Sparse.eval keyMomentRow1534 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1534).leftCharge (GramAssembly.key 1534).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3789) := by
    have ha : gramCharges (GramAssembly.key 1534).leftCharge (GramAssembly.key 1534).rightCharge = raw40952 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40952Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40952 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1534).leftCharge (GramAssembly.key 1534).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1534, Integer.Sparse.eval]

theorem keyMoment1535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1535) =
      Integer.Sparse.eval keyMomentRow1535 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1535).leftCharge (GramAssembly.key 1535).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3708) := by
    have ha : gramCharges (GramAssembly.key 1535).leftCharge (GramAssembly.key 1535).rightCharge = raw40953 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40953Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40953 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1535).leftCharge (GramAssembly.key 1535).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1535, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI

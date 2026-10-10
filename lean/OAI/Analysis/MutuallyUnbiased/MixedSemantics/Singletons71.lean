import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical11

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4544 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4544 node4544Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1129 node1129Labels + mixedMoment B node3263 node3263Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1368 singletonSmall4544
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4544) = raw1368Labels := by decide +kernel
  rw [hl, canonical1368 B hB] at h
  have hc0 : mixedMoment B raw1368 (Fin.cases (0 : Fin 2) singletonSmall4544) =
      mixedMoment B node1129 node1129Labels := by
    have ha : raw1368 = raw1369 := by apply Matrix.ext; unfold raw1368 raw1369; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4544 = raw1369Labels := by decide +kernel
    rw [ha, hj, canonical1369 B hB]
  have hc1 : mixedMoment B raw1368 (Fin.cases (1 : Fin 2) singletonSmall4544) =
      mixedMoment B node3263 node3263Labels := by
    have ha : raw1368 = raw1370 := by apply Matrix.ext; unfold raw1368 raw1370; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4544 = raw1370Labels := by decide +kernel
    rw [ha, hj, canonical1370 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4546 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4546 node4546Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1131 node1131Labels + mixedMoment B node3264 node3264Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1371 singletonSmall4546
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4546) = raw1371Labels := by decide +kernel
  rw [hl, canonical1371 B hB] at h
  have hc0 : mixedMoment B raw1371 (Fin.cases (0 : Fin 2) singletonSmall4546) =
      mixedMoment B node1131 node1131Labels := by
    have ha : raw1371 = raw1372 := by apply Matrix.ext; unfold raw1371 raw1372; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4546 = raw1372Labels := by decide +kernel
    rw [ha, hj, canonical1372 B hB]
  have hc1 : mixedMoment B raw1371 (Fin.cases (1 : Fin 2) singletonSmall4546) =
      mixedMoment B node3264 node3264Labels := by
    have ha : raw1371 = raw1373 := by apply Matrix.ext; unfold raw1371 raw1373; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4546 = raw1373Labels := by decide +kernel
    rw [ha, hj, canonical1373 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4549 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4549 node4549Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1134 node1134Labels + mixedMoment B node3265 node3265Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1374 singletonSmall4549
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4549) = raw1374Labels := by decide +kernel
  rw [hl, canonical1374 B hB] at h
  have hc0 : mixedMoment B raw1374 (Fin.cases (0 : Fin 2) singletonSmall4549) =
      mixedMoment B node1134 node1134Labels := by
    have ha : raw1374 = raw1375 := by apply Matrix.ext; unfold raw1374 raw1375; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4549 = raw1375Labels := by decide +kernel
    rw [ha, hj, canonical1375 B hB]
  have hc1 : mixedMoment B raw1374 (Fin.cases (1 : Fin 2) singletonSmall4549) =
      mixedMoment B node3265 node3265Labels := by
    have ha : raw1374 = raw1376 := by apply Matrix.ext; unfold raw1374 raw1376; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4549 = raw1376Labels := by decide +kernel
    rw [ha, hj, canonical1376 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4550 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4550 node4550Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1135 node1135Labels + mixedMoment B node3269 node3269Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1377 singletonSmall4550
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4550) = raw1377Labels := by decide +kernel
  rw [hl, canonical1377 B hB] at h
  have hc0 : mixedMoment B raw1377 (Fin.cases (0 : Fin 2) singletonSmall4550) =
      mixedMoment B node1135 node1135Labels := by
    have ha : raw1377 = raw1378 := by apply Matrix.ext; unfold raw1377 raw1378; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4550 = raw1378Labels := by decide +kernel
    rw [ha, hj, canonical1378 B hB]
  have hc1 : mixedMoment B raw1377 (Fin.cases (1 : Fin 2) singletonSmall4550) =
      mixedMoment B node3269 node3269Labels := by
    have ha : raw1377 = raw1379 := by apply Matrix.ext; unfold raw1377 raw1379; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4550 = raw1379Labels := by decide +kernel
    rw [ha, hj, canonical1379 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4551 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4551 node4551Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1136 node1136Labels + mixedMoment B node3273 node3273Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1380 singletonSmall4551
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4551) = raw1380Labels := by decide +kernel
  rw [hl, canonical1380 B hB] at h
  have hc0 : mixedMoment B raw1380 (Fin.cases (0 : Fin 2) singletonSmall4551) =
      mixedMoment B node1136 node1136Labels := by
    have ha : raw1380 = raw1381 := by apply Matrix.ext; unfold raw1380 raw1381; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4551 = raw1381Labels := by decide +kernel
    rw [ha, hj, canonical1381 B hB]
  have hc1 : mixedMoment B raw1380 (Fin.cases (1 : Fin 2) singletonSmall4551) =
      mixedMoment B node3273 node3273Labels := by
    have ha : raw1380 = raw1382 := by apply Matrix.ext; unfold raw1380 raw1382; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4551 = raw1382Labels := by decide +kernel
    rw [ha, hj, canonical1382 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4553 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4553 node4553Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1138 node1138Labels + mixedMoment B node3270 node3270Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1383 singletonSmall4553
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4553) = raw1383Labels := by decide +kernel
  rw [hl, canonical1383 B hB] at h
  have hc0 : mixedMoment B raw1383 (Fin.cases (0 : Fin 2) singletonSmall4553) =
      mixedMoment B node1138 node1138Labels := by
    have ha : raw1383 = raw1384 := by apply Matrix.ext; unfold raw1383 raw1384; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4553 = raw1384Labels := by decide +kernel
    rw [ha, hj, canonical1384 B hB]
  have hc1 : mixedMoment B raw1383 (Fin.cases (1 : Fin 2) singletonSmall4553) =
      mixedMoment B node3270 node3270Labels := by
    have ha : raw1383 = raw1385 := by apply Matrix.ext; unfold raw1383 raw1385; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4553 = raw1385Labels := by decide +kernel
    rw [ha, hj, canonical1385 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4554 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4554 node4554Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1139 node1139Labels + mixedMoment B node3274 node3274Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1386 singletonSmall4554
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4554) = raw1386Labels := by decide +kernel
  rw [hl, canonical1386 B hB] at h
  have hc0 : mixedMoment B raw1386 (Fin.cases (0 : Fin 2) singletonSmall4554) =
      mixedMoment B node1139 node1139Labels := by
    have ha : raw1386 = raw1387 := by apply Matrix.ext; unfold raw1386 raw1387; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4554 = raw1387Labels := by decide +kernel
    rw [ha, hj, canonical1387 B hB]
  have hc1 : mixedMoment B raw1386 (Fin.cases (1 : Fin 2) singletonSmall4554) =
      mixedMoment B node3274 node3274Labels := by
    have ha : raw1386 = raw1388 := by apply Matrix.ext; unfold raw1386 raw1388; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4554 = raw1388Labels := by decide +kernel
    rw [ha, hj, canonical1388 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4555 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4555 node4555Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1140 node1140Labels + mixedMoment B node3275 node3275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1389 singletonSmall4555
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4555) = raw1389Labels := by decide +kernel
  rw [hl, canonical1389 B hB] at h
  have hc0 : mixedMoment B raw1389 (Fin.cases (0 : Fin 2) singletonSmall4555) =
      mixedMoment B node1140 node1140Labels := by
    have ha : raw1389 = raw1390 := by apply Matrix.ext; unfold raw1389 raw1390; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4555 = raw1390Labels := by decide +kernel
    rw [ha, hj, canonical1390 B hB]
  have hc1 : mixedMoment B raw1389 (Fin.cases (1 : Fin 2) singletonSmall4555) =
      mixedMoment B node3275 node3275Labels := by
    have ha : raw1389 = raw1391 := by apply Matrix.ext; unfold raw1389 raw1391; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4555 = raw1391Labels := by decide +kernel
    rw [ha, hj, canonical1391 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4557 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4557 node4557Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1143 node1143Labels + mixedMoment B node2167 node2167Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1392 singletonSmall4557
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4557) = raw1392Labels := by decide +kernel
  rw [hl, canonical1392 B hB] at h
  have hc0 : mixedMoment B raw1392 (Fin.cases (0 : Fin 2) singletonSmall4557) =
      mixedMoment B node1143 node1143Labels := by
    have ha : raw1392 = raw1393 := by apply Matrix.ext; unfold raw1392 raw1393; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4557 = raw1393Labels := by decide +kernel
    rw [ha, hj, canonical1393 B hB]
  have hc1 : mixedMoment B raw1392 (Fin.cases (1 : Fin 2) singletonSmall4557) =
      mixedMoment B node2167 node2167Labels := by
    have ha : raw1392 = raw1394 := by apply Matrix.ext; unfold raw1392 raw1394; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4557 = raw1394Labels := by decide +kernel
    rw [ha, hj, canonical1394 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4558 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4558 node4558Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1144 node1144Labels + mixedMoment B node3276 node3276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1395 singletonSmall4558
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4558) = raw1395Labels := by decide +kernel
  rw [hl, canonical1395 B hB] at h
  have hc0 : mixedMoment B raw1395 (Fin.cases (0 : Fin 2) singletonSmall4558) =
      mixedMoment B node1144 node1144Labels := by
    have ha : raw1395 = raw1396 := by apply Matrix.ext; unfold raw1395 raw1396; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4558 = raw1396Labels := by decide +kernel
    rw [ha, hj, canonical1396 B hB]
  have hc1 : mixedMoment B raw1395 (Fin.cases (1 : Fin 2) singletonSmall4558) =
      mixedMoment B node3276 node3276Labels := by
    have ha : raw1395 = raw1397 := by apply Matrix.ext; unfold raw1395 raw1397; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4558 = raw1397Labels := by decide +kernel
    rw [ha, hj, canonical1397 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4559 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4559 node4559Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1145 node1145Labels + mixedMoment B node3277 node3277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1398 singletonSmall4559
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4559) = raw1398Labels := by decide +kernel
  rw [hl, canonical1398 B hB] at h
  have hc0 : mixedMoment B raw1398 (Fin.cases (0 : Fin 2) singletonSmall4559) =
      mixedMoment B node1145 node1145Labels := by
    have ha : raw1398 = raw1399 := by apply Matrix.ext; unfold raw1398 raw1399; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4559 = raw1399Labels := by decide +kernel
    rw [ha, hj, canonical1399 B hB]
  have hc1 : mixedMoment B raw1398 (Fin.cases (1 : Fin 2) singletonSmall4559) =
      mixedMoment B node3277 node3277Labels := by
    have ha : raw1398 = raw1400 := by apply Matrix.ext; unfold raw1398 raw1400; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4559 = raw1400Labels := by decide +kernel
    rw [ha, hj, canonical1400 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4569 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4569 node4569Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1187 node1187Labels + mixedMoment B node3244 node3244Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1401 singletonSmall4569
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4569) = raw1401Labels := by decide +kernel
  rw [hl, canonical1401 B hB] at h
  have hc0 : mixedMoment B raw1401 (Fin.cases (0 : Fin 2) singletonSmall4569) =
      mixedMoment B node1187 node1187Labels := by
    have ha : raw1401 = raw1402 := by apply Matrix.ext; unfold raw1401 raw1402; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4569 = raw1402Labels := by decide +kernel
    rw [ha, hj, canonical1402 B hB]
  have hc1 : mixedMoment B raw1401 (Fin.cases (1 : Fin 2) singletonSmall4569) =
      mixedMoment B node3244 node3244Labels := by
    have ha : raw1401 = raw1403 := by apply Matrix.ext; unfold raw1401 raw1403; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4569 = raw1403Labels := by decide +kernel
    rw [ha, hj, canonical1403 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4570 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4570 node4570Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1188 node1188Labels + mixedMoment B node3245 node3245Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1404 singletonSmall4570
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4570) = raw1404Labels := by decide +kernel
  rw [hl, canonical1404 B hB] at h
  have hc0 : mixedMoment B raw1404 (Fin.cases (0 : Fin 2) singletonSmall4570) =
      mixedMoment B node1188 node1188Labels := by
    have ha : raw1404 = raw1405 := by apply Matrix.ext; unfold raw1404 raw1405; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4570 = raw1405Labels := by decide +kernel
    rw [ha, hj, canonical1405 B hB]
  have hc1 : mixedMoment B raw1404 (Fin.cases (1 : Fin 2) singletonSmall4570) =
      mixedMoment B node3245 node3245Labels := by
    have ha : raw1404 = raw1406 := by apply Matrix.ext; unfold raw1404 raw1406; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4570 = raw1406Labels := by decide +kernel
    rw [ha, hj, canonical1406 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4572 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4572 node4572Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1190 node1190Labels + mixedMoment B node1952 node1952Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1407 singletonSmall4572
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4572) = raw1407Labels := by decide +kernel
  rw [hl, canonical1407 B hB] at h
  have hc0 : mixedMoment B raw1407 (Fin.cases (0 : Fin 2) singletonSmall4572) =
      mixedMoment B node1190 node1190Labels := by
    have ha : raw1407 = raw1408 := by apply Matrix.ext; unfold raw1407 raw1408; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4572 = raw1408Labels := by decide +kernel
    rw [ha, hj, canonical1408 B hB]
  have hc1 : mixedMoment B raw1407 (Fin.cases (1 : Fin 2) singletonSmall4572) =
      mixedMoment B node1952 node1952Labels := by
    have ha : raw1407 = raw1409 := by apply Matrix.ext; unfold raw1407 raw1409; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4572 = raw1409Labels := by decide +kernel
    rw [ha, hj, canonical1409 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4575 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4575 node4575Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1193 node1193Labels + mixedMoment B node3248 node3248Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1410 singletonSmall4575
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4575) = raw1410Labels := by decide +kernel
  rw [hl, canonical1410 B hB] at h
  have hc0 : mixedMoment B raw1410 (Fin.cases (0 : Fin 2) singletonSmall4575) =
      mixedMoment B node1193 node1193Labels := by
    have ha : raw1410 = raw1411 := by apply Matrix.ext; unfold raw1410 raw1411; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4575 = raw1411Labels := by decide +kernel
    rw [ha, hj, canonical1411 B hB]
  have hc1 : mixedMoment B raw1410 (Fin.cases (1 : Fin 2) singletonSmall4575) =
      mixedMoment B node3248 node3248Labels := by
    have ha : raw1410 = raw1412 := by apply Matrix.ext; unfold raw1410 raw1412; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4575 = raw1412Labels := by decide +kernel
    rw [ha, hj, canonical1412 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4581 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4581 node4581Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1200 node1200Labels + mixedMoment B node3281 node3281Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1413 singletonSmall4581
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4581) = raw1413Labels := by decide +kernel
  rw [hl, canonical1413 B hB] at h
  have hc0 : mixedMoment B raw1413 (Fin.cases (0 : Fin 2) singletonSmall4581) =
      mixedMoment B node1200 node1200Labels := by
    have ha : raw1413 = raw1414 := by apply Matrix.ext; unfold raw1413 raw1414; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4581 = raw1414Labels := by decide +kernel
    rw [ha, hj, canonical1414 B hB]
  have hc1 : mixedMoment B raw1413 (Fin.cases (1 : Fin 2) singletonSmall4581) =
      mixedMoment B node3281 node3281Labels := by
    have ha : raw1413 = raw1415 := by apply Matrix.ext; unfold raw1413 raw1415; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4581 = raw1415Labels := by decide +kernel
    rw [ha, hj, canonical1415 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4583 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4583 node4583Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1202 node1202Labels + mixedMoment B node1942 node1942Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1416 singletonSmall4583
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4583) = raw1416Labels := by decide +kernel
  rw [hl, canonical1416 B hB] at h
  have hc0 : mixedMoment B raw1416 (Fin.cases (0 : Fin 2) singletonSmall4583) =
      mixedMoment B node1202 node1202Labels := by
    have ha : raw1416 = raw1417 := by apply Matrix.ext; unfold raw1416 raw1417; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4583 = raw1417Labels := by decide +kernel
    rw [ha, hj, canonical1417 B hB]
  have hc1 : mixedMoment B raw1416 (Fin.cases (1 : Fin 2) singletonSmall4583) =
      mixedMoment B node1942 node1942Labels := by
    have ha : raw1416 = raw1418 := by apply Matrix.ext; unfold raw1416 raw1418; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4583 = raw1418Labels := by decide +kernel
    rw [ha, hj, canonical1418 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4586 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4586 node4586Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1205 node1205Labels + mixedMoment B node3284 node3284Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1419 singletonSmall4586
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4586) = raw1419Labels := by decide +kernel
  rw [hl, canonical1419 B hB] at h
  have hc0 : mixedMoment B raw1419 (Fin.cases (0 : Fin 2) singletonSmall4586) =
      mixedMoment B node1205 node1205Labels := by
    have ha : raw1419 = raw1420 := by apply Matrix.ext; unfold raw1419 raw1420; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4586 = raw1420Labels := by decide +kernel
    rw [ha, hj, canonical1420 B hB]
  have hc1 : mixedMoment B raw1419 (Fin.cases (1 : Fin 2) singletonSmall4586) =
      mixedMoment B node3284 node3284Labels := by
    have ha : raw1419 = raw1421 := by apply Matrix.ext; unfold raw1419 raw1421; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4586 = raw1421Labels := by decide +kernel
    rw [ha, hj, canonical1421 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4601 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4601 node4601Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1235 node1235Labels + mixedMoment B node3292 node3292Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1422 singletonSmall4601
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4601) = raw1422Labels := by decide +kernel
  rw [hl, canonical1422 B hB] at h
  have hc0 : mixedMoment B raw1422 (Fin.cases (0 : Fin 2) singletonSmall4601) =
      mixedMoment B node1235 node1235Labels := by
    have ha : raw1422 = raw1423 := by apply Matrix.ext; unfold raw1422 raw1423; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4601 = raw1423Labels := by decide +kernel
    rw [ha, hj, canonical1423 B hB]
  have hc1 : mixedMoment B raw1422 (Fin.cases (1 : Fin 2) singletonSmall4601) =
      mixedMoment B node3292 node3292Labels := by
    have ha : raw1422 = raw1424 := by apply Matrix.ext; unfold raw1422 raw1424; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4601 = raw1424Labels := by decide +kernel
    rw [ha, hj, canonical1424 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4602 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4602 node4602Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1236 node1236Labels + mixedMoment B node3293 node3293Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1425 singletonSmall4602
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4602) = raw1425Labels := by decide +kernel
  rw [hl, canonical1425 B hB] at h
  have hc0 : mixedMoment B raw1425 (Fin.cases (0 : Fin 2) singletonSmall4602) =
      mixedMoment B node1236 node1236Labels := by
    have ha : raw1425 = raw1426 := by apply Matrix.ext; unfold raw1425 raw1426; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4602 = raw1426Labels := by decide +kernel
    rw [ha, hj, canonical1426 B hB]
  have hc1 : mixedMoment B raw1425 (Fin.cases (1 : Fin 2) singletonSmall4602) =
      mixedMoment B node3293 node3293Labels := by
    have ha : raw1425 = raw1427 := by apply Matrix.ext; unfold raw1425 raw1427; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4602 = raw1427Labels := by decide +kernel
    rw [ha, hj, canonical1427 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4605 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4605 node4605Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1239 node1239Labels + mixedMoment B node2226 node2226Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1428 singletonSmall4605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4605) = raw1428Labels := by decide +kernel
  rw [hl, canonical1428 B hB] at h
  have hc0 : mixedMoment B raw1428 (Fin.cases (0 : Fin 2) singletonSmall4605) =
      mixedMoment B node1239 node1239Labels := by
    have ha : raw1428 = raw1429 := by apply Matrix.ext; unfold raw1428 raw1429; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4605 = raw1429Labels := by decide +kernel
    rw [ha, hj, canonical1429 B hB]
  have hc1 : mixedMoment B raw1428 (Fin.cases (1 : Fin 2) singletonSmall4605) =
      mixedMoment B node2226 node2226Labels := by
    have ha : raw1428 = raw1430 := by apply Matrix.ext; unfold raw1428 raw1430; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4605 = raw1430Labels := by decide +kernel
    rw [ha, hj, canonical1430 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4606 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4606 node4606Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1240 node1240Labels + mixedMoment B node3299 node3299Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1431 singletonSmall4606
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4606) = raw1431Labels := by decide +kernel
  rw [hl, canonical1431 B hB] at h
  have hc0 : mixedMoment B raw1431 (Fin.cases (0 : Fin 2) singletonSmall4606) =
      mixedMoment B node1240 node1240Labels := by
    have ha : raw1431 = raw1432 := by apply Matrix.ext; unfold raw1431 raw1432; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4606 = raw1432Labels := by decide +kernel
    rw [ha, hj, canonical1432 B hB]
  have hc1 : mixedMoment B raw1431 (Fin.cases (1 : Fin 2) singletonSmall4606) =
      mixedMoment B node3299 node3299Labels := by
    have ha : raw1431 = raw1433 := by apply Matrix.ext; unfold raw1431 raw1433; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4606 = raw1433Labels := by decide +kernel
    rw [ha, hj, canonical1433 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

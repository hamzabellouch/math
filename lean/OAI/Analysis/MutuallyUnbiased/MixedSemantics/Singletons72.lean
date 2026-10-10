import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical12

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4608 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4608 node4608Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1242 node1242Labels + mixedMoment B node3300 node3300Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1434 singletonSmall4608
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4608) = raw1434Labels := by decide +kernel
  rw [hl, canonical1434 B hB] at h
  have hc0 : mixedMoment B raw1434 (Fin.cases (0 : Fin 2) singletonSmall4608) =
      mixedMoment B node1242 node1242Labels := by
    have ha : raw1434 = raw1435 := by apply Matrix.ext; unfold raw1434 raw1435; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4608 = raw1435Labels := by decide +kernel
    rw [ha, hj, canonical1435 B hB]
  have hc1 : mixedMoment B raw1434 (Fin.cases (1 : Fin 2) singletonSmall4608) =
      mixedMoment B node3300 node3300Labels := by
    have ha : raw1434 = raw1436 := by apply Matrix.ext; unfold raw1434 raw1436; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4608 = raw1436Labels := by decide +kernel
    rw [ha, hj, canonical1436 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4612 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4612 node4612Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1246 node1246Labels + mixedMoment B node3301 node3301Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1437 singletonSmall4612
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4612) = raw1437Labels := by decide +kernel
  rw [hl, canonical1437 B hB] at h
  have hc0 : mixedMoment B raw1437 (Fin.cases (0 : Fin 2) singletonSmall4612) =
      mixedMoment B node1246 node1246Labels := by
    have ha : raw1437 = raw1438 := by apply Matrix.ext; unfold raw1437 raw1438; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4612 = raw1438Labels := by decide +kernel
    rw [ha, hj, canonical1438 B hB]
  have hc1 : mixedMoment B raw1437 (Fin.cases (1 : Fin 2) singletonSmall4612) =
      mixedMoment B node3301 node3301Labels := by
    have ha : raw1437 = raw1439 := by apply Matrix.ext; unfold raw1437 raw1439; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4612 = raw1439Labels := by decide +kernel
    rw [ha, hj, canonical1439 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4618 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4618 node4618Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1293 node1293Labels + mixedMoment B node3304 node3304Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1440 singletonSmall4618
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4618) = raw1440Labels := by decide +kernel
  rw [hl, canonical1440 B hB] at h
  have hc0 : mixedMoment B raw1440 (Fin.cases (0 : Fin 2) singletonSmall4618) =
      mixedMoment B node1293 node1293Labels := by
    have ha : raw1440 = raw1441 := by apply Matrix.ext; unfold raw1440 raw1441; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4618 = raw1441Labels := by decide +kernel
    rw [ha, hj, canonical1441 B hB]
  have hc1 : mixedMoment B raw1440 (Fin.cases (1 : Fin 2) singletonSmall4618) =
      mixedMoment B node3304 node3304Labels := by
    have ha : raw1440 = raw1442 := by apply Matrix.ext; unfold raw1440 raw1442; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4618 = raw1442Labels := by decide +kernel
    rw [ha, hj, canonical1442 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4619 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4619 node4619Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1294 node1294Labels + mixedMoment B node3305 node3305Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1443 singletonSmall4619
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4619) = raw1443Labels := by decide +kernel
  rw [hl, canonical1443 B hB] at h
  have hc0 : mixedMoment B raw1443 (Fin.cases (0 : Fin 2) singletonSmall4619) =
      mixedMoment B node1294 node1294Labels := by
    have ha : raw1443 = raw1444 := by apply Matrix.ext; unfold raw1443 raw1444; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4619 = raw1444Labels := by decide +kernel
    rw [ha, hj, canonical1444 B hB]
  have hc1 : mixedMoment B raw1443 (Fin.cases (1 : Fin 2) singletonSmall4619) =
      mixedMoment B node3305 node3305Labels := by
    have ha : raw1443 = raw1445 := by apply Matrix.ext; unfold raw1443 raw1445; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4619 = raw1445Labels := by decide +kernel
    rw [ha, hj, canonical1445 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4621 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4621 node4621Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1297 node1297Labels + mixedMoment B node2289 node2289Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1446 singletonSmall4621
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4621) = raw1446Labels := by decide +kernel
  rw [hl, canonical1446 B hB] at h
  have hc0 : mixedMoment B raw1446 (Fin.cases (0 : Fin 2) singletonSmall4621) =
      mixedMoment B node1297 node1297Labels := by
    have ha : raw1446 = raw1447 := by apply Matrix.ext; unfold raw1446 raw1447; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4621 = raw1447Labels := by decide +kernel
    rw [ha, hj, canonical1447 B hB]
  have hc1 : mixedMoment B raw1446 (Fin.cases (1 : Fin 2) singletonSmall4621) =
      mixedMoment B node2289 node2289Labels := by
    have ha : raw1446 = raw1448 := by apply Matrix.ext; unfold raw1446 raw1448; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4621 = raw1448Labels := by decide +kernel
    rw [ha, hj, canonical1448 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4622 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4622 node4622Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1299 node1299Labels + mixedMoment B node3307 node3307Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1449 singletonSmall4622
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4622) = raw1449Labels := by decide +kernel
  rw [hl, canonical1449 B hB] at h
  have hc0 : mixedMoment B raw1449 (Fin.cases (0 : Fin 2) singletonSmall4622) =
      mixedMoment B node1299 node1299Labels := by
    have ha : raw1449 = raw1450 := by apply Matrix.ext; unfold raw1449 raw1450; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4622 = raw1450Labels := by decide +kernel
    rw [ha, hj, canonical1450 B hB]
  have hc1 : mixedMoment B raw1449 (Fin.cases (1 : Fin 2) singletonSmall4622) =
      mixedMoment B node3307 node3307Labels := by
    have ha : raw1449 = raw1451 := by apply Matrix.ext; unfold raw1449 raw1451; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4622 = raw1451Labels := by decide +kernel
    rw [ha, hj, canonical1451 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4623 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4623 node4623Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1300 node1300Labels + mixedMoment B node3308 node3308Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1452 singletonSmall4623
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4623) = raw1452Labels := by decide +kernel
  rw [hl, canonical1452 B hB] at h
  have hc0 : mixedMoment B raw1452 (Fin.cases (0 : Fin 2) singletonSmall4623) =
      mixedMoment B node1300 node1300Labels := by
    have ha : raw1452 = raw1453 := by apply Matrix.ext; unfold raw1452 raw1453; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4623 = raw1453Labels := by decide +kernel
    rw [ha, hj, canonical1453 B hB]
  have hc1 : mixedMoment B raw1452 (Fin.cases (1 : Fin 2) singletonSmall4623) =
      mixedMoment B node3308 node3308Labels := by
    have ha : raw1452 = raw1454 := by apply Matrix.ext; unfold raw1452 raw1454; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4623 = raw1454Labels := by decide +kernel
    rw [ha, hj, canonical1454 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4624 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4624 node4624Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1301 node1301Labels + mixedMoment B node3309 node3309Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1455 singletonSmall4624
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4624) = raw1455Labels := by decide +kernel
  rw [hl, canonical1455 B hB] at h
  have hc0 : mixedMoment B raw1455 (Fin.cases (0 : Fin 2) singletonSmall4624) =
      mixedMoment B node1301 node1301Labels := by
    have ha : raw1455 = raw1456 := by apply Matrix.ext; unfold raw1455 raw1456; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4624 = raw1456Labels := by decide +kernel
    rw [ha, hj, canonical1456 B hB]
  have hc1 : mixedMoment B raw1455 (Fin.cases (1 : Fin 2) singletonSmall4624) =
      mixedMoment B node3309 node3309Labels := by
    have ha : raw1455 = raw1457 := by apply Matrix.ext; unfold raw1455 raw1457; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4624 = raw1457Labels := by decide +kernel
    rw [ha, hj, canonical1457 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4625 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4625 node4625Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1304 node1304Labels + mixedMoment B node3310 node3310Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1458 singletonSmall4625
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4625) = raw1458Labels := by decide +kernel
  rw [hl, canonical1458 B hB] at h
  have hc0 : mixedMoment B raw1458 (Fin.cases (0 : Fin 2) singletonSmall4625) =
      mixedMoment B node1304 node1304Labels := by
    have ha : raw1458 = raw1459 := by apply Matrix.ext; unfold raw1458 raw1459; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4625 = raw1459Labels := by decide +kernel
    rw [ha, hj, canonical1459 B hB]
  have hc1 : mixedMoment B raw1458 (Fin.cases (1 : Fin 2) singletonSmall4625) =
      mixedMoment B node3310 node3310Labels := by
    have ha : raw1458 = raw1460 := by apply Matrix.ext; unfold raw1458 raw1460; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4625 = raw1460Labels := by decide +kernel
    rw [ha, hj, canonical1460 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4627 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4627 node4627Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1311 node1311Labels + mixedMoment B node3311 node3311Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1461 singletonSmall4627
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4627) = raw1461Labels := by decide +kernel
  rw [hl, canonical1461 B hB] at h
  have hc0 : mixedMoment B raw1461 (Fin.cases (0 : Fin 2) singletonSmall4627) =
      mixedMoment B node1311 node1311Labels := by
    have ha : raw1461 = raw1462 := by apply Matrix.ext; unfold raw1461 raw1462; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4627 = raw1462Labels := by decide +kernel
    rw [ha, hj, canonical1462 B hB]
  have hc1 : mixedMoment B raw1461 (Fin.cases (1 : Fin 2) singletonSmall4627) =
      mixedMoment B node3311 node3311Labels := by
    have ha : raw1461 = raw1463 := by apply Matrix.ext; unfold raw1461 raw1463; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4627 = raw1463Labels := by decide +kernel
    rw [ha, hj, canonical1463 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4628 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4628 node4628Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1312 node1312Labels + mixedMoment B node3312 node3312Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1464 singletonSmall4628
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4628) = raw1464Labels := by decide +kernel
  rw [hl, canonical1464 B hB] at h
  have hc0 : mixedMoment B raw1464 (Fin.cases (0 : Fin 2) singletonSmall4628) =
      mixedMoment B node1312 node1312Labels := by
    have ha : raw1464 = raw1465 := by apply Matrix.ext; unfold raw1464 raw1465; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4628 = raw1465Labels := by decide +kernel
    rw [ha, hj, canonical1465 B hB]
  have hc1 : mixedMoment B raw1464 (Fin.cases (1 : Fin 2) singletonSmall4628) =
      mixedMoment B node3312 node3312Labels := by
    have ha : raw1464 = raw1466 := by apply Matrix.ext; unfold raw1464 raw1466; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4628 = raw1466Labels := by decide +kernel
    rw [ha, hj, canonical1466 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4629 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4629 node4629Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1313 node1313Labels + mixedMoment B node3313 node3313Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1467 singletonSmall4629
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4629) = raw1467Labels := by decide +kernel
  rw [hl, canonical1467 B hB] at h
  have hc0 : mixedMoment B raw1467 (Fin.cases (0 : Fin 2) singletonSmall4629) =
      mixedMoment B node1313 node1313Labels := by
    have ha : raw1467 = raw1468 := by apply Matrix.ext; unfold raw1467 raw1468; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4629 = raw1468Labels := by decide +kernel
    rw [ha, hj, canonical1468 B hB]
  have hc1 : mixedMoment B raw1467 (Fin.cases (1 : Fin 2) singletonSmall4629) =
      mixedMoment B node3313 node3313Labels := by
    have ha : raw1467 = raw1469 := by apply Matrix.ext; unfold raw1467 raw1469; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4629 = raw1469Labels := by decide +kernel
    rw [ha, hj, canonical1469 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4630 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4630 node4630Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1759 node1759Labels + mixedMoment B node1833 node1833Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1470 singletonSmall4630
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4630) = raw1470Labels := by decide +kernel
  rw [hl, canonical1470 B hB] at h
  have hc0 : mixedMoment B raw1470 (Fin.cases (0 : Fin 2) singletonSmall4630) =
      mixedMoment B node1759 node1759Labels := by
    have ha : raw1470 = raw1471 := by apply Matrix.ext; unfold raw1470 raw1471; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4630 = raw1471Labels := by decide +kernel
    rw [ha, hj, canonical1471 B hB]
  have hc1 : mixedMoment B raw1470 (Fin.cases (1 : Fin 2) singletonSmall4630) =
      mixedMoment B node1833 node1833Labels := by
    have ha : raw1470 = raw1472 := by apply Matrix.ext; unfold raw1470 raw1472; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4630 = raw1472Labels := by decide +kernel
    rw [ha, hj, canonical1472 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4631 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4631 node4631Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1760 node1760Labels + mixedMoment B node1836 node1836Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1473 singletonSmall4631
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4631) = raw1473Labels := by decide +kernel
  rw [hl, canonical1473 B hB] at h
  have hc0 : mixedMoment B raw1473 (Fin.cases (0 : Fin 2) singletonSmall4631) =
      mixedMoment B node1760 node1760Labels := by
    have ha : raw1473 = raw1474 := by apply Matrix.ext; unfold raw1473 raw1474; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4631 = raw1474Labels := by decide +kernel
    rw [ha, hj, canonical1474 B hB]
  have hc1 : mixedMoment B raw1473 (Fin.cases (1 : Fin 2) singletonSmall4631) =
      mixedMoment B node1836 node1836Labels := by
    have ha : raw1473 = raw1475 := by apply Matrix.ext; unfold raw1473 raw1475; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4631 = raw1475Labels := by decide +kernel
    rw [ha, hj, canonical1475 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4632 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4632 node4632Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1761 node1761Labels + mixedMoment B node1837 node1837Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1476 singletonSmall4632
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4632) = raw1476Labels := by decide +kernel
  rw [hl, canonical1476 B hB] at h
  have hc0 : mixedMoment B raw1476 (Fin.cases (0 : Fin 2) singletonSmall4632) =
      mixedMoment B node1761 node1761Labels := by
    have ha : raw1476 = raw1477 := by apply Matrix.ext; unfold raw1476 raw1477; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4632 = raw1477Labels := by decide +kernel
    rw [ha, hj, canonical1477 B hB]
  have hc1 : mixedMoment B raw1476 (Fin.cases (1 : Fin 2) singletonSmall4632) =
      mixedMoment B node1837 node1837Labels := by
    have ha : raw1476 = raw1478 := by apply Matrix.ext; unfold raw1476 raw1478; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4632 = raw1478Labels := by decide +kernel
    rw [ha, hj, canonical1478 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4633 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4633 node4633Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1762 node1762Labels + mixedMoment B node1847 node1847Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1479 singletonSmall4633
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4633) = raw1479Labels := by decide +kernel
  rw [hl, canonical1479 B hB] at h
  have hc0 : mixedMoment B raw1479 (Fin.cases (0 : Fin 2) singletonSmall4633) =
      mixedMoment B node1762 node1762Labels := by
    have ha : raw1479 = raw1480 := by apply Matrix.ext; unfold raw1479 raw1480; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4633 = raw1480Labels := by decide +kernel
    rw [ha, hj, canonical1480 B hB]
  have hc1 : mixedMoment B raw1479 (Fin.cases (1 : Fin 2) singletonSmall4633) =
      mixedMoment B node1847 node1847Labels := by
    have ha : raw1479 = raw1481 := by apply Matrix.ext; unfold raw1479 raw1481; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4633 = raw1481Labels := by decide +kernel
    rw [ha, hj, canonical1481 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4634 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4634 node4634Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1763 node1763Labels + mixedMoment B node1842 node1842Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1482 singletonSmall4634
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4634) = raw1482Labels := by decide +kernel
  rw [hl, canonical1482 B hB] at h
  have hc0 : mixedMoment B raw1482 (Fin.cases (0 : Fin 2) singletonSmall4634) =
      mixedMoment B node1763 node1763Labels := by
    have ha : raw1482 = raw1483 := by apply Matrix.ext; unfold raw1482 raw1483; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4634 = raw1483Labels := by decide +kernel
    rw [ha, hj, canonical1483 B hB]
  have hc1 : mixedMoment B raw1482 (Fin.cases (1 : Fin 2) singletonSmall4634) =
      mixedMoment B node1842 node1842Labels := by
    have ha : raw1482 = raw1484 := by apply Matrix.ext; unfold raw1482 raw1484; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4634 = raw1484Labels := by decide +kernel
    rw [ha, hj, canonical1484 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4635 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4635 node4635Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1764 node1764Labels + mixedMoment B node1848 node1848Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1485 singletonSmall4635
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4635) = raw1485Labels := by decide +kernel
  rw [hl, canonical1485 B hB] at h
  have hc0 : mixedMoment B raw1485 (Fin.cases (0 : Fin 2) singletonSmall4635) =
      mixedMoment B node1764 node1764Labels := by
    have ha : raw1485 = raw1486 := by apply Matrix.ext; unfold raw1485 raw1486; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4635 = raw1486Labels := by decide +kernel
    rw [ha, hj, canonical1486 B hB]
  have hc1 : mixedMoment B raw1485 (Fin.cases (1 : Fin 2) singletonSmall4635) =
      mixedMoment B node1848 node1848Labels := by
    have ha : raw1485 = raw1487 := by apply Matrix.ext; unfold raw1485 raw1487; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4635 = raw1487Labels := by decide +kernel
    rw [ha, hj, canonical1487 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4636 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4636 node4636Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1765 node1765Labels + mixedMoment B node1843 node1843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1488 singletonSmall4636
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4636) = raw1488Labels := by decide +kernel
  rw [hl, canonical1488 B hB] at h
  have hc0 : mixedMoment B raw1488 (Fin.cases (0 : Fin 2) singletonSmall4636) =
      mixedMoment B node1765 node1765Labels := by
    have ha : raw1488 = raw1489 := by apply Matrix.ext; unfold raw1488 raw1489; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4636 = raw1489Labels := by decide +kernel
    rw [ha, hj, canonical1489 B hB]
  have hc1 : mixedMoment B raw1488 (Fin.cases (1 : Fin 2) singletonSmall4636) =
      mixedMoment B node1843 node1843Labels := by
    have ha : raw1488 = raw1490 := by apply Matrix.ext; unfold raw1488 raw1490; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4636 = raw1490Labels := by decide +kernel
    rw [ha, hj, canonical1490 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4637 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4637 node4637Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1766 node1766Labels + mixedMoment B node1850 node1850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1491 singletonSmall4637
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4637) = raw1491Labels := by decide +kernel
  rw [hl, canonical1491 B hB] at h
  have hc0 : mixedMoment B raw1491 (Fin.cases (0 : Fin 2) singletonSmall4637) =
      mixedMoment B node1766 node1766Labels := by
    have ha : raw1491 = raw1492 := by apply Matrix.ext; unfold raw1491 raw1492; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4637 = raw1492Labels := by decide +kernel
    rw [ha, hj, canonical1492 B hB]
  have hc1 : mixedMoment B raw1491 (Fin.cases (1 : Fin 2) singletonSmall4637) =
      mixedMoment B node1850 node1850Labels := by
    have ha : raw1491 = raw1493 := by apply Matrix.ext; unfold raw1491 raw1493; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4637 = raw1493Labels := by decide +kernel
    rw [ha, hj, canonical1493 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4638 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4638 node4638Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1767 node1767Labels + mixedMoment B node1851 node1851Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1494 singletonSmall4638
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4638) = raw1494Labels := by decide +kernel
  rw [hl, canonical1494 B hB] at h
  have hc0 : mixedMoment B raw1494 (Fin.cases (0 : Fin 2) singletonSmall4638) =
      mixedMoment B node1767 node1767Labels := by
    have ha : raw1494 = raw1495 := by apply Matrix.ext; unfold raw1494 raw1495; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4638 = raw1495Labels := by decide +kernel
    rw [ha, hj, canonical1495 B hB]
  have hc1 : mixedMoment B raw1494 (Fin.cases (1 : Fin 2) singletonSmall4638) =
      mixedMoment B node1851 node1851Labels := by
    have ha : raw1494 = raw1496 := by apply Matrix.ext; unfold raw1494 raw1496; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4638 = raw1496Labels := by decide +kernel
    rw [ha, hj, canonical1496 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4639 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4639 node4639Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1768 node1768Labels + mixedMoment B node1834 node1834Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1497 singletonSmall4639
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4639) = raw1497Labels := by decide +kernel
  rw [hl, canonical1497 B hB] at h
  have hc0 : mixedMoment B raw1497 (Fin.cases (0 : Fin 2) singletonSmall4639) =
      mixedMoment B node1768 node1768Labels := by
    have ha : raw1497 = raw1498 := by apply Matrix.ext; unfold raw1497 raw1498; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4639 = raw1498Labels := by decide +kernel
    rw [ha, hj, canonical1498 B hB]
  have hc1 : mixedMoment B raw1497 (Fin.cases (1 : Fin 2) singletonSmall4639) =
      mixedMoment B node1834 node1834Labels := by
    have ha : raw1497 = raw1499 := by apply Matrix.ext; unfold raw1497 raw1499; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4639 = raw1499Labels := by decide +kernel
    rw [ha, hj, canonical1499 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4640 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4640 node4640Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1769 node1769Labels + mixedMoment B node1835 node1835Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1500 singletonSmall4640
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4640) = raw1500Labels := by decide +kernel
  rw [hl, canonical1500 B hB] at h
  have hc0 : mixedMoment B raw1500 (Fin.cases (0 : Fin 2) singletonSmall4640) =
      mixedMoment B node1769 node1769Labels := by
    have ha : raw1500 = raw1501 := by apply Matrix.ext; unfold raw1500 raw1501; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4640 = raw1501Labels := by decide +kernel
    rw [ha, hj, canonical1501 B hB]
  have hc1 : mixedMoment B raw1500 (Fin.cases (1 : Fin 2) singletonSmall4640) =
      mixedMoment B node1835 node1835Labels := by
    have ha : raw1500 = raw1502 := by apply Matrix.ext; unfold raw1500 raw1502; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4640 = raw1502Labels := by decide +kernel
    rw [ha, hj, canonical1502 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4642 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4642 node4642Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1771 node1771Labels + mixedMoment B node1838 node1838Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1503 singletonSmall4642
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4642) = raw1503Labels := by decide +kernel
  rw [hl, canonical1503 B hB] at h
  have hc0 : mixedMoment B raw1503 (Fin.cases (0 : Fin 2) singletonSmall4642) =
      mixedMoment B node1771 node1771Labels := by
    have ha : raw1503 = raw1504 := by apply Matrix.ext; unfold raw1503 raw1504; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4642 = raw1504Labels := by decide +kernel
    rw [ha, hj, canonical1504 B hB]
  have hc1 : mixedMoment B raw1503 (Fin.cases (1 : Fin 2) singletonSmall4642) =
      mixedMoment B node1838 node1838Labels := by
    have ha : raw1503 = raw1505 := by apply Matrix.ext; unfold raw1503 raw1505; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4642 = raw1505Labels := by decide +kernel
    rw [ha, hj, canonical1505 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4644 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4644 node4644Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1773 node1773Labels + mixedMoment B node1841 node1841Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1506 singletonSmall4644
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4644) = raw1506Labels := by decide +kernel
  rw [hl, canonical1506 B hB] at h
  have hc0 : mixedMoment B raw1506 (Fin.cases (0 : Fin 2) singletonSmall4644) =
      mixedMoment B node1773 node1773Labels := by
    have ha : raw1506 = raw1507 := by apply Matrix.ext; unfold raw1506 raw1507; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4644 = raw1507Labels := by decide +kernel
    rw [ha, hj, canonical1507 B hB]
  have hc1 : mixedMoment B raw1506 (Fin.cases (1 : Fin 2) singletonSmall4644) =
      mixedMoment B node1841 node1841Labels := by
    have ha : raw1506 = raw1508 := by apply Matrix.ext; unfold raw1506 raw1508; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4644 = raw1508Labels := by decide +kernel
    rw [ha, hj, canonical1508 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4645 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4645 node4645Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1774 node1774Labels + mixedMoment B node1840 node1840Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1509 singletonSmall4645
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4645) = raw1509Labels := by decide +kernel
  rw [hl, canonical1509 B hB] at h
  have hc0 : mixedMoment B raw1509 (Fin.cases (0 : Fin 2) singletonSmall4645) =
      mixedMoment B node1774 node1774Labels := by
    have ha : raw1509 = raw1510 := by apply Matrix.ext; unfold raw1509 raw1510; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4645 = raw1510Labels := by decide +kernel
    rw [ha, hj, canonical1510 B hB]
  have hc1 : mixedMoment B raw1509 (Fin.cases (1 : Fin 2) singletonSmall4645) =
      mixedMoment B node1840 node1840Labels := by
    have ha : raw1509 = raw1511 := by apply Matrix.ext; unfold raw1509 raw1511; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4645 = raw1511Labels := by decide +kernel
    rw [ha, hj, canonical1511 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4648 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4648 node4648Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1776 node1776Labels + mixedMoment B node1844 node1844Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1512 singletonSmall4648
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4648) = raw1512Labels := by decide +kernel
  rw [hl, canonical1512 B hB] at h
  have hc0 : mixedMoment B raw1512 (Fin.cases (0 : Fin 2) singletonSmall4648) =
      mixedMoment B node1776 node1776Labels := by
    have ha : raw1512 = raw1513 := by apply Matrix.ext; unfold raw1512 raw1513; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4648 = raw1513Labels := by decide +kernel
    rw [ha, hj, canonical1513 B hB]
  have hc1 : mixedMoment B raw1512 (Fin.cases (1 : Fin 2) singletonSmall4648) =
      mixedMoment B node1844 node1844Labels := by
    have ha : raw1512 = raw1514 := by apply Matrix.ext; unfold raw1512 raw1514; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4648 = raw1514Labels := by decide +kernel
    rw [ha, hj, canonical1514 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4650 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4650 node4650Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1778 node1778Labels + mixedMoment B node1854 node1854Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1515 singletonSmall4650
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4650) = raw1515Labels := by decide +kernel
  rw [hl, canonical1515 B hB] at h
  have hc0 : mixedMoment B raw1515 (Fin.cases (0 : Fin 2) singletonSmall4650) =
      mixedMoment B node1778 node1778Labels := by
    have ha : raw1515 = raw1516 := by apply Matrix.ext; unfold raw1515 raw1516; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4650 = raw1516Labels := by decide +kernel
    rw [ha, hj, canonical1516 B hB]
  have hc1 : mixedMoment B raw1515 (Fin.cases (1 : Fin 2) singletonSmall4650) =
      mixedMoment B node1854 node1854Labels := by
    have ha : raw1515 = raw1517 := by apply Matrix.ext; unfold raw1515 raw1517; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4650 = raw1517Labels := by decide +kernel
    rw [ha, hj, canonical1517 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4651 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4651 node4651Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1779 node1779Labels + mixedMoment B node1845 node1845Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1518 singletonSmall4651
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4651) = raw1518Labels := by decide +kernel
  rw [hl, canonical1518 B hB] at h
  have hc0 : mixedMoment B raw1518 (Fin.cases (0 : Fin 2) singletonSmall4651) =
      mixedMoment B node1779 node1779Labels := by
    have ha : raw1518 = raw1519 := by apply Matrix.ext; unfold raw1518 raw1519; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4651 = raw1519Labels := by decide +kernel
    rw [ha, hj, canonical1519 B hB]
  have hc1 : mixedMoment B raw1518 (Fin.cases (1 : Fin 2) singletonSmall4651) =
      mixedMoment B node1845 node1845Labels := by
    have ha : raw1518 = raw1520 := by apply Matrix.ext; unfold raw1518 raw1520; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4651 = raw1520Labels := by decide +kernel
    rw [ha, hj, canonical1520 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4653 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4653 node4653Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1781 node1781Labels + mixedMoment B node1846 node1846Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1521 singletonSmall4653
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4653) = raw1521Labels := by decide +kernel
  rw [hl, canonical1521 B hB] at h
  have hc0 : mixedMoment B raw1521 (Fin.cases (0 : Fin 2) singletonSmall4653) =
      mixedMoment B node1781 node1781Labels := by
    have ha : raw1521 = raw1522 := by apply Matrix.ext; unfold raw1521 raw1522; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4653 = raw1522Labels := by decide +kernel
    rw [ha, hj, canonical1522 B hB]
  have hc1 : mixedMoment B raw1521 (Fin.cases (1 : Fin 2) singletonSmall4653) =
      mixedMoment B node1846 node1846Labels := by
    have ha : raw1521 = raw1523 := by apply Matrix.ext; unfold raw1521 raw1523; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4653 = raw1523Labels := by decide +kernel
    rw [ha, hj, canonical1523 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4654 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4654 node4654Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1782 node1782Labels + mixedMoment B node1855 node1855Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1524 singletonSmall4654
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4654) = raw1524Labels := by decide +kernel
  rw [hl, canonical1524 B hB] at h
  have hc0 : mixedMoment B raw1524 (Fin.cases (0 : Fin 2) singletonSmall4654) =
      mixedMoment B node1782 node1782Labels := by
    have ha : raw1524 = raw1525 := by apply Matrix.ext; unfold raw1524 raw1525; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4654 = raw1525Labels := by decide +kernel
    rw [ha, hj, canonical1525 B hB]
  have hc1 : mixedMoment B raw1524 (Fin.cases (1 : Fin 2) singletonSmall4654) =
      mixedMoment B node1855 node1855Labels := by
    have ha : raw1524 = raw1526 := by apply Matrix.ext; unfold raw1524 raw1526; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4654 = raw1526Labels := by decide +kernel
    rw [ha, hj, canonical1526 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4657 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4657 node4657Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1783 node1783Labels + mixedMoment B node1857 node1857Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1527 singletonSmall4657
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4657) = raw1527Labels := by decide +kernel
  rw [hl, canonical1527 B hB] at h
  have hc0 : mixedMoment B raw1527 (Fin.cases (0 : Fin 2) singletonSmall4657) =
      mixedMoment B node1783 node1783Labels := by
    have ha : raw1527 = raw1528 := by apply Matrix.ext; unfold raw1527 raw1528; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4657 = raw1528Labels := by decide +kernel
    rw [ha, hj, canonical1528 B hB]
  have hc1 : mixedMoment B raw1527 (Fin.cases (1 : Fin 2) singletonSmall4657) =
      mixedMoment B node1857 node1857Labels := by
    have ha : raw1527 = raw1529 := by apply Matrix.ext; unfold raw1527 raw1529; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4657 = raw1529Labels := by decide +kernel
    rw [ha, hj, canonical1529 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4658 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4658 node4658Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1784 node1784Labels + mixedMoment B node1884 node1884Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1530 singletonSmall4658
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4658) = raw1530Labels := by decide +kernel
  rw [hl, canonical1530 B hB] at h
  have hc0 : mixedMoment B raw1530 (Fin.cases (0 : Fin 2) singletonSmall4658) =
      mixedMoment B node1784 node1784Labels := by
    have ha : raw1530 = raw1531 := by apply Matrix.ext; unfold raw1530 raw1531; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4658 = raw1531Labels := by decide +kernel
    rw [ha, hj, canonical1531 B hB]
  have hc1 : mixedMoment B raw1530 (Fin.cases (1 : Fin 2) singletonSmall4658) =
      mixedMoment B node1884 node1884Labels := by
    have ha : raw1530 = raw1532 := by apply Matrix.ext; unfold raw1530 raw1532; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4658 = raw1532Labels := by decide +kernel
    rw [ha, hj, canonical1532 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4659 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4659 node4659Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1785 node1785Labels + mixedMoment B node1981 node1981Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1533 singletonSmall4659
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4659) = raw1533Labels := by decide +kernel
  rw [hl, canonical1533 B hB] at h
  have hc0 : mixedMoment B raw1533 (Fin.cases (0 : Fin 2) singletonSmall4659) =
      mixedMoment B node1785 node1785Labels := by
    have ha : raw1533 = raw1534 := by apply Matrix.ext; unfold raw1533 raw1534; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4659 = raw1534Labels := by decide +kernel
    rw [ha, hj, canonical1534 B hB]
  have hc1 : mixedMoment B raw1533 (Fin.cases (1 : Fin 2) singletonSmall4659) =
      mixedMoment B node1981 node1981Labels := by
    have ha : raw1533 = raw1535 := by apply Matrix.ext; unfold raw1533 raw1535; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4659 = raw1535Labels := by decide +kernel
    rw [ha, hj, canonical1535 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4660 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4660 node4660Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1786 node1786Labels + mixedMoment B node1982 node1982Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1536 singletonSmall4660
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4660) = raw1536Labels := by decide +kernel
  rw [hl, canonical1536 B hB] at h
  have hc0 : mixedMoment B raw1536 (Fin.cases (0 : Fin 2) singletonSmall4660) =
      mixedMoment B node1786 node1786Labels := by
    have ha : raw1536 = raw1537 := by apply Matrix.ext; unfold raw1536 raw1537; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4660 = raw1537Labels := by decide +kernel
    rw [ha, hj, canonical1537 B hB]
  have hc1 : mixedMoment B raw1536 (Fin.cases (1 : Fin 2) singletonSmall4660) =
      mixedMoment B node1982 node1982Labels := by
    have ha : raw1536 = raw1538 := by apply Matrix.ext; unfold raw1536 raw1538; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4660 = raw1538Labels := by decide +kernel
    rw [ha, hj, canonical1538 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4661 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4661 node4661Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1787 node1787Labels + mixedMoment B node1983 node1983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1539 singletonSmall4661
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4661) = raw1539Labels := by decide +kernel
  rw [hl, canonical1539 B hB] at h
  have hc0 : mixedMoment B raw1539 (Fin.cases (0 : Fin 2) singletonSmall4661) =
      mixedMoment B node1787 node1787Labels := by
    have ha : raw1539 = raw1540 := by apply Matrix.ext; unfold raw1539 raw1540; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4661 = raw1540Labels := by decide +kernel
    rw [ha, hj, canonical1540 B hB]
  have hc1 : mixedMoment B raw1539 (Fin.cases (1 : Fin 2) singletonSmall4661) =
      mixedMoment B node1983 node1983Labels := by
    have ha : raw1539 = raw1541 := by apply Matrix.ext; unfold raw1539 raw1541; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4661 = raw1541Labels := by decide +kernel
    rw [ha, hj, canonical1541 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4662 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4662 node4662Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1788 node1788Labels + mixedMoment B node1984 node1984Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1542 singletonSmall4662
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4662) = raw1542Labels := by decide +kernel
  rw [hl, canonical1542 B hB] at h
  have hc0 : mixedMoment B raw1542 (Fin.cases (0 : Fin 2) singletonSmall4662) =
      mixedMoment B node1788 node1788Labels := by
    have ha : raw1542 = raw1543 := by apply Matrix.ext; unfold raw1542 raw1543; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4662 = raw1543Labels := by decide +kernel
    rw [ha, hj, canonical1543 B hB]
  have hc1 : mixedMoment B raw1542 (Fin.cases (1 : Fin 2) singletonSmall4662) =
      mixedMoment B node1984 node1984Labels := by
    have ha : raw1542 = raw1544 := by apply Matrix.ext; unfold raw1542 raw1544; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4662 = raw1544Labels := by decide +kernel
    rw [ha, hj, canonical1544 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

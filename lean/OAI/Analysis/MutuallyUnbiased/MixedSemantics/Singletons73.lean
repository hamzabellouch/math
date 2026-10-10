import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical12

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4672 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4672 node4672Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1798 node1798Labels + mixedMoment B node2067 node2067Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1545 singletonSmall4672
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4672) = raw1545Labels := by decide +kernel
  rw [hl, canonical1545 B hB] at h
  have hc0 : mixedMoment B raw1545 (Fin.cases (0 : Fin 2) singletonSmall4672) =
      mixedMoment B node1798 node1798Labels := by
    have ha : raw1545 = raw1546 := by apply Matrix.ext; unfold raw1545 raw1546; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4672 = raw1546Labels := by decide +kernel
    rw [ha, hj, canonical1546 B hB]
  have hc1 : mixedMoment B raw1545 (Fin.cases (1 : Fin 2) singletonSmall4672) =
      mixedMoment B node2067 node2067Labels := by
    have ha : raw1545 = raw1547 := by apply Matrix.ext; unfold raw1545 raw1547; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4672 = raw1547Labels := by decide +kernel
    rw [ha, hj, canonical1547 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4673 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4673 node4673Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1799 node1799Labels + mixedMoment B node1920 node1920Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1548 singletonSmall4673
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4673) = raw1548Labels := by decide +kernel
  rw [hl, canonical1548 B hB] at h
  have hc0 : mixedMoment B raw1548 (Fin.cases (0 : Fin 2) singletonSmall4673) =
      mixedMoment B node1799 node1799Labels := by
    have ha : raw1548 = raw1549 := by apply Matrix.ext; unfold raw1548 raw1549; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4673 = raw1549Labels := by decide +kernel
    rw [ha, hj, canonical1549 B hB]
  have hc1 : mixedMoment B raw1548 (Fin.cases (1 : Fin 2) singletonSmall4673) =
      mixedMoment B node1920 node1920Labels := by
    have ha : raw1548 = raw1550 := by apply Matrix.ext; unfold raw1548 raw1550; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4673 = raw1550Labels := by decide +kernel
    rw [ha, hj, canonical1550 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4674 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4674 node4674Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1800 node1800Labels + mixedMoment B node2068 node2068Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1551 singletonSmall4674
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4674) = raw1551Labels := by decide +kernel
  rw [hl, canonical1551 B hB] at h
  have hc0 : mixedMoment B raw1551 (Fin.cases (0 : Fin 2) singletonSmall4674) =
      mixedMoment B node1800 node1800Labels := by
    have ha : raw1551 = raw1552 := by apply Matrix.ext; unfold raw1551 raw1552; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4674 = raw1552Labels := by decide +kernel
    rw [ha, hj, canonical1552 B hB]
  have hc1 : mixedMoment B raw1551 (Fin.cases (1 : Fin 2) singletonSmall4674) =
      mixedMoment B node2068 node2068Labels := by
    have ha : raw1551 = raw1553 := by apply Matrix.ext; unfold raw1551 raw1553; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4674 = raw1553Labels := by decide +kernel
    rw [ha, hj, canonical1553 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4676 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4676 node4676Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1802 node1802Labels + mixedMoment B node2141 node2141Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1554 singletonSmall4676
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4676) = raw1554Labels := by decide +kernel
  rw [hl, canonical1554 B hB] at h
  have hc0 : mixedMoment B raw1554 (Fin.cases (0 : Fin 2) singletonSmall4676) =
      mixedMoment B node1802 node1802Labels := by
    have ha : raw1554 = raw1555 := by apply Matrix.ext; unfold raw1554 raw1555; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4676 = raw1555Labels := by decide +kernel
    rw [ha, hj, canonical1555 B hB]
  have hc1 : mixedMoment B raw1554 (Fin.cases (1 : Fin 2) singletonSmall4676) =
      mixedMoment B node2141 node2141Labels := by
    have ha : raw1554 = raw1556 := by apply Matrix.ext; unfold raw1554 raw1556; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4676 = raw1556Labels := by decide +kernel
    rw [ha, hj, canonical1556 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4678 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4678 node4678Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1804 node1804Labels + mixedMoment B node2143 node2143Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1557 singletonSmall4678
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4678) = raw1557Labels := by decide +kernel
  rw [hl, canonical1557 B hB] at h
  have hc0 : mixedMoment B raw1557 (Fin.cases (0 : Fin 2) singletonSmall4678) =
      mixedMoment B node1804 node1804Labels := by
    have ha : raw1557 = raw1558 := by apply Matrix.ext; unfold raw1557 raw1558; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4678 = raw1558Labels := by decide +kernel
    rw [ha, hj, canonical1558 B hB]
  have hc1 : mixedMoment B raw1557 (Fin.cases (1 : Fin 2) singletonSmall4678) =
      mixedMoment B node2143 node2143Labels := by
    have ha : raw1557 = raw1559 := by apply Matrix.ext; unfold raw1557 raw1559; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4678 = raw1559Labels := by decide +kernel
    rw [ha, hj, canonical1559 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4679 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4679 node4679Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1805 node1805Labels + mixedMoment B node2150 node2150Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1560 singletonSmall4679
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4679) = raw1560Labels := by decide +kernel
  rw [hl, canonical1560 B hB] at h
  have hc0 : mixedMoment B raw1560 (Fin.cases (0 : Fin 2) singletonSmall4679) =
      mixedMoment B node1805 node1805Labels := by
    have ha : raw1560 = raw1561 := by apply Matrix.ext; unfold raw1560 raw1561; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4679 = raw1561Labels := by decide +kernel
    rw [ha, hj, canonical1561 B hB]
  have hc1 : mixedMoment B raw1560 (Fin.cases (1 : Fin 2) singletonSmall4679) =
      mixedMoment B node2150 node2150Labels := by
    have ha : raw1560 = raw1562 := by apply Matrix.ext; unfold raw1560 raw1562; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4679 = raw1562Labels := by decide +kernel
    rw [ha, hj, canonical1562 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4681 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4681 node4681Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1807 node1807Labels + mixedMoment B node2151 node2151Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1563 singletonSmall4681
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4681) = raw1563Labels := by decide +kernel
  rw [hl, canonical1563 B hB] at h
  have hc0 : mixedMoment B raw1563 (Fin.cases (0 : Fin 2) singletonSmall4681) =
      mixedMoment B node1807 node1807Labels := by
    have ha : raw1563 = raw1564 := by apply Matrix.ext; unfold raw1563 raw1564; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4681 = raw1564Labels := by decide +kernel
    rw [ha, hj, canonical1564 B hB]
  have hc1 : mixedMoment B raw1563 (Fin.cases (1 : Fin 2) singletonSmall4681) =
      mixedMoment B node2151 node2151Labels := by
    have ha : raw1563 = raw1565 := by apply Matrix.ext; unfold raw1563 raw1565; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4681 = raw1565Labels := by decide +kernel
    rw [ha, hj, canonical1565 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4684 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4684 node4684Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1810 node1810Labels + mixedMoment B node2152 node2152Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1566 singletonSmall4684
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4684) = raw1566Labels := by decide +kernel
  rw [hl, canonical1566 B hB] at h
  have hc0 : mixedMoment B raw1566 (Fin.cases (0 : Fin 2) singletonSmall4684) =
      mixedMoment B node1810 node1810Labels := by
    have ha : raw1566 = raw1567 := by apply Matrix.ext; unfold raw1566 raw1567; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4684 = raw1567Labels := by decide +kernel
    rw [ha, hj, canonical1567 B hB]
  have hc1 : mixedMoment B raw1566 (Fin.cases (1 : Fin 2) singletonSmall4684) =
      mixedMoment B node2152 node2152Labels := by
    have ha : raw1566 = raw1568 := by apply Matrix.ext; unfold raw1566 raw1568; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4684 = raw1568Labels := by decide +kernel
    rw [ha, hj, canonical1568 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4685 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4685 node4685Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1811 node1811Labels + mixedMoment B node2156 node2156Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1569 singletonSmall4685
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4685) = raw1569Labels := by decide +kernel
  rw [hl, canonical1569 B hB] at h
  have hc0 : mixedMoment B raw1569 (Fin.cases (0 : Fin 2) singletonSmall4685) =
      mixedMoment B node1811 node1811Labels := by
    have ha : raw1569 = raw1570 := by apply Matrix.ext; unfold raw1569 raw1570; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4685 = raw1570Labels := by decide +kernel
    rw [ha, hj, canonical1570 B hB]
  have hc1 : mixedMoment B raw1569 (Fin.cases (1 : Fin 2) singletonSmall4685) =
      mixedMoment B node2156 node2156Labels := by
    have ha : raw1569 = raw1571 := by apply Matrix.ext; unfold raw1569 raw1571; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4685 = raw1571Labels := by decide +kernel
    rw [ha, hj, canonical1571 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4686 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4686 node4686Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1812 node1812Labels + mixedMoment B node2165 node2165Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1572 singletonSmall4686
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4686) = raw1572Labels := by decide +kernel
  rw [hl, canonical1572 B hB] at h
  have hc0 : mixedMoment B raw1572 (Fin.cases (0 : Fin 2) singletonSmall4686) =
      mixedMoment B node1812 node1812Labels := by
    have ha : raw1572 = raw1573 := by apply Matrix.ext; unfold raw1572 raw1573; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4686 = raw1573Labels := by decide +kernel
    rw [ha, hj, canonical1573 B hB]
  have hc1 : mixedMoment B raw1572 (Fin.cases (1 : Fin 2) singletonSmall4686) =
      mixedMoment B node2165 node2165Labels := by
    have ha : raw1572 = raw1574 := by apply Matrix.ext; unfold raw1572 raw1574; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4686 = raw1574Labels := by decide +kernel
    rw [ha, hj, canonical1574 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4688 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4688 node4688Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1814 node1814Labels + mixedMoment B node2157 node2157Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1575 singletonSmall4688
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4688) = raw1575Labels := by decide +kernel
  rw [hl, canonical1575 B hB] at h
  have hc0 : mixedMoment B raw1575 (Fin.cases (0 : Fin 2) singletonSmall4688) =
      mixedMoment B node1814 node1814Labels := by
    have ha : raw1575 = raw1576 := by apply Matrix.ext; unfold raw1575 raw1576; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4688 = raw1576Labels := by decide +kernel
    rw [ha, hj, canonical1576 B hB]
  have hc1 : mixedMoment B raw1575 (Fin.cases (1 : Fin 2) singletonSmall4688) =
      mixedMoment B node2157 node2157Labels := by
    have ha : raw1575 = raw1577 := by apply Matrix.ext; unfold raw1575 raw1577; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4688 = raw1577Labels := by decide +kernel
    rw [ha, hj, canonical1577 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4689 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4689 node4689Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1815 node1815Labels + mixedMoment B node2166 node2166Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1578 singletonSmall4689
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4689) = raw1578Labels := by decide +kernel
  rw [hl, canonical1578 B hB] at h
  have hc0 : mixedMoment B raw1578 (Fin.cases (0 : Fin 2) singletonSmall4689) =
      mixedMoment B node1815 node1815Labels := by
    have ha : raw1578 = raw1579 := by apply Matrix.ext; unfold raw1578 raw1579; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4689 = raw1579Labels := by decide +kernel
    rw [ha, hj, canonical1579 B hB]
  have hc1 : mixedMoment B raw1578 (Fin.cases (1 : Fin 2) singletonSmall4689) =
      mixedMoment B node2166 node2166Labels := by
    have ha : raw1578 = raw1580 := by apply Matrix.ext; unfold raw1578 raw1580; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4689 = raw1580Labels := by decide +kernel
    rw [ha, hj, canonical1580 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4691 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4691 node4691Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1817 node1817Labels + mixedMoment B node2159 node2159Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1581 singletonSmall4691
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4691) = raw1581Labels := by decide +kernel
  rw [hl, canonical1581 B hB] at h
  have hc0 : mixedMoment B raw1581 (Fin.cases (0 : Fin 2) singletonSmall4691) =
      mixedMoment B node1817 node1817Labels := by
    have ha : raw1581 = raw1582 := by apply Matrix.ext; unfold raw1581 raw1582; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4691 = raw1582Labels := by decide +kernel
    rw [ha, hj, canonical1582 B hB]
  have hc1 : mixedMoment B raw1581 (Fin.cases (1 : Fin 2) singletonSmall4691) =
      mixedMoment B node2159 node2159Labels := by
    have ha : raw1581 = raw1583 := by apply Matrix.ext; unfold raw1581 raw1583; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4691 = raw1583Labels := by decide +kernel
    rw [ha, hj, canonical1583 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4692 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4692 node4692Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1818 node1818Labels + mixedMoment B node2168 node2168Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1584 singletonSmall4692
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4692) = raw1584Labels := by decide +kernel
  rw [hl, canonical1584 B hB] at h
  have hc0 : mixedMoment B raw1584 (Fin.cases (0 : Fin 2) singletonSmall4692) =
      mixedMoment B node1818 node1818Labels := by
    have ha : raw1584 = raw1585 := by apply Matrix.ext; unfold raw1584 raw1585; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4692 = raw1585Labels := by decide +kernel
    rw [ha, hj, canonical1585 B hB]
  have hc1 : mixedMoment B raw1584 (Fin.cases (1 : Fin 2) singletonSmall4692) =
      mixedMoment B node2168 node2168Labels := by
    have ha : raw1584 = raw1586 := by apply Matrix.ext; unfold raw1584 raw1586; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4692 = raw1586Labels := by decide +kernel
    rw [ha, hj, canonical1586 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4693 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4693 node4693Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1819 node1819Labels + mixedMoment B node2169 node2169Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1587 singletonSmall4693
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4693) = raw1587Labels := by decide +kernel
  rw [hl, canonical1587 B hB] at h
  have hc0 : mixedMoment B raw1587 (Fin.cases (0 : Fin 2) singletonSmall4693) =
      mixedMoment B node1819 node1819Labels := by
    have ha : raw1587 = raw1588 := by apply Matrix.ext; unfold raw1587 raw1588; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4693 = raw1588Labels := by decide +kernel
    rw [ha, hj, canonical1588 B hB]
  have hc1 : mixedMoment B raw1587 (Fin.cases (1 : Fin 2) singletonSmall4693) =
      mixedMoment B node2169 node2169Labels := by
    have ha : raw1587 = raw1589 := by apply Matrix.ext; unfold raw1587 raw1589; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4693 = raw1589Labels := by decide +kernel
    rw [ha, hj, canonical1589 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4706 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4706 node4706Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1860 node1860Labels + mixedMoment B node1888 node1888Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1590 singletonSmall4706
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4706) = raw1590Labels := by decide +kernel
  rw [hl, canonical1590 B hB] at h
  have hc0 : mixedMoment B raw1590 (Fin.cases (0 : Fin 2) singletonSmall4706) =
      mixedMoment B node1860 node1860Labels := by
    have ha : raw1590 = raw1591 := by apply Matrix.ext; unfold raw1590 raw1591; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4706 = raw1591Labels := by decide +kernel
    rw [ha, hj, canonical1591 B hB]
  have hc1 : mixedMoment B raw1590 (Fin.cases (1 : Fin 2) singletonSmall4706) =
      mixedMoment B node1888 node1888Labels := by
    have ha : raw1590 = raw1592 := by apply Matrix.ext; unfold raw1590 raw1592; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4706 = raw1592Labels := by decide +kernel
    rw [ha, hj, canonical1592 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4707 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4707 node4707Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1861 node1861Labels + mixedMoment B node1889 node1889Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1593 singletonSmall4707
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4707) = raw1593Labels := by decide +kernel
  rw [hl, canonical1593 B hB] at h
  have hc0 : mixedMoment B raw1593 (Fin.cases (0 : Fin 2) singletonSmall4707) =
      mixedMoment B node1861 node1861Labels := by
    have ha : raw1593 = raw1594 := by apply Matrix.ext; unfold raw1593 raw1594; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4707 = raw1594Labels := by decide +kernel
    rw [ha, hj, canonical1594 B hB]
  have hc1 : mixedMoment B raw1593 (Fin.cases (1 : Fin 2) singletonSmall4707) =
      mixedMoment B node1889 node1889Labels := by
    have ha : raw1593 = raw1595 := by apply Matrix.ext; unfold raw1593 raw1595; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4707 = raw1595Labels := by decide +kernel
    rw [ha, hj, canonical1595 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4709 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4709 node4709Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1863 node1863Labels + mixedMoment B node1883 node1883Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1596 singletonSmall4709
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4709) = raw1596Labels := by decide +kernel
  rw [hl, canonical1596 B hB] at h
  have hc0 : mixedMoment B raw1596 (Fin.cases (0 : Fin 2) singletonSmall4709) =
      mixedMoment B node1863 node1863Labels := by
    have ha : raw1596 = raw1597 := by apply Matrix.ext; unfold raw1596 raw1597; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4709 = raw1597Labels := by decide +kernel
    rw [ha, hj, canonical1597 B hB]
  have hc1 : mixedMoment B raw1596 (Fin.cases (1 : Fin 2) singletonSmall4709) =
      mixedMoment B node1883 node1883Labels := by
    have ha : raw1596 = raw1598 := by apply Matrix.ext; unfold raw1596 raw1598; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4709 = raw1598Labels := by decide +kernel
    rw [ha, hj, canonical1598 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4710 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4710 node4710Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1864 node1864Labels + mixedMoment B node1882 node1882Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1599 singletonSmall4710
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4710) = raw1599Labels := by decide +kernel
  rw [hl, canonical1599 B hB] at h
  have hc0 : mixedMoment B raw1599 (Fin.cases (0 : Fin 2) singletonSmall4710) =
      mixedMoment B node1864 node1864Labels := by
    have ha : raw1599 = raw1600 := by apply Matrix.ext; unfold raw1599 raw1600; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4710 = raw1600Labels := by decide +kernel
    rw [ha, hj, canonical1600 B hB]
  have hc1 : mixedMoment B raw1599 (Fin.cases (1 : Fin 2) singletonSmall4710) =
      mixedMoment B node1882 node1882Labels := by
    have ha : raw1599 = raw1601 := by apply Matrix.ext; unfold raw1599 raw1601; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4710 = raw1601Labels := by decide +kernel
    rw [ha, hj, canonical1601 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4713 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4713 node4713Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1867 node1867Labels + mixedMoment B node1891 node1891Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1602 singletonSmall4713
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4713) = raw1602Labels := by decide +kernel
  rw [hl, canonical1602 B hB] at h
  have hc0 : mixedMoment B raw1602 (Fin.cases (0 : Fin 2) singletonSmall4713) =
      mixedMoment B node1867 node1867Labels := by
    have ha : raw1602 = raw1603 := by apply Matrix.ext; unfold raw1602 raw1603; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4713 = raw1603Labels := by decide +kernel
    rw [ha, hj, canonical1603 B hB]
  have hc1 : mixedMoment B raw1602 (Fin.cases (1 : Fin 2) singletonSmall4713) =
      mixedMoment B node1891 node1891Labels := by
    have ha : raw1602 = raw1604 := by apply Matrix.ext; unfold raw1602 raw1604; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4713 = raw1604Labels := by decide +kernel
    rw [ha, hj, canonical1604 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4714 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4714 node4714Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1868 node1868Labels + mixedMoment B node1885 node1885Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1605 singletonSmall4714
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4714) = raw1605Labels := by decide +kernel
  rw [hl, canonical1605 B hB] at h
  have hc0 : mixedMoment B raw1605 (Fin.cases (0 : Fin 2) singletonSmall4714) =
      mixedMoment B node1868 node1868Labels := by
    have ha : raw1605 = raw1606 := by apply Matrix.ext; unfold raw1605 raw1606; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4714 = raw1606Labels := by decide +kernel
    rw [ha, hj, canonical1606 B hB]
  have hc1 : mixedMoment B raw1605 (Fin.cases (1 : Fin 2) singletonSmall4714) =
      mixedMoment B node1885 node1885Labels := by
    have ha : raw1605 = raw1607 := by apply Matrix.ext; unfold raw1605 raw1607; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4714 = raw1607Labels := by decide +kernel
    rw [ha, hj, canonical1607 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4716 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4716 node4716Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1870 node1870Labels + mixedMoment B node1886 node1886Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1608 singletonSmall4716
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4716) = raw1608Labels := by decide +kernel
  rw [hl, canonical1608 B hB] at h
  have hc0 : mixedMoment B raw1608 (Fin.cases (0 : Fin 2) singletonSmall4716) =
      mixedMoment B node1870 node1870Labels := by
    have ha : raw1608 = raw1609 := by apply Matrix.ext; unfold raw1608 raw1609; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4716 = raw1609Labels := by decide +kernel
    rw [ha, hj, canonical1609 B hB]
  have hc1 : mixedMoment B raw1608 (Fin.cases (1 : Fin 2) singletonSmall4716) =
      mixedMoment B node1886 node1886Labels := by
    have ha : raw1608 = raw1610 := by apply Matrix.ext; unfold raw1608 raw1610; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4716 = raw1610Labels := by decide +kernel
    rw [ha, hj, canonical1610 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4717 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4717 node4717Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1871 node1871Labels + mixedMoment B node1892 node1892Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1611 singletonSmall4717
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4717) = raw1611Labels := by decide +kernel
  rw [hl, canonical1611 B hB] at h
  have hc0 : mixedMoment B raw1611 (Fin.cases (0 : Fin 2) singletonSmall4717) =
      mixedMoment B node1871 node1871Labels := by
    have ha : raw1611 = raw1612 := by apply Matrix.ext; unfold raw1611 raw1612; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4717 = raw1612Labels := by decide +kernel
    rw [ha, hj, canonical1612 B hB]
  have hc1 : mixedMoment B raw1611 (Fin.cases (1 : Fin 2) singletonSmall4717) =
      mixedMoment B node1892 node1892Labels := by
    have ha : raw1611 = raw1613 := by apply Matrix.ext; unfold raw1611 raw1613; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4717 = raw1613Labels := by decide +kernel
    rw [ha, hj, canonical1613 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4719 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4719 node4719Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1873 node1873Labels + mixedMoment B node1893 node1893Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1614 singletonSmall4719
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4719) = raw1614Labels := by decide +kernel
  rw [hl, canonical1614 B hB] at h
  have hc0 : mixedMoment B raw1614 (Fin.cases (0 : Fin 2) singletonSmall4719) =
      mixedMoment B node1873 node1873Labels := by
    have ha : raw1614 = raw1615 := by apply Matrix.ext; unfold raw1614 raw1615; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4719 = raw1615Labels := by decide +kernel
    rw [ha, hj, canonical1615 B hB]
  have hc1 : mixedMoment B raw1614 (Fin.cases (1 : Fin 2) singletonSmall4719) =
      mixedMoment B node1893 node1893Labels := by
    have ha : raw1614 = raw1616 := by apply Matrix.ext; unfold raw1614 raw1616; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4719 = raw1616Labels := by decide +kernel
    rw [ha, hj, canonical1616 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4720 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4720 node4720Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1874 node1874Labels + mixedMoment B node1896 node1896Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1617 singletonSmall4720
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4720) = raw1617Labels := by decide +kernel
  rw [hl, canonical1617 B hB] at h
  have hc0 : mixedMoment B raw1617 (Fin.cases (0 : Fin 2) singletonSmall4720) =
      mixedMoment B node1874 node1874Labels := by
    have ha : raw1617 = raw1618 := by apply Matrix.ext; unfold raw1617 raw1618; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4720 = raw1618Labels := by decide +kernel
    rw [ha, hj, canonical1618 B hB]
  have hc1 : mixedMoment B raw1617 (Fin.cases (1 : Fin 2) singletonSmall4720) =
      mixedMoment B node1896 node1896Labels := by
    have ha : raw1617 = raw1619 := by apply Matrix.ext; unfold raw1617 raw1619; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4720 = raw1619Labels := by decide +kernel
    rw [ha, hj, canonical1619 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4721 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4721 node4721Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1875 node1875Labels + mixedMoment B node1905 node1905Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1620 singletonSmall4721
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4721) = raw1620Labels := by decide +kernel
  rw [hl, canonical1620 B hB] at h
  have hc0 : mixedMoment B raw1620 (Fin.cases (0 : Fin 2) singletonSmall4721) =
      mixedMoment B node1875 node1875Labels := by
    have ha : raw1620 = raw1621 := by apply Matrix.ext; unfold raw1620 raw1621; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4721 = raw1621Labels := by decide +kernel
    rw [ha, hj, canonical1621 B hB]
  have hc1 : mixedMoment B raw1620 (Fin.cases (1 : Fin 2) singletonSmall4721) =
      mixedMoment B node1905 node1905Labels := by
    have ha : raw1620 = raw1622 := by apply Matrix.ext; unfold raw1620 raw1622; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4721 = raw1622Labels := by decide +kernel
    rw [ha, hj, canonical1622 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4722 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4722 node4722Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1876 node1876Labels + mixedMoment B node1906 node1906Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1623 singletonSmall4722
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4722) = raw1623Labels := by decide +kernel
  rw [hl, canonical1623 B hB] at h
  have hc0 : mixedMoment B raw1623 (Fin.cases (0 : Fin 2) singletonSmall4722) =
      mixedMoment B node1876 node1876Labels := by
    have ha : raw1623 = raw1624 := by apply Matrix.ext; unfold raw1623 raw1624; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4722 = raw1624Labels := by decide +kernel
    rw [ha, hj, canonical1624 B hB]
  have hc1 : mixedMoment B raw1623 (Fin.cases (1 : Fin 2) singletonSmall4722) =
      mixedMoment B node1906 node1906Labels := by
    have ha : raw1623 = raw1625 := by apply Matrix.ext; unfold raw1623 raw1625; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4722 = raw1625Labels := by decide +kernel
    rw [ha, hj, canonical1625 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4723 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4723 node4723Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1877 node1877Labels + mixedMoment B node1935 node1935Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1626 singletonSmall4723
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4723) = raw1626Labels := by decide +kernel
  rw [hl, canonical1626 B hB] at h
  have hc0 : mixedMoment B raw1626 (Fin.cases (0 : Fin 2) singletonSmall4723) =
      mixedMoment B node1877 node1877Labels := by
    have ha : raw1626 = raw1627 := by apply Matrix.ext; unfold raw1626 raw1627; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4723 = raw1627Labels := by decide +kernel
    rw [ha, hj, canonical1627 B hB]
  have hc1 : mixedMoment B raw1626 (Fin.cases (1 : Fin 2) singletonSmall4723) =
      mixedMoment B node1935 node1935Labels := by
    have ha : raw1626 = raw1628 := by apply Matrix.ext; unfold raw1626 raw1628; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4723 = raw1628Labels := by decide +kernel
    rw [ha, hj, canonical1628 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4724 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4724 node4724Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1878 node1878Labels + mixedMoment B node1919 node1919Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1629 singletonSmall4724
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4724) = raw1629Labels := by decide +kernel
  rw [hl, canonical1629 B hB] at h
  have hc0 : mixedMoment B raw1629 (Fin.cases (0 : Fin 2) singletonSmall4724) =
      mixedMoment B node1878 node1878Labels := by
    have ha : raw1629 = raw1630 := by apply Matrix.ext; unfold raw1629 raw1630; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4724 = raw1630Labels := by decide +kernel
    rw [ha, hj, canonical1630 B hB]
  have hc1 : mixedMoment B raw1629 (Fin.cases (1 : Fin 2) singletonSmall4724) =
      mixedMoment B node1919 node1919Labels := by
    have ha : raw1629 = raw1631 := by apply Matrix.ext; unfold raw1629 raw1631; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4724 = raw1631Labels := by decide +kernel
    rw [ha, hj, canonical1631 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4725 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4725 node4725Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1879 node1879Labels + mixedMoment B node1936 node1936Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1632 singletonSmall4725
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4725) = raw1632Labels := by decide +kernel
  rw [hl, canonical1632 B hB] at h
  have hc0 : mixedMoment B raw1632 (Fin.cases (0 : Fin 2) singletonSmall4725) =
      mixedMoment B node1879 node1879Labels := by
    have ha : raw1632 = raw1633 := by apply Matrix.ext; unfold raw1632 raw1633; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4725 = raw1633Labels := by decide +kernel
    rw [ha, hj, canonical1633 B hB]
  have hc1 : mixedMoment B raw1632 (Fin.cases (1 : Fin 2) singletonSmall4725) =
      mixedMoment B node1936 node1936Labels := by
    have ha : raw1632 = raw1634 := by apply Matrix.ext; unfold raw1632 raw1634; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4725 = raw1634Labels := by decide +kernel
    rw [ha, hj, canonical1634 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4726 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4726 node4726Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1880 node1880Labels + mixedMoment B node1938 node1938Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1635 singletonSmall4726
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4726) = raw1635Labels := by decide +kernel
  rw [hl, canonical1635 B hB] at h
  have hc0 : mixedMoment B raw1635 (Fin.cases (0 : Fin 2) singletonSmall4726) =
      mixedMoment B node1880 node1880Labels := by
    have ha : raw1635 = raw1636 := by apply Matrix.ext; unfold raw1635 raw1636; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4726 = raw1636Labels := by decide +kernel
    rw [ha, hj, canonical1636 B hB]
  have hc1 : mixedMoment B raw1635 (Fin.cases (1 : Fin 2) singletonSmall4726) =
      mixedMoment B node1938 node1938Labels := by
    have ha : raw1635 = raw1637 := by apply Matrix.ext; unfold raw1635 raw1637; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4726 = raw1637Labels := by decide +kernel
    rw [ha, hj, canonical1637 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4727 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4727 node4727Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1881 node1881Labels + mixedMoment B node1939 node1939Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1638 singletonSmall4727
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4727) = raw1638Labels := by decide +kernel
  rw [hl, canonical1638 B hB] at h
  have hc0 : mixedMoment B raw1638 (Fin.cases (0 : Fin 2) singletonSmall4727) =
      mixedMoment B node1881 node1881Labels := by
    have ha : raw1638 = raw1639 := by apply Matrix.ext; unfold raw1638 raw1639; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4727 = raw1639Labels := by decide +kernel
    rw [ha, hj, canonical1639 B hB]
  have hc1 : mixedMoment B raw1638 (Fin.cases (1 : Fin 2) singletonSmall4727) =
      mixedMoment B node1939 node1939Labels := by
    have ha : raw1638 = raw1640 := by apply Matrix.ext; unfold raw1638 raw1640; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4727 = raw1640Labels := by decide +kernel
    rw [ha, hj, canonical1640 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4728 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4728 node4728Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1897 node1897Labels + mixedMoment B node1907 node1907Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1641 singletonSmall4728
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4728) = raw1641Labels := by decide +kernel
  rw [hl, canonical1641 B hB] at h
  have hc0 : mixedMoment B raw1641 (Fin.cases (0 : Fin 2) singletonSmall4728) =
      mixedMoment B node1897 node1897Labels := by
    have ha : raw1641 = raw1642 := by apply Matrix.ext; unfold raw1641 raw1642; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4728 = raw1642Labels := by decide +kernel
    rw [ha, hj, canonical1642 B hB]
  have hc1 : mixedMoment B raw1641 (Fin.cases (1 : Fin 2) singletonSmall4728) =
      mixedMoment B node1907 node1907Labels := by
    have ha : raw1641 = raw1643 := by apply Matrix.ext; unfold raw1641 raw1643; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4728 = raw1643Labels := by decide +kernel
    rw [ha, hj, canonical1643 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4729 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4729 node4729Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1898 node1898Labels + mixedMoment B node1940 node1940Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1644 singletonSmall4729
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4729) = raw1644Labels := by decide +kernel
  rw [hl, canonical1644 B hB] at h
  have hc0 : mixedMoment B raw1644 (Fin.cases (0 : Fin 2) singletonSmall4729) =
      mixedMoment B node1898 node1898Labels := by
    have ha : raw1644 = raw1645 := by apply Matrix.ext; unfold raw1644 raw1645; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4729 = raw1645Labels := by decide +kernel
    rw [ha, hj, canonical1645 B hB]
  have hc1 : mixedMoment B raw1644 (Fin.cases (1 : Fin 2) singletonSmall4729) =
      mixedMoment B node1940 node1940Labels := by
    have ha : raw1644 = raw1646 := by apply Matrix.ext; unfold raw1644 raw1646; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4729 = raw1646Labels := by decide +kernel
    rw [ha, hj, canonical1646 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4731 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4731 node4731Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1900 node1900Labels + mixedMoment B node1921 node1921Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1647 singletonSmall4731
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4731) = raw1647Labels := by decide +kernel
  rw [hl, canonical1647 B hB] at h
  have hc0 : mixedMoment B raw1647 (Fin.cases (0 : Fin 2) singletonSmall4731) =
      mixedMoment B node1900 node1900Labels := by
    have ha : raw1647 = raw1648 := by apply Matrix.ext; unfold raw1647 raw1648; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4731 = raw1648Labels := by decide +kernel
    rw [ha, hj, canonical1648 B hB]
  have hc1 : mixedMoment B raw1647 (Fin.cases (1 : Fin 2) singletonSmall4731) =
      mixedMoment B node1921 node1921Labels := by
    have ha : raw1647 = raw1649 := by apply Matrix.ext; unfold raw1647 raw1649; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4731 = raw1649Labels := by decide +kernel
    rw [ha, hj, canonical1649 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4732 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4732 node4732Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1901 node1901Labels + mixedMoment B node1941 node1941Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1650 singletonSmall4732
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4732) = raw1650Labels := by decide +kernel
  rw [hl, canonical1650 B hB] at h
  have hc0 : mixedMoment B raw1650 (Fin.cases (0 : Fin 2) singletonSmall4732) =
      mixedMoment B node1901 node1901Labels := by
    have ha : raw1650 = raw1651 := by apply Matrix.ext; unfold raw1650 raw1651; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4732 = raw1651Labels := by decide +kernel
    rw [ha, hj, canonical1651 B hB]
  have hc1 : mixedMoment B raw1650 (Fin.cases (1 : Fin 2) singletonSmall4732) =
      mixedMoment B node1941 node1941Labels := by
    have ha : raw1650 = raw1652 := by apply Matrix.ext; unfold raw1650 raw1652; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4732 = raw1652Labels := by decide +kernel
    rw [ha, hj, canonical1652 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

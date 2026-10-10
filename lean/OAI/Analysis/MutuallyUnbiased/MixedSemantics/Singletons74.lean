import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical13

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4737 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4737 node4737Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1909 node1909Labels + mixedMoment B node1909 node1909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1653 singletonSmall4737
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4737) = raw1653Labels := by decide +kernel
  rw [hl, canonical1653 B hB] at h
  have hc0 : mixedMoment B raw1653 (Fin.cases (0 : Fin 2) singletonSmall4737) =
      mixedMoment B node1909 node1909Labels := by
    have ha : raw1653 = raw1654 := by apply Matrix.ext; unfold raw1653 raw1654; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4737 = raw1654Labels := by decide +kernel
    rw [ha, hj, canonical1654 B hB]
  have hc1 : mixedMoment B raw1653 (Fin.cases (1 : Fin 2) singletonSmall4737) =
      mixedMoment B node1909 node1909Labels := by
    have ha : raw1653 = raw1655 := by apply Matrix.ext; unfold raw1653 raw1655; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4737 = raw1655Labels := by decide +kernel
    rw [ha, hj, canonical1655 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4740 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4740 node4740Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1913 node1913Labels + mixedMoment B node1922 node1922Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1656 singletonSmall4740
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4740) = raw1656Labels := by decide +kernel
  rw [hl, canonical1656 B hB] at h
  have hc0 : mixedMoment B raw1656 (Fin.cases (0 : Fin 2) singletonSmall4740) =
      mixedMoment B node1913 node1913Labels := by
    have ha : raw1656 = raw1657 := by apply Matrix.ext; unfold raw1656 raw1657; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4740 = raw1657Labels := by decide +kernel
    rw [ha, hj, canonical1657 B hB]
  have hc1 : mixedMoment B raw1656 (Fin.cases (1 : Fin 2) singletonSmall4740) =
      mixedMoment B node1922 node1922Labels := by
    have ha : raw1656 = raw1658 := by apply Matrix.ext; unfold raw1656 raw1658; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4740 = raw1658Labels := by decide +kernel
    rw [ha, hj, canonical1658 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4742 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4742 node4742Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1915 node1915Labels + mixedMoment B node1946 node1946Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1659 singletonSmall4742
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4742) = raw1659Labels := by decide +kernel
  rw [hl, canonical1659 B hB] at h
  have hc0 : mixedMoment B raw1659 (Fin.cases (0 : Fin 2) singletonSmall4742) =
      mixedMoment B node1915 node1915Labels := by
    have ha : raw1659 = raw1660 := by apply Matrix.ext; unfold raw1659 raw1660; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4742 = raw1660Labels := by decide +kernel
    rw [ha, hj, canonical1660 B hB]
  have hc1 : mixedMoment B raw1659 (Fin.cases (1 : Fin 2) singletonSmall4742) =
      mixedMoment B node1946 node1946Labels := by
    have ha : raw1659 = raw1661 := by apply Matrix.ext; unfold raw1659 raw1661; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4742 = raw1661Labels := by decide +kernel
    rw [ha, hj, canonical1661 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4744 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4744 node4744Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1917 node1917Labels + mixedMoment B node1924 node1924Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1662 singletonSmall4744
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4744) = raw1662Labels := by decide +kernel
  rw [hl, canonical1662 B hB] at h
  have hc0 : mixedMoment B raw1662 (Fin.cases (0 : Fin 2) singletonSmall4744) =
      mixedMoment B node1917 node1917Labels := by
    have ha : raw1662 = raw1663 := by apply Matrix.ext; unfold raw1662 raw1663; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4744 = raw1663Labels := by decide +kernel
    rw [ha, hj, canonical1663 B hB]
  have hc1 : mixedMoment B raw1662 (Fin.cases (1 : Fin 2) singletonSmall4744) =
      mixedMoment B node1924 node1924Labels := by
    have ha : raw1662 = raw1664 := by apply Matrix.ext; unfold raw1662 raw1664; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4744 = raw1664Labels := by decide +kernel
    rw [ha, hj, canonical1664 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4746 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4746 node4746Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1925 node1925Labels + mixedMoment B node1925 node1925Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1665 singletonSmall4746
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4746) = raw1665Labels := by decide +kernel
  rw [hl, canonical1665 B hB] at h
  have hc0 : mixedMoment B raw1665 (Fin.cases (0 : Fin 2) singletonSmall4746) =
      mixedMoment B node1925 node1925Labels := by
    have ha : raw1665 = raw1666 := by apply Matrix.ext; unfold raw1665 raw1666; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4746 = raw1666Labels := by decide +kernel
    rw [ha, hj, canonical1666 B hB]
  have hc1 : mixedMoment B raw1665 (Fin.cases (1 : Fin 2) singletonSmall4746) =
      mixedMoment B node1925 node1925Labels := by
    have ha : raw1665 = raw1667 := by apply Matrix.ext; unfold raw1665 raw1667; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4746 = raw1667Labels := by decide +kernel
    rw [ha, hj, canonical1667 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4747 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4747 node4747Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1926 node1926Labels + mixedMoment B node1948 node1948Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1668 singletonSmall4747
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4747) = raw1668Labels := by decide +kernel
  rw [hl, canonical1668 B hB] at h
  have hc0 : mixedMoment B raw1668 (Fin.cases (0 : Fin 2) singletonSmall4747) =
      mixedMoment B node1926 node1926Labels := by
    have ha : raw1668 = raw1669 := by apply Matrix.ext; unfold raw1668 raw1669; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4747 = raw1669Labels := by decide +kernel
    rw [ha, hj, canonical1669 B hB]
  have hc1 : mixedMoment B raw1668 (Fin.cases (1 : Fin 2) singletonSmall4747) =
      mixedMoment B node1948 node1948Labels := by
    have ha : raw1668 = raw1670 := by apply Matrix.ext; unfold raw1668 raw1670; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4747 = raw1670Labels := by decide +kernel
    rw [ha, hj, canonical1670 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4749 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4749 node4749Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1928 node1928Labels + mixedMoment B node1928 node1928Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1671 singletonSmall4749
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4749) = raw1671Labels := by decide +kernel
  rw [hl, canonical1671 B hB] at h
  have hc0 : mixedMoment B raw1671 (Fin.cases (0 : Fin 2) singletonSmall4749) =
      mixedMoment B node1928 node1928Labels := by
    have ha : raw1671 = raw1672 := by apply Matrix.ext; unfold raw1671 raw1672; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4749 = raw1672Labels := by decide +kernel
    rw [ha, hj, canonical1672 B hB]
  have hc1 : mixedMoment B raw1671 (Fin.cases (1 : Fin 2) singletonSmall4749) =
      mixedMoment B node1928 node1928Labels := by
    have ha : raw1671 = raw1673 := by apply Matrix.ext; unfold raw1671 raw1673; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4749 = raw1673Labels := by decide +kernel
    rw [ha, hj, canonical1673 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4750 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4750 node4750Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1929 node1929Labels + mixedMoment B node1949 node1949Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1674 singletonSmall4750
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4750) = raw1674Labels := by decide +kernel
  rw [hl, canonical1674 B hB] at h
  have hc0 : mixedMoment B raw1674 (Fin.cases (0 : Fin 2) singletonSmall4750) =
      mixedMoment B node1929 node1929Labels := by
    have ha : raw1674 = raw1675 := by apply Matrix.ext; unfold raw1674 raw1675; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4750 = raw1675Labels := by decide +kernel
    rw [ha, hj, canonical1675 B hB]
  have hc1 : mixedMoment B raw1674 (Fin.cases (1 : Fin 2) singletonSmall4750) =
      mixedMoment B node1949 node1949Labels := by
    have ha : raw1674 = raw1676 := by apply Matrix.ext; unfold raw1674 raw1676; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4750 = raw1676Labels := by decide +kernel
    rw [ha, hj, canonical1676 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4754 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4754 node4754Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1951 node1951Labels + mixedMoment B node1951 node1951Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1677 singletonSmall4754
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4754) = raw1677Labels := by decide +kernel
  rw [hl, canonical1677 B hB] at h
  have hc0 : mixedMoment B raw1677 (Fin.cases (0 : Fin 2) singletonSmall4754) =
      mixedMoment B node1951 node1951Labels := by
    have ha : raw1677 = raw1678 := by apply Matrix.ext; unfold raw1677 raw1678; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4754 = raw1678Labels := by decide +kernel
    rw [ha, hj, canonical1678 B hB]
  have hc1 : mixedMoment B raw1677 (Fin.cases (1 : Fin 2) singletonSmall4754) =
      mixedMoment B node1951 node1951Labels := by
    have ha : raw1677 = raw1679 := by apply Matrix.ext; unfold raw1677 raw1679; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4754 = raw1679Labels := by decide +kernel
    rw [ha, hj, canonical1679 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4755 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4755 node4755Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1954 node1954Labels + mixedMoment B node1985 node1985Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1680 singletonSmall4755
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4755) = raw1680Labels := by decide +kernel
  rw [hl, canonical1680 B hB] at h
  have hc0 : mixedMoment B raw1680 (Fin.cases (0 : Fin 2) singletonSmall4755) =
      mixedMoment B node1954 node1954Labels := by
    have ha : raw1680 = raw1681 := by apply Matrix.ext; unfold raw1680 raw1681; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4755 = raw1681Labels := by decide +kernel
    rw [ha, hj, canonical1681 B hB]
  have hc1 : mixedMoment B raw1680 (Fin.cases (1 : Fin 2) singletonSmall4755) =
      mixedMoment B node1985 node1985Labels := by
    have ha : raw1680 = raw1682 := by apply Matrix.ext; unfold raw1680 raw1682; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4755 = raw1682Labels := by decide +kernel
    rw [ha, hj, canonical1682 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4758 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4758 node4758Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1958 node1958Labels + mixedMoment B node2069 node2069Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1683 singletonSmall4758
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4758) = raw1683Labels := by decide +kernel
  rw [hl, canonical1683 B hB] at h
  have hc0 : mixedMoment B raw1683 (Fin.cases (0 : Fin 2) singletonSmall4758) =
      mixedMoment B node1958 node1958Labels := by
    have ha : raw1683 = raw1684 := by apply Matrix.ext; unfold raw1683 raw1684; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4758 = raw1684Labels := by decide +kernel
    rw [ha, hj, canonical1684 B hB]
  have hc1 : mixedMoment B raw1683 (Fin.cases (1 : Fin 2) singletonSmall4758) =
      mixedMoment B node2069 node2069Labels := by
    have ha : raw1683 = raw1685 := by apply Matrix.ext; unfold raw1683 raw1685; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4758 = raw1685Labels := by decide +kernel
    rw [ha, hj, canonical1685 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4759 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4759 node4759Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1959 node1959Labels + mixedMoment B node2170 node2170Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1686 singletonSmall4759
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4759) = raw1686Labels := by decide +kernel
  rw [hl, canonical1686 B hB] at h
  have hc0 : mixedMoment B raw1686 (Fin.cases (0 : Fin 2) singletonSmall4759) =
      mixedMoment B node1959 node1959Labels := by
    have ha : raw1686 = raw1687 := by apply Matrix.ext; unfold raw1686 raw1687; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4759 = raw1687Labels := by decide +kernel
    rw [ha, hj, canonical1687 B hB]
  have hc1 : mixedMoment B raw1686 (Fin.cases (1 : Fin 2) singletonSmall4759) =
      mixedMoment B node2170 node2170Labels := by
    have ha : raw1686 = raw1688 := by apply Matrix.ext; unfold raw1686 raw1688; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4759 = raw1688Labels := by decide +kernel
    rw [ha, hj, canonical1688 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4760 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4760 node4760Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1960 node1960Labels + mixedMoment B node2173 node2173Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1689 singletonSmall4760
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4760) = raw1689Labels := by decide +kernel
  rw [hl, canonical1689 B hB] at h
  have hc0 : mixedMoment B raw1689 (Fin.cases (0 : Fin 2) singletonSmall4760) =
      mixedMoment B node1960 node1960Labels := by
    have ha : raw1689 = raw1690 := by apply Matrix.ext; unfold raw1689 raw1690; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4760 = raw1690Labels := by decide +kernel
    rw [ha, hj, canonical1690 B hB]
  have hc1 : mixedMoment B raw1689 (Fin.cases (1 : Fin 2) singletonSmall4760) =
      mixedMoment B node2173 node2173Labels := by
    have ha : raw1689 = raw1691 := by apply Matrix.ext; unfold raw1689 raw1691; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4760 = raw1691Labels := by decide +kernel
    rw [ha, hj, canonical1691 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4763 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4763 node4763Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1963 node1963Labels + mixedMoment B node2174 node2174Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1692 singletonSmall4763
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4763) = raw1692Labels := by decide +kernel
  rw [hl, canonical1692 B hB] at h
  have hc0 : mixedMoment B raw1692 (Fin.cases (0 : Fin 2) singletonSmall4763) =
      mixedMoment B node1963 node1963Labels := by
    have ha : raw1692 = raw1693 := by apply Matrix.ext; unfold raw1692 raw1693; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4763 = raw1693Labels := by decide +kernel
    rw [ha, hj, canonical1693 B hB]
  have hc1 : mixedMoment B raw1692 (Fin.cases (1 : Fin 2) singletonSmall4763) =
      mixedMoment B node2174 node2174Labels := by
    have ha : raw1692 = raw1694 := by apply Matrix.ext; unfold raw1692 raw1694; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4763 = raw1694Labels := by decide +kernel
    rw [ha, hj, canonical1694 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4764 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4764 node4764Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1964 node1964Labels + mixedMoment B node2182 node2182Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1695 singletonSmall4764
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4764) = raw1695Labels := by decide +kernel
  rw [hl, canonical1695 B hB] at h
  have hc0 : mixedMoment B raw1695 (Fin.cases (0 : Fin 2) singletonSmall4764) =
      mixedMoment B node1964 node1964Labels := by
    have ha : raw1695 = raw1696 := by apply Matrix.ext; unfold raw1695 raw1696; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4764 = raw1696Labels := by decide +kernel
    rw [ha, hj, canonical1696 B hB]
  have hc1 : mixedMoment B raw1695 (Fin.cases (1 : Fin 2) singletonSmall4764) =
      mixedMoment B node2182 node2182Labels := by
    have ha : raw1695 = raw1697 := by apply Matrix.ext; unfold raw1695 raw1697; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4764 = raw1697Labels := by decide +kernel
    rw [ha, hj, canonical1697 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4766 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4766 node4766Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1966 node1966Labels + mixedMoment B node2177 node2177Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1698 singletonSmall4766
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4766) = raw1698Labels := by decide +kernel
  rw [hl, canonical1698 B hB] at h
  have hc0 : mixedMoment B raw1698 (Fin.cases (0 : Fin 2) singletonSmall4766) =
      mixedMoment B node1966 node1966Labels := by
    have ha : raw1698 = raw1699 := by apply Matrix.ext; unfold raw1698 raw1699; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4766 = raw1699Labels := by decide +kernel
    rw [ha, hj, canonical1699 B hB]
  have hc1 : mixedMoment B raw1698 (Fin.cases (1 : Fin 2) singletonSmall4766) =
      mixedMoment B node2177 node2177Labels := by
    have ha : raw1698 = raw1700 := by apply Matrix.ext; unfold raw1698 raw1700; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4766 = raw1700Labels := by decide +kernel
    rw [ha, hj, canonical1700 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4767 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4767 node4767Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1967 node1967Labels + mixedMoment B node2183 node2183Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1701 singletonSmall4767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4767) = raw1701Labels := by decide +kernel
  rw [hl, canonical1701 B hB] at h
  have hc0 : mixedMoment B raw1701 (Fin.cases (0 : Fin 2) singletonSmall4767) =
      mixedMoment B node1967 node1967Labels := by
    have ha : raw1701 = raw1702 := by apply Matrix.ext; unfold raw1701 raw1702; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4767 = raw1702Labels := by decide +kernel
    rw [ha, hj, canonical1702 B hB]
  have hc1 : mixedMoment B raw1701 (Fin.cases (1 : Fin 2) singletonSmall4767) =
      mixedMoment B node2183 node2183Labels := by
    have ha : raw1701 = raw1703 := by apply Matrix.ext; unfold raw1701 raw1703; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4767 = raw1703Labels := by decide +kernel
    rw [ha, hj, canonical1703 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4769 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4769 node4769Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1969 node1969Labels + mixedMoment B node2185 node2185Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1704 singletonSmall4769
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4769) = raw1704Labels := by decide +kernel
  rw [hl, canonical1704 B hB] at h
  have hc0 : mixedMoment B raw1704 (Fin.cases (0 : Fin 2) singletonSmall4769) =
      mixedMoment B node1969 node1969Labels := by
    have ha : raw1704 = raw1705 := by apply Matrix.ext; unfold raw1704 raw1705; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4769 = raw1705Labels := by decide +kernel
    rw [ha, hj, canonical1705 B hB]
  have hc1 : mixedMoment B raw1704 (Fin.cases (1 : Fin 2) singletonSmall4769) =
      mixedMoment B node2185 node2185Labels := by
    have ha : raw1704 = raw1706 := by apply Matrix.ext; unfold raw1704 raw1706; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4769 = raw1706Labels := by decide +kernel
    rw [ha, hj, canonical1706 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4770 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4770 node4770Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1970 node1970Labels + mixedMoment B node2186 node2186Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1707 singletonSmall4770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4770) = raw1707Labels := by decide +kernel
  rw [hl, canonical1707 B hB] at h
  have hc0 : mixedMoment B raw1707 (Fin.cases (0 : Fin 2) singletonSmall4770) =
      mixedMoment B node1970 node1970Labels := by
    have ha : raw1707 = raw1708 := by apply Matrix.ext; unfold raw1707 raw1708; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4770 = raw1708Labels := by decide +kernel
    rw [ha, hj, canonical1708 B hB]
  have hc1 : mixedMoment B raw1707 (Fin.cases (1 : Fin 2) singletonSmall4770) =
      mixedMoment B node2186 node2186Labels := by
    have ha : raw1707 = raw1709 := by apply Matrix.ext; unfold raw1707 raw1709; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4770 = raw1709Labels := by decide +kernel
    rw [ha, hj, canonical1709 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4778 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4778 node4778Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1986 node1986Labels + mixedMoment B node1986 node1986Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1710 singletonSmall4778
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4778) = raw1710Labels := by decide +kernel
  rw [hl, canonical1710 B hB] at h
  have hc0 : mixedMoment B raw1710 (Fin.cases (0 : Fin 2) singletonSmall4778) =
      mixedMoment B node1986 node1986Labels := by
    have ha : raw1710 = raw1711 := by apply Matrix.ext; unfold raw1710 raw1711; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4778 = raw1711Labels := by decide +kernel
    rw [ha, hj, canonical1711 B hB]
  have hc1 : mixedMoment B raw1710 (Fin.cases (1 : Fin 2) singletonSmall4778) =
      mixedMoment B node1986 node1986Labels := by
    have ha : raw1710 = raw1712 := by apply Matrix.ext; unfold raw1710 raw1712; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4778 = raw1712Labels := by decide +kernel
    rw [ha, hj, canonical1712 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4779 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4779 node4779Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1987 node1987Labels + mixedMoment B node1996 node1996Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1713 singletonSmall4779
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4779) = raw1713Labels := by decide +kernel
  rw [hl, canonical1713 B hB] at h
  have hc0 : mixedMoment B raw1713 (Fin.cases (0 : Fin 2) singletonSmall4779) =
      mixedMoment B node1987 node1987Labels := by
    have ha : raw1713 = raw1714 := by apply Matrix.ext; unfold raw1713 raw1714; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4779 = raw1714Labels := by decide +kernel
    rw [ha, hj, canonical1714 B hB]
  have hc1 : mixedMoment B raw1713 (Fin.cases (1 : Fin 2) singletonSmall4779) =
      mixedMoment B node1996 node1996Labels := by
    have ha : raw1713 = raw1715 := by apply Matrix.ext; unfold raw1713 raw1715; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4779 = raw1715Labels := by decide +kernel
    rw [ha, hj, canonical1715 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4782 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4782 node4782Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1990 node1990Labels + mixedMoment B node1997 node1997Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1716 singletonSmall4782
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4782) = raw1716Labels := by decide +kernel
  rw [hl, canonical1716 B hB] at h
  have hc0 : mixedMoment B raw1716 (Fin.cases (0 : Fin 2) singletonSmall4782) =
      mixedMoment B node1990 node1990Labels := by
    have ha : raw1716 = raw1717 := by apply Matrix.ext; unfold raw1716 raw1717; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4782 = raw1717Labels := by decide +kernel
    rw [ha, hj, canonical1717 B hB]
  have hc1 : mixedMoment B raw1716 (Fin.cases (1 : Fin 2) singletonSmall4782) =
      mixedMoment B node1997 node1997Labels := by
    have ha : raw1716 = raw1718 := by apply Matrix.ext; unfold raw1716 raw1718; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4782 = raw1718Labels := by decide +kernel
    rw [ha, hj, canonical1718 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4787 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4787 node4787Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2000 node2000Labels + mixedMoment B node2000 node2000Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1719 singletonSmall4787
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4787) = raw1719Labels := by decide +kernel
  rw [hl, canonical1719 B hB] at h
  have hc0 : mixedMoment B raw1719 (Fin.cases (0 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1720 := by apply Matrix.ext; unfold raw1719 raw1720; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4787 = raw1720Labels := by decide +kernel
    rw [ha, hj, canonical1720 B hB]
  have hc1 : mixedMoment B raw1719 (Fin.cases (1 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1721 := by apply Matrix.ext; unfold raw1719 raw1721; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4787 = raw1721Labels := by decide +kernel
    rw [ha, hj, canonical1721 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4788 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4788 node4788Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2003 node2003Labels + mixedMoment B node2006 node2006Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1722 singletonSmall4788
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4788) = raw1722Labels := by decide +kernel
  rw [hl, canonical1722 B hB] at h
  have hc0 : mixedMoment B raw1722 (Fin.cases (0 : Fin 2) singletonSmall4788) =
      mixedMoment B node2003 node2003Labels := by
    have ha : raw1722 = raw1723 := by apply Matrix.ext; unfold raw1722 raw1723; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4788 = raw1723Labels := by decide +kernel
    rw [ha, hj, canonical1723 B hB]
  have hc1 : mixedMoment B raw1722 (Fin.cases (1 : Fin 2) singletonSmall4788) =
      mixedMoment B node2006 node2006Labels := by
    have ha : raw1722 = raw1724 := by apply Matrix.ext; unfold raw1722 raw1724; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4788 = raw1724Labels := by decide +kernel
    rw [ha, hj, canonical1724 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4798 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4798 node4798Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2016 node2016Labels + mixedMoment B node2075 node2075Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1725 singletonSmall4798
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4798) = raw1725Labels := by decide +kernel
  rw [hl, canonical1725 B hB] at h
  have hc0 : mixedMoment B raw1725 (Fin.cases (0 : Fin 2) singletonSmall4798) =
      mixedMoment B node2016 node2016Labels := by
    have ha : raw1725 = raw1726 := by apply Matrix.ext; unfold raw1725 raw1726; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4798 = raw1726Labels := by decide +kernel
    rw [ha, hj, canonical1726 B hB]
  have hc1 : mixedMoment B raw1725 (Fin.cases (1 : Fin 2) singletonSmall4798) =
      mixedMoment B node2075 node2075Labels := by
    have ha : raw1725 = raw1727 := by apply Matrix.ext; unfold raw1725 raw1727; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4798 = raw1727Labels := by decide +kernel
    rw [ha, hj, canonical1727 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

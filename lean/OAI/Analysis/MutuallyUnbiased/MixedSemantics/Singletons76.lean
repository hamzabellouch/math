import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical14

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4864 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4864 node4864Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2105 node2105Labels + mixedMoment B node2241 node2241Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1788 singletonSmall4864
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4864) = raw1788Labels := by decide +kernel
  rw [hl, canonical1788 B hB] at h
  have hc0 : mixedMoment B raw1788 (Fin.cases (0 : Fin 2) singletonSmall4864) =
      mixedMoment B node2105 node2105Labels := by
    have ha : raw1788 = raw1789 := by apply Matrix.ext; unfold raw1788 raw1789; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4864 = raw1789Labels := by decide +kernel
    rw [ha, hj, canonical1789 B hB]
  have hc1 : mixedMoment B raw1788 (Fin.cases (1 : Fin 2) singletonSmall4864) =
      mixedMoment B node2241 node2241Labels := by
    have ha : raw1788 = raw1790 := by apply Matrix.ext; unfold raw1788 raw1790; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4864 = raw1790Labels := by decide +kernel
    rw [ha, hj, canonical1790 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4865 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4865 node4865Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2106 node2106Labels + mixedMoment B node2242 node2242Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1791 singletonSmall4865
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4865) = raw1791Labels := by decide +kernel
  rw [hl, canonical1791 B hB] at h
  have hc0 : mixedMoment B raw1791 (Fin.cases (0 : Fin 2) singletonSmall4865) =
      mixedMoment B node2106 node2106Labels := by
    have ha : raw1791 = raw1792 := by apply Matrix.ext; unfold raw1791 raw1792; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4865 = raw1792Labels := by decide +kernel
    rw [ha, hj, canonical1792 B hB]
  have hc1 : mixedMoment B raw1791 (Fin.cases (1 : Fin 2) singletonSmall4865) =
      mixedMoment B node2242 node2242Labels := by
    have ha : raw1791 = raw1793 := by apply Matrix.ext; unfold raw1791 raw1793; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4865 = raw1793Labels := by decide +kernel
    rw [ha, hj, canonical1793 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4866 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4866 node4866Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2107 node2107Labels + mixedMoment B node2260 node2260Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1794 singletonSmall4866
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4866) = raw1794Labels := by decide +kernel
  rw [hl, canonical1794 B hB] at h
  have hc0 : mixedMoment B raw1794 (Fin.cases (0 : Fin 2) singletonSmall4866) =
      mixedMoment B node2107 node2107Labels := by
    have ha : raw1794 = raw1795 := by apply Matrix.ext; unfold raw1794 raw1795; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4866 = raw1795Labels := by decide +kernel
    rw [ha, hj, canonical1795 B hB]
  have hc1 : mixedMoment B raw1794 (Fin.cases (1 : Fin 2) singletonSmall4866) =
      mixedMoment B node2260 node2260Labels := by
    have ha : raw1794 = raw1796 := by apply Matrix.ext; unfold raw1794 raw1796; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4866 = raw1796Labels := by decide +kernel
    rw [ha, hj, canonical1796 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4868 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4868 node4868Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2109 node2109Labels + mixedMoment B node2261 node2261Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1797 singletonSmall4868
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4868) = raw1797Labels := by decide +kernel
  rw [hl, canonical1797 B hB] at h
  have hc0 : mixedMoment B raw1797 (Fin.cases (0 : Fin 2) singletonSmall4868) =
      mixedMoment B node2109 node2109Labels := by
    have ha : raw1797 = raw1798 := by apply Matrix.ext; unfold raw1797 raw1798; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4868 = raw1798Labels := by decide +kernel
    rw [ha, hj, canonical1798 B hB]
  have hc1 : mixedMoment B raw1797 (Fin.cases (1 : Fin 2) singletonSmall4868) =
      mixedMoment B node2261 node2261Labels := by
    have ha : raw1797 = raw1799 := by apply Matrix.ext; unfold raw1797 raw1799; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4868 = raw1799Labels := by decide +kernel
    rw [ha, hj, canonical1799 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4869 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4869 node4869Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2110 node2110Labels + mixedMoment B node2275 node2275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1800 singletonSmall4869
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4869) = raw1800Labels := by decide +kernel
  rw [hl, canonical1800 B hB] at h
  have hc0 : mixedMoment B raw1800 (Fin.cases (0 : Fin 2) singletonSmall4869) =
      mixedMoment B node2110 node2110Labels := by
    have ha : raw1800 = raw1801 := by apply Matrix.ext; unfold raw1800 raw1801; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4869 = raw1801Labels := by decide +kernel
    rw [ha, hj, canonical1801 B hB]
  have hc1 : mixedMoment B raw1800 (Fin.cases (1 : Fin 2) singletonSmall4869) =
      mixedMoment B node2275 node2275Labels := by
    have ha : raw1800 = raw1802 := by apply Matrix.ext; unfold raw1800 raw1802; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4869 = raw1802Labels := by decide +kernel
    rw [ha, hj, canonical1802 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4871 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4871 node4871Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2112 node2112Labels + mixedMoment B node2287 node2287Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1803 singletonSmall4871
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4871) = raw1803Labels := by decide +kernel
  rw [hl, canonical1803 B hB] at h
  have hc0 : mixedMoment B raw1803 (Fin.cases (0 : Fin 2) singletonSmall4871) =
      mixedMoment B node2112 node2112Labels := by
    have ha : raw1803 = raw1804 := by apply Matrix.ext; unfold raw1803 raw1804; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4871 = raw1804Labels := by decide +kernel
    rw [ha, hj, canonical1804 B hB]
  have hc1 : mixedMoment B raw1803 (Fin.cases (1 : Fin 2) singletonSmall4871) =
      mixedMoment B node2287 node2287Labels := by
    have ha : raw1803 = raw1805 := by apply Matrix.ext; unfold raw1803 raw1805; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4871 = raw1805Labels := by decide +kernel
    rw [ha, hj, canonical1805 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4874 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4874 node4874Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2115 node2115Labels + mixedMoment B node2276 node2276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1806 singletonSmall4874
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4874) = raw1806Labels := by decide +kernel
  rw [hl, canonical1806 B hB] at h
  have hc0 : mixedMoment B raw1806 (Fin.cases (0 : Fin 2) singletonSmall4874) =
      mixedMoment B node2115 node2115Labels := by
    have ha : raw1806 = raw1807 := by apply Matrix.ext; unfold raw1806 raw1807; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4874 = raw1807Labels := by decide +kernel
    rw [ha, hj, canonical1807 B hB]
  have hc1 : mixedMoment B raw1806 (Fin.cases (1 : Fin 2) singletonSmall4874) =
      mixedMoment B node2276 node2276Labels := by
    have ha : raw1806 = raw1808 := by apply Matrix.ext; unfold raw1806 raw1808; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4874 = raw1808Labels := by decide +kernel
    rw [ha, hj, canonical1808 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4875 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4875 node4875Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2116 node2116Labels + mixedMoment B node2288 node2288Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1809 singletonSmall4875
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4875) = raw1809Labels := by decide +kernel
  rw [hl, canonical1809 B hB] at h
  have hc0 : mixedMoment B raw1809 (Fin.cases (0 : Fin 2) singletonSmall4875) =
      mixedMoment B node2116 node2116Labels := by
    have ha : raw1809 = raw1810 := by apply Matrix.ext; unfold raw1809 raw1810; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4875 = raw1810Labels := by decide +kernel
    rw [ha, hj, canonical1810 B hB]
  have hc1 : mixedMoment B raw1809 (Fin.cases (1 : Fin 2) singletonSmall4875) =
      mixedMoment B node2288 node2288Labels := by
    have ha : raw1809 = raw1811 := by apply Matrix.ext; unfold raw1809 raw1811; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4875 = raw1811Labels := by decide +kernel
    rw [ha, hj, canonical1811 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4887 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4887 node4887Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2243 node2243Labels + mixedMoment B node2243 node2243Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1812 singletonSmall4887
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4887) = raw1812Labels := by decide +kernel
  rw [hl, canonical1812 B hB] at h
  have hc0 : mixedMoment B raw1812 (Fin.cases (0 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1813 := by apply Matrix.ext; unfold raw1812 raw1813; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4887 = raw1813Labels := by decide +kernel
    rw [ha, hj, canonical1813 B hB]
  have hc1 : mixedMoment B raw1812 (Fin.cases (1 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1814 := by apply Matrix.ext; unfold raw1812 raw1814; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4887 = raw1814Labels := by decide +kernel
    rw [ha, hj, canonical1814 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4888 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4888 node4888Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2244 node2244Labels + mixedMoment B node2262 node2262Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1815 singletonSmall4888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4888) = raw1815Labels := by decide +kernel
  rw [hl, canonical1815 B hB] at h
  have hc0 : mixedMoment B raw1815 (Fin.cases (0 : Fin 2) singletonSmall4888) =
      mixedMoment B node2244 node2244Labels := by
    have ha : raw1815 = raw1816 := by apply Matrix.ext; unfold raw1815 raw1816; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4888 = raw1816Labels := by decide +kernel
    rw [ha, hj, canonical1816 B hB]
  have hc1 : mixedMoment B raw1815 (Fin.cases (1 : Fin 2) singletonSmall4888) =
      mixedMoment B node2262 node2262Labels := by
    have ha : raw1815 = raw1817 := by apply Matrix.ext; unfold raw1815 raw1817; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4888 = raw1817Labels := by decide +kernel
    rw [ha, hj, canonical1817 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4889 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4889 node4889Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2245 node2245Labels + mixedMoment B node2277 node2277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1818 singletonSmall4889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4889) = raw1818Labels := by decide +kernel
  rw [hl, canonical1818 B hB] at h
  have hc0 : mixedMoment B raw1818 (Fin.cases (0 : Fin 2) singletonSmall4889) =
      mixedMoment B node2245 node2245Labels := by
    have ha : raw1818 = raw1819 := by apply Matrix.ext; unfold raw1818 raw1819; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4889 = raw1819Labels := by decide +kernel
    rw [ha, hj, canonical1819 B hB]
  have hc1 : mixedMoment B raw1818 (Fin.cases (1 : Fin 2) singletonSmall4889) =
      mixedMoment B node2277 node2277Labels := by
    have ha : raw1818 = raw1820 := by apply Matrix.ext; unfold raw1818 raw1820; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4889 = raw1820Labels := by decide +kernel
    rw [ha, hj, canonical1820 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4890 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4890 node4890Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2247 node2247Labels + mixedMoment B node2290 node2290Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1821 singletonSmall4890
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4890) = raw1821Labels := by decide +kernel
  rw [hl, canonical1821 B hB] at h
  have hc0 : mixedMoment B raw1821 (Fin.cases (0 : Fin 2) singletonSmall4890) =
      mixedMoment B node2247 node2247Labels := by
    have ha : raw1821 = raw1822 := by apply Matrix.ext; unfold raw1821 raw1822; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4890 = raw1822Labels := by decide +kernel
    rw [ha, hj, canonical1822 B hB]
  have hc1 : mixedMoment B raw1821 (Fin.cases (1 : Fin 2) singletonSmall4890) =
      mixedMoment B node2290 node2290Labels := by
    have ha : raw1821 = raw1823 := by apply Matrix.ext; unfold raw1821 raw1823; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4890 = raw1823Labels := by decide +kernel
    rw [ha, hj, canonical1823 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4896 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4896 node4896Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2266 node2266Labels + mixedMoment B node2278 node2278Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1824 singletonSmall4896
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4896) = raw1824Labels := by decide +kernel
  rw [hl, canonical1824 B hB] at h
  have hc0 : mixedMoment B raw1824 (Fin.cases (0 : Fin 2) singletonSmall4896) =
      mixedMoment B node2266 node2266Labels := by
    have ha : raw1824 = raw1825 := by apply Matrix.ext; unfold raw1824 raw1825; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4896 = raw1825Labels := by decide +kernel
    rw [ha, hj, canonical1825 B hB]
  have hc1 : mixedMoment B raw1824 (Fin.cases (1 : Fin 2) singletonSmall4896) =
      mixedMoment B node2278 node2278Labels := by
    have ha : raw1824 = raw1826 := by apply Matrix.ext; unfold raw1824 raw1826; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4896 = raw1826Labels := by decide +kernel
    rw [ha, hj, canonical1826 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4898 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4898 node4898Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2279 node2279Labels + mixedMoment B node2279 node2279Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1827 singletonSmall4898
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4898) = raw1827Labels := by decide +kernel
  rw [hl, canonical1827 B hB] at h
  have hc0 : mixedMoment B raw1827 (Fin.cases (0 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1828 := by apply Matrix.ext; unfold raw1827 raw1828; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4898 = raw1828Labels := by decide +kernel
    rw [ha, hj, canonical1828 B hB]
  have hc1 : mixedMoment B raw1827 (Fin.cases (1 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1829 := by apply Matrix.ext; unfold raw1827 raw1829; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4898 = raw1829Labels := by decide +kernel
    rw [ha, hj, canonical1829 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4899 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4899 node4899Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2281 node2281Labels + mixedMoment B node2294 node2294Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1830 singletonSmall4899
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4899) = raw1830Labels := by decide +kernel
  rw [hl, canonical1830 B hB] at h
  have hc0 : mixedMoment B raw1830 (Fin.cases (0 : Fin 2) singletonSmall4899) =
      mixedMoment B node2281 node2281Labels := by
    have ha : raw1830 = raw1831 := by apply Matrix.ext; unfold raw1830 raw1831; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4899 = raw1831Labels := by decide +kernel
    rw [ha, hj, canonical1831 B hB]
  have hc1 : mixedMoment B raw1830 (Fin.cases (1 : Fin 2) singletonSmall4899) =
      mixedMoment B node2294 node2294Labels := by
    have ha : raw1830 = raw1832 := by apply Matrix.ext; unfold raw1830 raw1832; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4899 = raw1832Labels := by decide +kernel
    rw [ha, hj, canonical1832 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4902 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4902 node4902Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2295 node2295Labels + mixedMoment B node3315 node3315Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1833 singletonSmall4902
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4902) = raw1833Labels := by decide +kernel
  rw [hl, canonical1833 B hB] at h
  have hc0 : mixedMoment B raw1833 (Fin.cases (0 : Fin 2) singletonSmall4902) =
      mixedMoment B node2295 node2295Labels := by
    have ha : raw1833 = raw1834 := by apply Matrix.ext; unfold raw1833 raw1834; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4902 = raw1834Labels := by decide +kernel
    rw [ha, hj, canonical1834 B hB]
  have hc1 : mixedMoment B raw1833 (Fin.cases (1 : Fin 2) singletonSmall4902) =
      mixedMoment B node3315 node3315Labels := by
    have ha : raw1833 = raw1835 := by apply Matrix.ext; unfold raw1833 raw1835; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4902 = raw1835Labels := by decide +kernel
    rw [ha, hj, canonical1835 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4903 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4903 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4903 node4903Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2296 node2296Labels + mixedMoment B node3316 node3316Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1836 singletonSmall4903
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4903) = raw1836Labels := by decide +kernel
  rw [hl, canonical1836 B hB] at h
  have hc0 : mixedMoment B raw1836 (Fin.cases (0 : Fin 2) singletonSmall4903) =
      mixedMoment B node2296 node2296Labels := by
    have ha : raw1836 = raw1837 := by apply Matrix.ext; unfold raw1836 raw1837; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4903 = raw1837Labels := by decide +kernel
    rw [ha, hj, canonical1837 B hB]
  have hc1 : mixedMoment B raw1836 (Fin.cases (1 : Fin 2) singletonSmall4903) =
      mixedMoment B node3316 node3316Labels := by
    have ha : raw1836 = raw1838 := by apply Matrix.ext; unfold raw1836 raw1838; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4903 = raw1838Labels := by decide +kernel
    rw [ha, hj, canonical1838 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4904 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4904 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4904 node4904Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2297 node2297Labels + mixedMoment B node3323 node3323Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1839 singletonSmall4904
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4904) = raw1839Labels := by decide +kernel
  rw [hl, canonical1839 B hB] at h
  have hc0 : mixedMoment B raw1839 (Fin.cases (0 : Fin 2) singletonSmall4904) =
      mixedMoment B node2297 node2297Labels := by
    have ha : raw1839 = raw1840 := by apply Matrix.ext; unfold raw1839 raw1840; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4904 = raw1840Labels := by decide +kernel
    rw [ha, hj, canonical1840 B hB]
  have hc1 : mixedMoment B raw1839 (Fin.cases (1 : Fin 2) singletonSmall4904) =
      mixedMoment B node3323 node3323Labels := by
    have ha : raw1839 = raw1841 := by apply Matrix.ext; unfold raw1839 raw1841; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4904 = raw1841Labels := by decide +kernel
    rw [ha, hj, canonical1841 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4905 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4905 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4905 node4905Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2298 node2298Labels + mixedMoment B node3320 node3320Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1842 singletonSmall4905
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4905) = raw1842Labels := by decide +kernel
  rw [hl, canonical1842 B hB] at h
  have hc0 : mixedMoment B raw1842 (Fin.cases (0 : Fin 2) singletonSmall4905) =
      mixedMoment B node2298 node2298Labels := by
    have ha : raw1842 = raw1843 := by apply Matrix.ext; unfold raw1842 raw1843; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4905 = raw1843Labels := by decide +kernel
    rw [ha, hj, canonical1843 B hB]
  have hc1 : mixedMoment B raw1842 (Fin.cases (1 : Fin 2) singletonSmall4905) =
      mixedMoment B node3320 node3320Labels := by
    have ha : raw1842 = raw1844 := by apply Matrix.ext; unfold raw1842 raw1844; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4905 = raw1844Labels := by decide +kernel
    rw [ha, hj, canonical1844 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4906 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4906 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4906 node4906Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2299 node2299Labels + mixedMoment B node3324 node3324Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1845 singletonSmall4906
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4906) = raw1845Labels := by decide +kernel
  rw [hl, canonical1845 B hB] at h
  have hc0 : mixedMoment B raw1845 (Fin.cases (0 : Fin 2) singletonSmall4906) =
      mixedMoment B node2299 node2299Labels := by
    have ha : raw1845 = raw1846 := by apply Matrix.ext; unfold raw1845 raw1846; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4906 = raw1846Labels := by decide +kernel
    rw [ha, hj, canonical1846 B hB]
  have hc1 : mixedMoment B raw1845 (Fin.cases (1 : Fin 2) singletonSmall4906) =
      mixedMoment B node3324 node3324Labels := by
    have ha : raw1845 = raw1847 := by apply Matrix.ext; unfold raw1845 raw1847; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4906 = raw1847Labels := by decide +kernel
    rw [ha, hj, canonical1847 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4907 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4907 node4907Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2300 node2300Labels + mixedMoment B node3325 node3325Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1848 singletonSmall4907
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4907) = raw1848Labels := by decide +kernel
  rw [hl, canonical1848 B hB] at h
  have hc0 : mixedMoment B raw1848 (Fin.cases (0 : Fin 2) singletonSmall4907) =
      mixedMoment B node2300 node2300Labels := by
    have ha : raw1848 = raw1849 := by apply Matrix.ext; unfold raw1848 raw1849; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4907 = raw1849Labels := by decide +kernel
    rw [ha, hj, canonical1849 B hB]
  have hc1 : mixedMoment B raw1848 (Fin.cases (1 : Fin 2) singletonSmall4907) =
      mixedMoment B node3325 node3325Labels := by
    have ha : raw1848 = raw1850 := by apply Matrix.ext; unfold raw1848 raw1850; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4907 = raw1850Labels := by decide +kernel
    rw [ha, hj, canonical1850 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4908 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4908 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4908 node4908Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2301 node2301Labels + mixedMoment B node3326 node3326Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1851 singletonSmall4908
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4908) = raw1851Labels := by decide +kernel
  rw [hl, canonical1851 B hB] at h
  have hc0 : mixedMoment B raw1851 (Fin.cases (0 : Fin 2) singletonSmall4908) =
      mixedMoment B node2301 node2301Labels := by
    have ha : raw1851 = raw1852 := by apply Matrix.ext; unfold raw1851 raw1852; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4908 = raw1852Labels := by decide +kernel
    rw [ha, hj, canonical1852 B hB]
  have hc1 : mixedMoment B raw1851 (Fin.cases (1 : Fin 2) singletonSmall4908) =
      mixedMoment B node3326 node3326Labels := by
    have ha : raw1851 = raw1853 := by apply Matrix.ext; unfold raw1851 raw1853; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4908 = raw1853Labels := by decide +kernel
    rw [ha, hj, canonical1853 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4909 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4909 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4909 node4909Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2302 node2302Labels + mixedMoment B node2448 node2448Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1854 singletonSmall4909
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4909) = raw1854Labels := by decide +kernel
  rw [hl, canonical1854 B hB] at h
  have hc0 : mixedMoment B raw1854 (Fin.cases (0 : Fin 2) singletonSmall4909) =
      mixedMoment B node2302 node2302Labels := by
    have ha : raw1854 = raw1855 := by apply Matrix.ext; unfold raw1854 raw1855; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4909 = raw1855Labels := by decide +kernel
    rw [ha, hj, canonical1855 B hB]
  have hc1 : mixedMoment B raw1854 (Fin.cases (1 : Fin 2) singletonSmall4909) =
      mixedMoment B node2448 node2448Labels := by
    have ha : raw1854 = raw1856 := by apply Matrix.ext; unfold raw1854 raw1856; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4909 = raw1856Labels := by decide +kernel
    rw [ha, hj, canonical1856 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4910 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4910 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4910 node4910Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2303 node2303Labels + mixedMoment B node3314 node3314Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1857 singletonSmall4910
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4910) = raw1857Labels := by decide +kernel
  rw [hl, canonical1857 B hB] at h
  have hc0 : mixedMoment B raw1857 (Fin.cases (0 : Fin 2) singletonSmall4910) =
      mixedMoment B node2303 node2303Labels := by
    have ha : raw1857 = raw1858 := by apply Matrix.ext; unfold raw1857 raw1858; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4910 = raw1858Labels := by decide +kernel
    rw [ha, hj, canonical1858 B hB]
  have hc1 : mixedMoment B raw1857 (Fin.cases (1 : Fin 2) singletonSmall4910) =
      mixedMoment B node3314 node3314Labels := by
    have ha : raw1857 = raw1859 := by apply Matrix.ext; unfold raw1857 raw1859; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4910 = raw1859Labels := by decide +kernel
    rw [ha, hj, canonical1859 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4912 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4912 node4912Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2305 node2305Labels + mixedMoment B node3317 node3317Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1860 singletonSmall4912
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4912) = raw1860Labels := by decide +kernel
  rw [hl, canonical1860 B hB] at h
  have hc0 : mixedMoment B raw1860 (Fin.cases (0 : Fin 2) singletonSmall4912) =
      mixedMoment B node2305 node2305Labels := by
    have ha : raw1860 = raw1861 := by apply Matrix.ext; unfold raw1860 raw1861; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4912 = raw1861Labels := by decide +kernel
    rw [ha, hj, canonical1861 B hB]
  have hc1 : mixedMoment B raw1860 (Fin.cases (1 : Fin 2) singletonSmall4912) =
      mixedMoment B node3317 node3317Labels := by
    have ha : raw1860 = raw1862 := by apply Matrix.ext; unfold raw1860 raw1862; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4912 = raw1862Labels := by decide +kernel
    rw [ha, hj, canonical1862 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4913 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4913 node4913Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2306 node2306Labels + mixedMoment B node3318 node3318Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1863 singletonSmall4913
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4913) = raw1863Labels := by decide +kernel
  rw [hl, canonical1863 B hB] at h
  have hc0 : mixedMoment B raw1863 (Fin.cases (0 : Fin 2) singletonSmall4913) =
      mixedMoment B node2306 node2306Labels := by
    have ha : raw1863 = raw1864 := by apply Matrix.ext; unfold raw1863 raw1864; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4913 = raw1864Labels := by decide +kernel
    rw [ha, hj, canonical1864 B hB]
  have hc1 : mixedMoment B raw1863 (Fin.cases (1 : Fin 2) singletonSmall4913) =
      mixedMoment B node3318 node3318Labels := by
    have ha : raw1863 = raw1865 := by apply Matrix.ext; unfold raw1863 raw1865; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4913 = raw1865Labels := by decide +kernel
    rw [ha, hj, canonical1865 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4914 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4914 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4914 node4914Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2307 node2307Labels + mixedMoment B node2376 node2376Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1866 singletonSmall4914
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4914) = raw1866Labels := by decide +kernel
  rw [hl, canonical1866 B hB] at h
  have hc0 : mixedMoment B raw1866 (Fin.cases (0 : Fin 2) singletonSmall4914) =
      mixedMoment B node2307 node2307Labels := by
    have ha : raw1866 = raw1867 := by apply Matrix.ext; unfold raw1866 raw1867; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4914 = raw1867Labels := by decide +kernel
    rw [ha, hj, canonical1867 B hB]
  have hc1 : mixedMoment B raw1866 (Fin.cases (1 : Fin 2) singletonSmall4914) =
      mixedMoment B node2376 node2376Labels := by
    have ha : raw1866 = raw1868 := by apply Matrix.ext; unfold raw1866 raw1868; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4914 = raw1868Labels := by decide +kernel
    rw [ha, hj, canonical1868 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4917 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4917 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4917 node4917Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2308 node2308Labels + mixedMoment B node3321 node3321Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1869 singletonSmall4917
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4917) = raw1869Labels := by decide +kernel
  rw [hl, canonical1869 B hB] at h
  have hc0 : mixedMoment B raw1869 (Fin.cases (0 : Fin 2) singletonSmall4917) =
      mixedMoment B node2308 node2308Labels := by
    have ha : raw1869 = raw1870 := by apply Matrix.ext; unfold raw1869 raw1870; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4917 = raw1870Labels := by decide +kernel
    rw [ha, hj, canonical1870 B hB]
  have hc1 : mixedMoment B raw1869 (Fin.cases (1 : Fin 2) singletonSmall4917) =
      mixedMoment B node3321 node3321Labels := by
    have ha : raw1869 = raw1871 := by apply Matrix.ext; unfold raw1869 raw1871; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4917 = raw1871Labels := by decide +kernel
    rw [ha, hj, canonical1871 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4919 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4919 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4919 node4919Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2310 node2310Labels + mixedMoment B node3329 node3329Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1872 singletonSmall4919
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4919) = raw1872Labels := by decide +kernel
  rw [hl, canonical1872 B hB] at h
  have hc0 : mixedMoment B raw1872 (Fin.cases (0 : Fin 2) singletonSmall4919) =
      mixedMoment B node2310 node2310Labels := by
    have ha : raw1872 = raw1873 := by apply Matrix.ext; unfold raw1872 raw1873; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4919 = raw1873Labels := by decide +kernel
    rw [ha, hj, canonical1873 B hB]
  have hc1 : mixedMoment B raw1872 (Fin.cases (1 : Fin 2) singletonSmall4919) =
      mixedMoment B node3329 node3329Labels := by
    have ha : raw1872 = raw1874 := by apply Matrix.ext; unfold raw1872 raw1874; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4919 = raw1874Labels := by decide +kernel
    rw [ha, hj, canonical1874 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4920 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4920 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4920 node4920Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2311 node2311Labels + mixedMoment B node2447 node2447Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1875 singletonSmall4920
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4920) = raw1875Labels := by decide +kernel
  rw [hl, canonical1875 B hB] at h
  have hc0 : mixedMoment B raw1875 (Fin.cases (0 : Fin 2) singletonSmall4920) =
      mixedMoment B node2311 node2311Labels := by
    have ha : raw1875 = raw1876 := by apply Matrix.ext; unfold raw1875 raw1876; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4920 = raw1876Labels := by decide +kernel
    rw [ha, hj, canonical1876 B hB]
  have hc1 : mixedMoment B raw1875 (Fin.cases (1 : Fin 2) singletonSmall4920) =
      mixedMoment B node2447 node2447Labels := by
    have ha : raw1875 = raw1877 := by apply Matrix.ext; unfold raw1875 raw1877; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4920 = raw1877Labels := by decide +kernel
    rw [ha, hj, canonical1877 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4922 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4922 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4922 node4922Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2313 node2313Labels + mixedMoment B node3322 node3322Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1878 singletonSmall4922
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4922) = raw1878Labels := by decide +kernel
  rw [hl, canonical1878 B hB] at h
  have hc0 : mixedMoment B raw1878 (Fin.cases (0 : Fin 2) singletonSmall4922) =
      mixedMoment B node2313 node2313Labels := by
    have ha : raw1878 = raw1879 := by apply Matrix.ext; unfold raw1878 raw1879; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4922 = raw1879Labels := by decide +kernel
    rw [ha, hj, canonical1879 B hB]
  have hc1 : mixedMoment B raw1878 (Fin.cases (1 : Fin 2) singletonSmall4922) =
      mixedMoment B node3322 node3322Labels := by
    have ha : raw1878 = raw1880 := by apply Matrix.ext; unfold raw1878 raw1880; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4922 = raw1880Labels := by decide +kernel
    rw [ha, hj, canonical1880 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4923 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4923 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4923 node4923Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2314 node2314Labels + mixedMoment B node3330 node3330Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1881 singletonSmall4923
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4923) = raw1881Labels := by decide +kernel
  rw [hl, canonical1881 B hB] at h
  have hc0 : mixedMoment B raw1881 (Fin.cases (0 : Fin 2) singletonSmall4923) =
      mixedMoment B node2314 node2314Labels := by
    have ha : raw1881 = raw1882 := by apply Matrix.ext; unfold raw1881 raw1882; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4923 = raw1882Labels := by decide +kernel
    rw [ha, hj, canonical1882 B hB]
  have hc1 : mixedMoment B raw1881 (Fin.cases (1 : Fin 2) singletonSmall4923) =
      mixedMoment B node3330 node3330Labels := by
    have ha : raw1881 = raw1883 := by apply Matrix.ext; unfold raw1881 raw1883; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4923 = raw1883Labels := by decide +kernel
    rw [ha, hj, canonical1883 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4925 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4925 node4925Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2315 node2315Labels + mixedMoment B node2369 node2369Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1884 singletonSmall4925
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4925) = raw1884Labels := by decide +kernel
  rw [hl, canonical1884 B hB] at h
  have hc0 : mixedMoment B raw1884 (Fin.cases (0 : Fin 2) singletonSmall4925) =
      mixedMoment B node2315 node2315Labels := by
    have ha : raw1884 = raw1885 := by apply Matrix.ext; unfold raw1884 raw1885; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4925 = raw1885Labels := by decide +kernel
    rw [ha, hj, canonical1885 B hB]
  have hc1 : mixedMoment B raw1884 (Fin.cases (1 : Fin 2) singletonSmall4925) =
      mixedMoment B node2369 node2369Labels := by
    have ha : raw1884 = raw1886 := by apply Matrix.ext; unfold raw1884 raw1886; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4925 = raw1886Labels := by decide +kernel
    rw [ha, hj, canonical1886 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4926 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4926 node4926Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2316 node2316Labels + mixedMoment B node3398 node3398Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1887 singletonSmall4926
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4926) = raw1887Labels := by decide +kernel
  rw [hl, canonical1887 B hB] at h
  have hc0 : mixedMoment B raw1887 (Fin.cases (0 : Fin 2) singletonSmall4926) =
      mixedMoment B node2316 node2316Labels := by
    have ha : raw1887 = raw1888 := by apply Matrix.ext; unfold raw1887 raw1888; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4926 = raw1888Labels := by decide +kernel
    rw [ha, hj, canonical1888 B hB]
  have hc1 : mixedMoment B raw1887 (Fin.cases (1 : Fin 2) singletonSmall4926) =
      mixedMoment B node3398 node3398Labels := by
    have ha : raw1887 = raw1889 := by apply Matrix.ext; unfold raw1887 raw1889; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4926 = raw1889Labels := by decide +kernel
    rw [ha, hj, canonical1889 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4927 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4927 node4927Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2317 node2317Labels + mixedMoment B node3399 node3399Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1890 singletonSmall4927
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4927) = raw1890Labels := by decide +kernel
  rw [hl, canonical1890 B hB] at h
  have hc0 : mixedMoment B raw1890 (Fin.cases (0 : Fin 2) singletonSmall4927) =
      mixedMoment B node2317 node2317Labels := by
    have ha : raw1890 = raw1891 := by apply Matrix.ext; unfold raw1890 raw1891; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4927 = raw1891Labels := by decide +kernel
    rw [ha, hj, canonical1891 B hB]
  have hc1 : mixedMoment B raw1890 (Fin.cases (1 : Fin 2) singletonSmall4927) =
      mixedMoment B node3399 node3399Labels := by
    have ha : raw1890 = raw1892 := by apply Matrix.ext; unfold raw1890 raw1892; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4927 = raw1892Labels := by decide +kernel
    rw [ha, hj, canonical1892 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical16

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4996 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4996 node4996Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2382 node2382Labels + mixedMoment B node3340 node3340Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2007 singletonSmall4996
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4996) = raw2007Labels := by decide +kernel
  rw [hl, canonical2007 B hB] at h
  have hc0 : mixedMoment B raw2007 (Fin.cases (0 : Fin 2) singletonSmall4996) =
      mixedMoment B node2382 node2382Labels := by
    have ha : raw2007 = raw2008 := by apply Matrix.ext; unfold raw2007 raw2008; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4996 = raw2008Labels := by decide +kernel
    rw [ha, hj, canonical2008 B hB]
  have hc1 : mixedMoment B raw2007 (Fin.cases (1 : Fin 2) singletonSmall4996) =
      mixedMoment B node3340 node3340Labels := by
    have ha : raw2007 = raw2009 := by apply Matrix.ext; unfold raw2007 raw2009; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4996 = raw2009Labels := by decide +kernel
    rw [ha, hj, canonical2009 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4998 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4998 node4998Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2383 node2383Labels + mixedMoment B node3352 node3352Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2010 singletonSmall4998
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4998) = raw2010Labels := by decide +kernel
  rw [hl, canonical2010 B hB] at h
  have hc0 : mixedMoment B raw2010 (Fin.cases (0 : Fin 2) singletonSmall4998) =
      mixedMoment B node2383 node2383Labels := by
    have ha : raw2010 = raw2011 := by apply Matrix.ext; unfold raw2010 raw2011; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4998 = raw2011Labels := by decide +kernel
    rw [ha, hj, canonical2011 B hB]
  have hc1 : mixedMoment B raw2010 (Fin.cases (1 : Fin 2) singletonSmall4998) =
      mixedMoment B node3352 node3352Labels := by
    have ha : raw2010 = raw2012 := by apply Matrix.ext; unfold raw2010 raw2012; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4998 = raw2012Labels := by decide +kernel
    rw [ha, hj, canonical2012 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5000 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5000 node5000Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2385 node2385Labels + mixedMoment B node3353 node3353Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2013 singletonSmall5000
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5000) = raw2013Labels := by decide +kernel
  rw [hl, canonical2013 B hB] at h
  have hc0 : mixedMoment B raw2013 (Fin.cases (0 : Fin 2) singletonSmall5000) =
      mixedMoment B node2385 node2385Labels := by
    have ha : raw2013 = raw2014 := by apply Matrix.ext; unfold raw2013 raw2014; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5000 = raw2014Labels := by decide +kernel
    rw [ha, hj, canonical2014 B hB]
  have hc1 : mixedMoment B raw2013 (Fin.cases (1 : Fin 2) singletonSmall5000) =
      mixedMoment B node3353 node3353Labels := by
    have ha : raw2013 = raw2015 := by apply Matrix.ext; unfold raw2013 raw2015; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5000 = raw2015Labels := by decide +kernel
    rw [ha, hj, canonical2015 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5003 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5003 node5003Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2388 node2388Labels + mixedMoment B node3354 node3354Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2016 singletonSmall5003
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5003) = raw2016Labels := by decide +kernel
  rw [hl, canonical2016 B hB] at h
  have hc0 : mixedMoment B raw2016 (Fin.cases (0 : Fin 2) singletonSmall5003) =
      mixedMoment B node2388 node2388Labels := by
    have ha : raw2016 = raw2017 := by apply Matrix.ext; unfold raw2016 raw2017; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5003 = raw2017Labels := by decide +kernel
    rw [ha, hj, canonical2017 B hB]
  have hc1 : mixedMoment B raw2016 (Fin.cases (1 : Fin 2) singletonSmall5003) =
      mixedMoment B node3354 node3354Labels := by
    have ha : raw2016 = raw2018 := by apply Matrix.ext; unfold raw2016 raw2018; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5003 = raw2018Labels := by decide +kernel
    rw [ha, hj, canonical2018 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5013 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5013 node5013Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2398 node2398Labels + mixedMoment B node3341 node3341Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2019 singletonSmall5013
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5013) = raw2019Labels := by decide +kernel
  rw [hl, canonical2019 B hB] at h
  have hc0 : mixedMoment B raw2019 (Fin.cases (0 : Fin 2) singletonSmall5013) =
      mixedMoment B node2398 node2398Labels := by
    have ha : raw2019 = raw2020 := by apply Matrix.ext; unfold raw2019 raw2020; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5013 = raw2020Labels := by decide +kernel
    rw [ha, hj, canonical2020 B hB]
  have hc1 : mixedMoment B raw2019 (Fin.cases (1 : Fin 2) singletonSmall5013) =
      mixedMoment B node3341 node3341Labels := by
    have ha : raw2019 = raw2021 := by apply Matrix.ext; unfold raw2019 raw2021; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5013 = raw2021Labels := by decide +kernel
    rw [ha, hj, canonical2021 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5014 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5014 node5014Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2399 node2399Labels + mixedMoment B node2467 node2467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2022 singletonSmall5014
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5014) = raw2022Labels := by decide +kernel
  rw [hl, canonical2022 B hB] at h
  have hc0 : mixedMoment B raw2022 (Fin.cases (0 : Fin 2) singletonSmall5014) =
      mixedMoment B node2399 node2399Labels := by
    have ha : raw2022 = raw2023 := by apply Matrix.ext; unfold raw2022 raw2023; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5014 = raw2023Labels := by decide +kernel
    rw [ha, hj, canonical2023 B hB]
  have hc1 : mixedMoment B raw2022 (Fin.cases (1 : Fin 2) singletonSmall5014) =
      mixedMoment B node2467 node2467Labels := by
    have ha : raw2022 = raw2024 := by apply Matrix.ext; unfold raw2022 raw2024; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5014 = raw2024Labels := by decide +kernel
    rw [ha, hj, canonical2024 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5015 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5015 node5015Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2400 node2400Labels + mixedMoment B node3344 node3344Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2025 singletonSmall5015
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5015) = raw2025Labels := by decide +kernel
  rw [hl, canonical2025 B hB] at h
  have hc0 : mixedMoment B raw2025 (Fin.cases (0 : Fin 2) singletonSmall5015) =
      mixedMoment B node2400 node2400Labels := by
    have ha : raw2025 = raw2026 := by apply Matrix.ext; unfold raw2025 raw2026; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5015 = raw2026Labels := by decide +kernel
    rw [ha, hj, canonical2026 B hB]
  have hc1 : mixedMoment B raw2025 (Fin.cases (1 : Fin 2) singletonSmall5015) =
      mixedMoment B node3344 node3344Labels := by
    have ha : raw2025 = raw2027 := by apply Matrix.ext; unfold raw2025 raw2027; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5015 = raw2027Labels := by decide +kernel
    rw [ha, hj, canonical2027 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5018 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5018 node5018Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2404 node2404Labels + mixedMoment B node3357 node3357Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2028 singletonSmall5018
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5018) = raw2028Labels := by decide +kernel
  rw [hl, canonical2028 B hB] at h
  have hc0 : mixedMoment B raw2028 (Fin.cases (0 : Fin 2) singletonSmall5018) =
      mixedMoment B node2404 node2404Labels := by
    have ha : raw2028 = raw2029 := by apply Matrix.ext; unfold raw2028 raw2029; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5018 = raw2029Labels := by decide +kernel
    rw [ha, hj, canonical2029 B hB]
  have hc1 : mixedMoment B raw2028 (Fin.cases (1 : Fin 2) singletonSmall5018) =
      mixedMoment B node3357 node3357Labels := by
    have ha : raw2028 = raw2030 := by apply Matrix.ext; unfold raw2028 raw2030; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5018 = raw2030Labels := by decide +kernel
    rw [ha, hj, canonical2030 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5021 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5021 node5021Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2407 node2407Labels + mixedMoment B node3360 node3360Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2031 singletonSmall5021
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5021) = raw2031Labels := by decide +kernel
  rw [hl, canonical2031 B hB] at h
  have hc0 : mixedMoment B raw2031 (Fin.cases (0 : Fin 2) singletonSmall5021) =
      mixedMoment B node2407 node2407Labels := by
    have ha : raw2031 = raw2032 := by apply Matrix.ext; unfold raw2031 raw2032; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5021 = raw2032Labels := by decide +kernel
    rw [ha, hj, canonical2032 B hB]
  have hc1 : mixedMoment B raw2031 (Fin.cases (1 : Fin 2) singletonSmall5021) =
      mixedMoment B node3360 node3360Labels := by
    have ha : raw2031 = raw2033 := by apply Matrix.ext; unfold raw2031 raw2033; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5021 = raw2033Labels := by decide +kernel
    rw [ha, hj, canonical2033 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5023 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5023 node5023Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2410 node2410Labels + mixedMoment B node2410 node2410Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2034 singletonSmall5023
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5023) = raw2034Labels := by decide +kernel
  rw [hl, canonical2034 B hB] at h
  have hc0 : mixedMoment B raw2034 (Fin.cases (0 : Fin 2) singletonSmall5023) =
      mixedMoment B node2410 node2410Labels := by
    have ha : raw2034 = raw2035 := by apply Matrix.ext; unfold raw2034 raw2035; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5023 = raw2035Labels := by decide +kernel
    rw [ha, hj, canonical2035 B hB]
  have hc1 : mixedMoment B raw2034 (Fin.cases (1 : Fin 2) singletonSmall5023) =
      mixedMoment B node2410 node2410Labels := by
    have ha : raw2034 = raw2036 := by apply Matrix.ext; unfold raw2034 raw2036; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5023 = raw2036Labels := by decide +kernel
    rw [ha, hj, canonical2036 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5027 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5027 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5027 node5027Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2416 node2416Labels + mixedMoment B node3427 node3427Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2037 singletonSmall5027
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5027) = raw2037Labels := by decide +kernel
  rw [hl, canonical2037 B hB] at h
  have hc0 : mixedMoment B raw2037 (Fin.cases (0 : Fin 2) singletonSmall5027) =
      mixedMoment B node2416 node2416Labels := by
    have ha : raw2037 = raw2038 := by apply Matrix.ext; unfold raw2037 raw2038; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5027 = raw2038Labels := by decide +kernel
    rw [ha, hj, canonical2038 B hB]
  have hc1 : mixedMoment B raw2037 (Fin.cases (1 : Fin 2) singletonSmall5027) =
      mixedMoment B node3427 node3427Labels := by
    have ha : raw2037 = raw2039 := by apply Matrix.ext; unfold raw2037 raw2039; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5027 = raw2039Labels := by decide +kernel
    rw [ha, hj, canonical2039 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5028 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5028 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5028 node5028Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2417 node2417Labels + mixedMoment B node2445 node2445Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2040 singletonSmall5028
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5028) = raw2040Labels := by decide +kernel
  rw [hl, canonical2040 B hB] at h
  have hc0 : mixedMoment B raw2040 (Fin.cases (0 : Fin 2) singletonSmall5028) =
      mixedMoment B node2417 node2417Labels := by
    have ha : raw2040 = raw2041 := by apply Matrix.ext; unfold raw2040 raw2041; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5028 = raw2041Labels := by decide +kernel
    rw [ha, hj, canonical2041 B hB]
  have hc1 : mixedMoment B raw2040 (Fin.cases (1 : Fin 2) singletonSmall5028) =
      mixedMoment B node2445 node2445Labels := by
    have ha : raw2040 = raw2042 := by apply Matrix.ext; unfold raw2040 raw2042; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5028 = raw2042Labels := by decide +kernel
    rw [ha, hj, canonical2042 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5030 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5030 node5030Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2419 node2419Labels + mixedMoment B node3425 node3425Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2043 singletonSmall5030
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5030) = raw2043Labels := by decide +kernel
  rw [hl, canonical2043 B hB] at h
  have hc0 : mixedMoment B raw2043 (Fin.cases (0 : Fin 2) singletonSmall5030) =
      mixedMoment B node2419 node2419Labels := by
    have ha : raw2043 = raw2044 := by apply Matrix.ext; unfold raw2043 raw2044; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5030 = raw2044Labels := by decide +kernel
    rw [ha, hj, canonical2044 B hB]
  have hc1 : mixedMoment B raw2043 (Fin.cases (1 : Fin 2) singletonSmall5030) =
      mixedMoment B node3425 node3425Labels := by
    have ha : raw2043 = raw2045 := by apply Matrix.ext; unfold raw2043 raw2045; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5030 = raw2045Labels := by decide +kernel
    rw [ha, hj, canonical2045 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5031 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5031 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5031 node5031Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2420 node2420Labels + mixedMoment B node3428 node3428Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2046 singletonSmall5031
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5031) = raw2046Labels := by decide +kernel
  rw [hl, canonical2046 B hB] at h
  have hc0 : mixedMoment B raw2046 (Fin.cases (0 : Fin 2) singletonSmall5031) =
      mixedMoment B node2420 node2420Labels := by
    have ha : raw2046 = raw2047 := by apply Matrix.ext; unfold raw2046 raw2047; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5031 = raw2047Labels := by decide +kernel
    rw [ha, hj, canonical2047 B hB]
  have hc1 : mixedMoment B raw2046 (Fin.cases (1 : Fin 2) singletonSmall5031) =
      mixedMoment B node3428 node3428Labels := by
    have ha : raw2046 = raw2048 := by apply Matrix.ext; unfold raw2046 raw2048; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5031 = raw2048Labels := by decide +kernel
    rw [ha, hj, canonical2048 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5032 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5032 node5032Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2424 node2424Labels + mixedMoment B node3440 node3440Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2049 singletonSmall5032
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5032) = raw2049Labels := by decide +kernel
  rw [hl, canonical2049 B hB] at h
  have hc0 : mixedMoment B raw2049 (Fin.cases (0 : Fin 2) singletonSmall5032) =
      mixedMoment B node2424 node2424Labels := by
    have ha : raw2049 = raw2050 := by apply Matrix.ext; unfold raw2049 raw2050; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5032 = raw2050Labels := by decide +kernel
    rw [ha, hj, canonical2050 B hB]
  have hc1 : mixedMoment B raw2049 (Fin.cases (1 : Fin 2) singletonSmall5032) =
      mixedMoment B node3440 node3440Labels := by
    have ha : raw2049 = raw2051 := by apply Matrix.ext; unfold raw2049 raw2051; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5032 = raw2051Labels := by decide +kernel
    rw [ha, hj, canonical2051 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5033 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5033 node5033Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2425 node2425Labels + mixedMoment B node3449 node3449Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2052 singletonSmall5033
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5033) = raw2052Labels := by decide +kernel
  rw [hl, canonical2052 B hB] at h
  have hc0 : mixedMoment B raw2052 (Fin.cases (0 : Fin 2) singletonSmall5033) =
      mixedMoment B node2425 node2425Labels := by
    have ha : raw2052 = raw2053 := by apply Matrix.ext; unfold raw2052 raw2053; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5033 = raw2053Labels := by decide +kernel
    rw [ha, hj, canonical2053 B hB]
  have hc1 : mixedMoment B raw2052 (Fin.cases (1 : Fin 2) singletonSmall5033) =
      mixedMoment B node3449 node3449Labels := by
    have ha : raw2052 = raw2054 := by apply Matrix.ext; unfold raw2052 raw2054; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5033 = raw2054Labels := by decide +kernel
    rw [ha, hj, canonical2054 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5036 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5036 node5036Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2428 node2428Labels + mixedMoment B node3450 node3450Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2055 singletonSmall5036
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5036) = raw2055Labels := by decide +kernel
  rw [hl, canonical2055 B hB] at h
  have hc0 : mixedMoment B raw2055 (Fin.cases (0 : Fin 2) singletonSmall5036) =
      mixedMoment B node2428 node2428Labels := by
    have ha : raw2055 = raw2056 := by apply Matrix.ext; unfold raw2055 raw2056; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5036 = raw2056Labels := by decide +kernel
    rw [ha, hj, canonical2056 B hB]
  have hc1 : mixedMoment B raw2055 (Fin.cases (1 : Fin 2) singletonSmall5036) =
      mixedMoment B node3450 node3450Labels := by
    have ha : raw2055 = raw2057 := by apply Matrix.ext; unfold raw2055 raw2057; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5036 = raw2057Labels := by decide +kernel
    rw [ha, hj, canonical2057 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5037 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5037 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5037 node5037Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2429 node2429Labels + mixedMoment B node3455 node3455Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2058 singletonSmall5037
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5037) = raw2058Labels := by decide +kernel
  rw [hl, canonical2058 B hB] at h
  have hc0 : mixedMoment B raw2058 (Fin.cases (0 : Fin 2) singletonSmall5037) =
      mixedMoment B node2429 node2429Labels := by
    have ha : raw2058 = raw2059 := by apply Matrix.ext; unfold raw2058 raw2059; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5037 = raw2059Labels := by decide +kernel
    rw [ha, hj, canonical2059 B hB]
  have hc1 : mixedMoment B raw2058 (Fin.cases (1 : Fin 2) singletonSmall5037) =
      mixedMoment B node3455 node3455Labels := by
    have ha : raw2058 = raw2060 := by apply Matrix.ext; unfold raw2058 raw2060; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5037 = raw2060Labels := by decide +kernel
    rw [ha, hj, canonical2060 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5038 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5038 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5038 node5038Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2431 node2431Labels + mixedMoment B node3453 node3453Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2061 singletonSmall5038
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5038) = raw2061Labels := by decide +kernel
  rw [hl, canonical2061 B hB] at h
  have hc0 : mixedMoment B raw2061 (Fin.cases (0 : Fin 2) singletonSmall5038) =
      mixedMoment B node2431 node2431Labels := by
    have ha : raw2061 = raw2062 := by apply Matrix.ext; unfold raw2061 raw2062; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5038 = raw2062Labels := by decide +kernel
    rw [ha, hj, canonical2062 B hB]
  have hc1 : mixedMoment B raw2061 (Fin.cases (1 : Fin 2) singletonSmall5038) =
      mixedMoment B node3453 node3453Labels := by
    have ha : raw2061 = raw2063 := by apply Matrix.ext; unfold raw2061 raw2063; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5038 = raw2063Labels := by decide +kernel
    rw [ha, hj, canonical2063 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5039 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5039 node5039Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2432 node2432Labels + mixedMoment B node3456 node3456Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2064 singletonSmall5039
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5039) = raw2064Labels := by decide +kernel
  rw [hl, canonical2064 B hB] at h
  have hc0 : mixedMoment B raw2064 (Fin.cases (0 : Fin 2) singletonSmall5039) =
      mixedMoment B node2432 node2432Labels := by
    have ha : raw2064 = raw2065 := by apply Matrix.ext; unfold raw2064 raw2065; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5039 = raw2065Labels := by decide +kernel
    rw [ha, hj, canonical2065 B hB]
  have hc1 : mixedMoment B raw2064 (Fin.cases (1 : Fin 2) singletonSmall5039) =
      mixedMoment B node3456 node3456Labels := by
    have ha : raw2064 = raw2066 := by apply Matrix.ext; unfold raw2064 raw2066; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5039 = raw2066Labels := by decide +kernel
    rw [ha, hj, canonical2066 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5045 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5045 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5045 node5045Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2444 node2444Labels + mixedMoment B node3362 node3362Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2067 singletonSmall5045
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5045) = raw2067Labels := by decide +kernel
  rw [hl, canonical2067 B hB] at h
  have hc0 : mixedMoment B raw2067 (Fin.cases (0 : Fin 2) singletonSmall5045) =
      mixedMoment B node2444 node2444Labels := by
    have ha : raw2067 = raw2068 := by apply Matrix.ext; unfold raw2067 raw2068; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5045 = raw2068Labels := by decide +kernel
    rw [ha, hj, canonical2068 B hB]
  have hc1 : mixedMoment B raw2067 (Fin.cases (1 : Fin 2) singletonSmall5045) =
      mixedMoment B node3362 node3362Labels := by
    have ha : raw2067 = raw2069 := by apply Matrix.ext; unfold raw2067 raw2069; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5045 = raw2069Labels := by decide +kernel
    rw [ha, hj, canonical2069 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5046 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5046 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5046 node5046Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2446 node2446Labels + mixedMoment B node3363 node3363Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2070 singletonSmall5046
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5046) = raw2070Labels := by decide +kernel
  rw [hl, canonical2070 B hB] at h
  have hc0 : mixedMoment B raw2070 (Fin.cases (0 : Fin 2) singletonSmall5046) =
      mixedMoment B node2446 node2446Labels := by
    have ha : raw2070 = raw2071 := by apply Matrix.ext; unfold raw2070 raw2071; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5046 = raw2071Labels := by decide +kernel
    rw [ha, hj, canonical2071 B hB]
  have hc1 : mixedMoment B raw2070 (Fin.cases (1 : Fin 2) singletonSmall5046) =
      mixedMoment B node3363 node3363Labels := by
    have ha : raw2070 = raw2072 := by apply Matrix.ext; unfold raw2070 raw2072; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5046 = raw2072Labels := by decide +kernel
    rw [ha, hj, canonical2072 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5047 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5047 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5047 node5047Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2449 node2449Labels + mixedMoment B node3432 node3432Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2073 singletonSmall5047
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5047) = raw2073Labels := by decide +kernel
  rw [hl, canonical2073 B hB] at h
  have hc0 : mixedMoment B raw2073 (Fin.cases (0 : Fin 2) singletonSmall5047) =
      mixedMoment B node2449 node2449Labels := by
    have ha : raw2073 = raw2074 := by apply Matrix.ext; unfold raw2073 raw2074; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5047 = raw2074Labels := by decide +kernel
    rw [ha, hj, canonical2074 B hB]
  have hc1 : mixedMoment B raw2073 (Fin.cases (1 : Fin 2) singletonSmall5047) =
      mixedMoment B node3432 node3432Labels := by
    have ha : raw2073 = raw2075 := by apply Matrix.ext; unfold raw2073 raw2075; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5047 = raw2075Labels := by decide +kernel
    rw [ha, hj, canonical2075 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5050 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5050 node5050Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2452 node2452Labels + mixedMoment B node3433 node3433Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2076 singletonSmall5050
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5050) = raw2076Labels := by decide +kernel
  rw [hl, canonical2076 B hB] at h
  have hc0 : mixedMoment B raw2076 (Fin.cases (0 : Fin 2) singletonSmall5050) =
      mixedMoment B node2452 node2452Labels := by
    have ha : raw2076 = raw2077 := by apply Matrix.ext; unfold raw2076 raw2077; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5050 = raw2077Labels := by decide +kernel
    rw [ha, hj, canonical2077 B hB]
  have hc1 : mixedMoment B raw2076 (Fin.cases (1 : Fin 2) singletonSmall5050) =
      mixedMoment B node3433 node3433Labels := by
    have ha : raw2076 = raw2078 := by apply Matrix.ext; unfold raw2076 raw2078; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5050 = raw2078Labels := by decide +kernel
    rw [ha, hj, canonical2078 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5055 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5055 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5055 node5055Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2458 node2458Labels + mixedMoment B node2458 node2458Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2079 singletonSmall5055
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5055) = raw2079Labels := by decide +kernel
  rw [hl, canonical2079 B hB] at h
  have hc0 : mixedMoment B raw2079 (Fin.cases (0 : Fin 2) singletonSmall5055) =
      mixedMoment B node2458 node2458Labels := by
    have ha : raw2079 = raw2080 := by apply Matrix.ext; unfold raw2079 raw2080; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5055 = raw2080Labels := by decide +kernel
    rw [ha, hj, canonical2080 B hB]
  have hc1 : mixedMoment B raw2079 (Fin.cases (1 : Fin 2) singletonSmall5055) =
      mixedMoment B node2458 node2458Labels := by
    have ha : raw2079 = raw2081 := by apply Matrix.ext; unfold raw2079 raw2081; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5055 = raw2081Labels := by decide +kernel
    rw [ha, hj, canonical2081 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

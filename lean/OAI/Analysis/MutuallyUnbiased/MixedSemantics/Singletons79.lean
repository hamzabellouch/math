import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical16

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5056 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5056 node5056Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2459 node2459Labels + mixedMoment B node3429 node3429Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2082 singletonSmall5056
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5056) = raw2082Labels := by decide +kernel
  rw [hl, canonical2082 B hB] at h
  have hc0 : mixedMoment B raw2082 (Fin.cases (0 : Fin 2) singletonSmall5056) =
      mixedMoment B node2459 node2459Labels := by
    have ha : raw2082 = raw2083 := by apply Matrix.ext; unfold raw2082 raw2083; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5056 = raw2083Labels := by decide +kernel
    rw [ha, hj, canonical2083 B hB]
  have hc1 : mixedMoment B raw2082 (Fin.cases (1 : Fin 2) singletonSmall5056) =
      mixedMoment B node3429 node3429Labels := by
    have ha : raw2082 = raw2084 := by apply Matrix.ext; unfold raw2082 raw2084; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5056 = raw2084Labels := by decide +kernel
    rw [ha, hj, canonical2084 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5059 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5059 node5059Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2462 node2462Labels + mixedMoment B node3436 node3436Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2085 singletonSmall5059
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5059) = raw2085Labels := by decide +kernel
  rw [hl, canonical2085 B hB] at h
  have hc0 : mixedMoment B raw2085 (Fin.cases (0 : Fin 2) singletonSmall5059) =
      mixedMoment B node2462 node2462Labels := by
    have ha : raw2085 = raw2086 := by apply Matrix.ext; unfold raw2085 raw2086; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5059 = raw2086Labels := by decide +kernel
    rw [ha, hj, canonical2086 B hB]
  have hc1 : mixedMoment B raw2085 (Fin.cases (1 : Fin 2) singletonSmall5059) =
      mixedMoment B node3436 node3436Labels := by
    have ha : raw2085 = raw2087 := by apply Matrix.ext; unfold raw2085 raw2087; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5059 = raw2087Labels := by decide +kernel
    rw [ha, hj, canonical2087 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5070 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5070 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5070 node5070Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2477 node2477Labels + mixedMoment B node3444 node3444Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2088 singletonSmall5070
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5070) = raw2088Labels := by decide +kernel
  rw [hl, canonical2088 B hB] at h
  have hc0 : mixedMoment B raw2088 (Fin.cases (0 : Fin 2) singletonSmall5070) =
      mixedMoment B node2477 node2477Labels := by
    have ha : raw2088 = raw2089 := by apply Matrix.ext; unfold raw2088 raw2089; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5070 = raw2089Labels := by decide +kernel
    rw [ha, hj, canonical2089 B hB]
  have hc1 : mixedMoment B raw2088 (Fin.cases (1 : Fin 2) singletonSmall5070) =
      mixedMoment B node3444 node3444Labels := by
    have ha : raw2088 = raw2090 := by apply Matrix.ext; unfold raw2088 raw2090; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5070 = raw2090Labels := by decide +kernel
    rw [ha, hj, canonical2090 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5072 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5072 node5072Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2479 node2479Labels + mixedMoment B node3459 node3459Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2091 singletonSmall5072
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5072) = raw2091Labels := by decide +kernel
  rw [hl, canonical2091 B hB] at h
  have hc0 : mixedMoment B raw2091 (Fin.cases (0 : Fin 2) singletonSmall5072) =
      mixedMoment B node2479 node2479Labels := by
    have ha : raw2091 = raw2092 := by apply Matrix.ext; unfold raw2091 raw2092; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5072 = raw2092Labels := by decide +kernel
    rw [ha, hj, canonical2092 B hB]
  have hc1 : mixedMoment B raw2091 (Fin.cases (1 : Fin 2) singletonSmall5072) =
      mixedMoment B node3459 node3459Labels := by
    have ha : raw2091 = raw2093 := by apply Matrix.ext; unfold raw2091 raw2093; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5072 = raw2093Labels := by decide +kernel
    rw [ha, hj, canonical2093 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5073 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5073 node5073Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2480 node2480Labels + mixedMoment B node3467 node3467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2094 singletonSmall5073
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5073) = raw2094Labels := by decide +kernel
  rw [hl, canonical2094 B hB] at h
  have hc0 : mixedMoment B raw2094 (Fin.cases (0 : Fin 2) singletonSmall5073) =
      mixedMoment B node2480 node2480Labels := by
    have ha : raw2094 = raw2095 := by apply Matrix.ext; unfold raw2094 raw2095; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5073 = raw2095Labels := by decide +kernel
    rw [ha, hj, canonical2095 B hB]
  have hc1 : mixedMoment B raw2094 (Fin.cases (1 : Fin 2) singletonSmall5073) =
      mixedMoment B node3467 node3467Labels := by
    have ha : raw2094 = raw2096 := by apply Matrix.ext; unfold raw2094 raw2096; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5073 = raw2096Labels := by decide +kernel
    rw [ha, hj, canonical2096 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5075 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5075 node5075Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2482 node2482Labels + mixedMoment B node3468 node3468Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2097 singletonSmall5075
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5075) = raw2097Labels := by decide +kernel
  rw [hl, canonical2097 B hB] at h
  have hc0 : mixedMoment B raw2097 (Fin.cases (0 : Fin 2) singletonSmall5075) =
      mixedMoment B node2482 node2482Labels := by
    have ha : raw2097 = raw2098 := by apply Matrix.ext; unfold raw2097 raw2098; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5075 = raw2098Labels := by decide +kernel
    rw [ha, hj, canonical2098 B hB]
  have hc1 : mixedMoment B raw2097 (Fin.cases (1 : Fin 2) singletonSmall5075) =
      mixedMoment B node3468 node3468Labels := by
    have ha : raw2097 = raw2099 := by apply Matrix.ext; unfold raw2097 raw2099; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5075 = raw2099Labels := by decide +kernel
    rw [ha, hj, canonical2099 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5076 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5076 node5076Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2483 node2483Labels + mixedMoment B node3477 node3477Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2100 singletonSmall5076
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5076) = raw2100Labels := by decide +kernel
  rw [hl, canonical2100 B hB] at h
  have hc0 : mixedMoment B raw2100 (Fin.cases (0 : Fin 2) singletonSmall5076) =
      mixedMoment B node2483 node2483Labels := by
    have ha : raw2100 = raw2101 := by apply Matrix.ext; unfold raw2100 raw2101; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5076 = raw2101Labels := by decide +kernel
    rw [ha, hj, canonical2101 B hB]
  have hc1 : mixedMoment B raw2100 (Fin.cases (1 : Fin 2) singletonSmall5076) =
      mixedMoment B node3477 node3477Labels := by
    have ha : raw2100 = raw2102 := by apply Matrix.ext; unfold raw2100 raw2102; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5076 = raw2102Labels := by decide +kernel
    rw [ha, hj, canonical2102 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5078 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5078 node5078Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2485 node2485Labels + mixedMoment B node3481 node3481Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2103 singletonSmall5078
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5078) = raw2103Labels := by decide +kernel
  rw [hl, canonical2103 B hB] at h
  have hc0 : mixedMoment B raw2103 (Fin.cases (0 : Fin 2) singletonSmall5078) =
      mixedMoment B node2485 node2485Labels := by
    have ha : raw2103 = raw2104 := by apply Matrix.ext; unfold raw2103 raw2104; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5078 = raw2104Labels := by decide +kernel
    rw [ha, hj, canonical2104 B hB]
  have hc1 : mixedMoment B raw2103 (Fin.cases (1 : Fin 2) singletonSmall5078) =
      mixedMoment B node3481 node3481Labels := by
    have ha : raw2103 = raw2105 := by apply Matrix.ext; unfold raw2103 raw2105; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5078 = raw2105Labels := by decide +kernel
    rw [ha, hj, canonical2105 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5080 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5080 node5080Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2488 node2488Labels + mixedMoment B node3478 node3478Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2106 singletonSmall5080
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5080) = raw2106Labels := by decide +kernel
  rw [hl, canonical2106 B hB] at h
  have hc0 : mixedMoment B raw2106 (Fin.cases (0 : Fin 2) singletonSmall5080) =
      mixedMoment B node2488 node2488Labels := by
    have ha : raw2106 = raw2107 := by apply Matrix.ext; unfold raw2106 raw2107; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5080 = raw2107Labels := by decide +kernel
    rw [ha, hj, canonical2107 B hB]
  have hc1 : mixedMoment B raw2106 (Fin.cases (1 : Fin 2) singletonSmall5080) =
      mixedMoment B node3478 node3478Labels := by
    have ha : raw2106 = raw2108 := by apply Matrix.ext; unfold raw2106 raw2108; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5080 = raw2108Labels := by decide +kernel
    rw [ha, hj, canonical2108 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5081 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5081 node5081Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2489 node2489Labels + mixedMoment B node3482 node3482Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2109 singletonSmall5081
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5081) = raw2109Labels := by decide +kernel
  rw [hl, canonical2109 B hB] at h
  have hc0 : mixedMoment B raw2109 (Fin.cases (0 : Fin 2) singletonSmall5081) =
      mixedMoment B node2489 node2489Labels := by
    have ha : raw2109 = raw2110 := by apply Matrix.ext; unfold raw2109 raw2110; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5081 = raw2110Labels := by decide +kernel
    rw [ha, hj, canonical2110 B hB]
  have hc1 : mixedMoment B raw2109 (Fin.cases (1 : Fin 2) singletonSmall5081) =
      mixedMoment B node3482 node3482Labels := by
    have ha : raw2109 = raw2111 := by apply Matrix.ext; unfold raw2109 raw2111; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5081 = raw2111Labels := by decide +kernel
    rw [ha, hj, canonical2111 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5093 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5093 node5093Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2503 node2503Labels + mixedMoment B node3446 node3446Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2112 singletonSmall5093
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5093) = raw2112Labels := by decide +kernel
  rw [hl, canonical2112 B hB] at h
  have hc0 : mixedMoment B raw2112 (Fin.cases (0 : Fin 2) singletonSmall5093) =
      mixedMoment B node2503 node2503Labels := by
    have ha : raw2112 = raw2113 := by apply Matrix.ext; unfold raw2112 raw2113; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5093 = raw2113Labels := by decide +kernel
    rw [ha, hj, canonical2113 B hB]
  have hc1 : mixedMoment B raw2112 (Fin.cases (1 : Fin 2) singletonSmall5093) =
      mixedMoment B node3446 node3446Labels := by
    have ha : raw2112 = raw2114 := by apply Matrix.ext; unfold raw2112 raw2114; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5093 = raw2114Labels := by decide +kernel
    rw [ha, hj, canonical2114 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5094 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5094 node5094Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2504 node2504Labels + mixedMoment B node2504 node2504Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2115 singletonSmall5094
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5094) = raw2115Labels := by decide +kernel
  rw [hl, canonical2115 B hB] at h
  have hc0 : mixedMoment B raw2115 (Fin.cases (0 : Fin 2) singletonSmall5094) =
      mixedMoment B node2504 node2504Labels := by
    have ha : raw2115 = raw2116 := by apply Matrix.ext; unfold raw2115 raw2116; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5094 = raw2116Labels := by decide +kernel
    rw [ha, hj, canonical2116 B hB]
  have hc1 : mixedMoment B raw2115 (Fin.cases (1 : Fin 2) singletonSmall5094) =
      mixedMoment B node2504 node2504Labels := by
    have ha : raw2115 = raw2117 := by apply Matrix.ext; unfold raw2115 raw2117; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5094 = raw2117Labels := by decide +kernel
    rw [ha, hj, canonical2117 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5095 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5095 node5095Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2505 node2505Labels + mixedMoment B node3448 node3448Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2118 singletonSmall5095
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5095) = raw2118Labels := by decide +kernel
  rw [hl, canonical2118 B hB] at h
  have hc0 : mixedMoment B raw2118 (Fin.cases (0 : Fin 2) singletonSmall5095) =
      mixedMoment B node2505 node2505Labels := by
    have ha : raw2118 = raw2119 := by apply Matrix.ext; unfold raw2118 raw2119; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5095 = raw2119Labels := by decide +kernel
    rw [ha, hj, canonical2119 B hB]
  have hc1 : mixedMoment B raw2118 (Fin.cases (1 : Fin 2) singletonSmall5095) =
      mixedMoment B node3448 node3448Labels := by
    have ha : raw2118 = raw2120 := by apply Matrix.ext; unfold raw2118 raw2120; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5095 = raw2120Labels := by decide +kernel
    rw [ha, hj, canonical2120 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5098 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5098 node5098Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2508 node2508Labels + mixedMoment B node3460 node3460Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2121 singletonSmall5098
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5098) = raw2121Labels := by decide +kernel
  rw [hl, canonical2121 B hB] at h
  have hc0 : mixedMoment B raw2121 (Fin.cases (0 : Fin 2) singletonSmall5098) =
      mixedMoment B node2508 node2508Labels := by
    have ha : raw2121 = raw2122 := by apply Matrix.ext; unfold raw2121 raw2122; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5098 = raw2122Labels := by decide +kernel
    rw [ha, hj, canonical2122 B hB]
  have hc1 : mixedMoment B raw2121 (Fin.cases (1 : Fin 2) singletonSmall5098) =
      mixedMoment B node3460 node3460Labels := by
    have ha : raw2121 = raw2123 := by apply Matrix.ext; unfold raw2121 raw2123; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5098 = raw2123Labels := by decide +kernel
    rw [ha, hj, canonical2123 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5099 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5099 node5099Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2509 node2509Labels + mixedMoment B node2704 node2704Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2124 singletonSmall5099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5099) = raw2124Labels := by decide +kernel
  rw [hl, canonical2124 B hB] at h
  have hc0 : mixedMoment B raw2124 (Fin.cases (0 : Fin 2) singletonSmall5099) =
      mixedMoment B node2509 node2509Labels := by
    have ha : raw2124 = raw2125 := by apply Matrix.ext; unfold raw2124 raw2125; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5099 = raw2125Labels := by decide +kernel
    rw [ha, hj, canonical2125 B hB]
  have hc1 : mixedMoment B raw2124 (Fin.cases (1 : Fin 2) singletonSmall5099) =
      mixedMoment B node2704 node2704Labels := by
    have ha : raw2124 = raw2126 := by apply Matrix.ext; unfold raw2124 raw2126; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5099 = raw2126Labels := by decide +kernel
    rw [ha, hj, canonical2126 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5102 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5102 node5102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2512 node2512Labels + mixedMoment B node3471 node3471Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2127 singletonSmall5102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5102) = raw2127Labels := by decide +kernel
  rw [hl, canonical2127 B hB] at h
  have hc0 : mixedMoment B raw2127 (Fin.cases (0 : Fin 2) singletonSmall5102) =
      mixedMoment B node2512 node2512Labels := by
    have ha : raw2127 = raw2128 := by apply Matrix.ext; unfold raw2127 raw2128; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5102 = raw2128Labels := by decide +kernel
    rw [ha, hj, canonical2128 B hB]
  have hc1 : mixedMoment B raw2127 (Fin.cases (1 : Fin 2) singletonSmall5102) =
      mixedMoment B node3471 node3471Labels := by
    have ha : raw2127 = raw2129 := by apply Matrix.ext; unfold raw2127 raw2129; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5102 = raw2129Labels := by decide +kernel
    rw [ha, hj, canonical2129 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5105 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5105 node5105Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2515 node2515Labels + mixedMoment B node3479 node3479Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2130 singletonSmall5105
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5105) = raw2130Labels := by decide +kernel
  rw [hl, canonical2130 B hB] at h
  have hc0 : mixedMoment B raw2130 (Fin.cases (0 : Fin 2) singletonSmall5105) =
      mixedMoment B node2515 node2515Labels := by
    have ha : raw2130 = raw2131 := by apply Matrix.ext; unfold raw2130 raw2131; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5105 = raw2131Labels := by decide +kernel
    rw [ha, hj, canonical2131 B hB]
  have hc1 : mixedMoment B raw2130 (Fin.cases (1 : Fin 2) singletonSmall5105) =
      mixedMoment B node3479 node3479Labels := by
    have ha : raw2130 = raw2132 := by apply Matrix.ext; unfold raw2130 raw2132; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5105 = raw2132Labels := by decide +kernel
    rw [ha, hj, canonical2132 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5109 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5109 node5109Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2519 node2519Labels + mixedMoment B node3486 node3486Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2133 singletonSmall5109
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5109) = raw2133Labels := by decide +kernel
  rw [hl, canonical2133 B hB] at h
  have hc0 : mixedMoment B raw2133 (Fin.cases (0 : Fin 2) singletonSmall5109) =
      mixedMoment B node2519 node2519Labels := by
    have ha : raw2133 = raw2134 := by apply Matrix.ext; unfold raw2133 raw2134; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5109 = raw2134Labels := by decide +kernel
    rw [ha, hj, canonical2134 B hB]
  have hc1 : mixedMoment B raw2133 (Fin.cases (1 : Fin 2) singletonSmall5109) =
      mixedMoment B node3486 node3486Labels := by
    have ha : raw2133 = raw2135 := by apply Matrix.ext; unfold raw2133 raw2135; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5109 = raw2135Labels := by decide +kernel
    rw [ha, hj, canonical2135 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5110 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5110 node5110Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2522 node2522Labels + mixedMoment B node2685 node2685Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2136 singletonSmall5110
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5110) = raw2136Labels := by decide +kernel
  rw [hl, canonical2136 B hB] at h
  have hc0 : mixedMoment B raw2136 (Fin.cases (0 : Fin 2) singletonSmall5110) =
      mixedMoment B node2522 node2522Labels := by
    have ha : raw2136 = raw2137 := by apply Matrix.ext; unfold raw2136 raw2137; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5110 = raw2137Labels := by decide +kernel
    rw [ha, hj, canonical2137 B hB]
  have hc1 : mixedMoment B raw2136 (Fin.cases (1 : Fin 2) singletonSmall5110) =
      mixedMoment B node2685 node2685Labels := by
    have ha : raw2136 = raw2138 := by apply Matrix.ext; unfold raw2136 raw2138; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5110 = raw2138Labels := by decide +kernel
    rw [ha, hj, canonical2138 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5114 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5114 node5114Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2896 node2896Labels + mixedMoment B node3597 node3597Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2139 singletonSmall5114
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5114) = raw2139Labels := by decide +kernel
  rw [hl, canonical2139 B hB] at h
  have hc0 : mixedMoment B raw2139 (Fin.cases (0 : Fin 2) singletonSmall5114) =
      mixedMoment B node2896 node2896Labels := by
    have ha : raw2139 = raw2140 := by apply Matrix.ext; unfold raw2139 raw2140; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5114 = raw2140Labels := by decide +kernel
    rw [ha, hj, canonical2140 B hB]
  have hc1 : mixedMoment B raw2139 (Fin.cases (1 : Fin 2) singletonSmall5114) =
      mixedMoment B node3597 node3597Labels := by
    have ha : raw2139 = raw2141 := by apply Matrix.ext; unfold raw2139 raw2141; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5114 = raw2141Labels := by decide +kernel
    rw [ha, hj, canonical2141 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5117 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5117 node5117Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2893 node2893Labels + mixedMoment B node3599 node3599Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2142 singletonSmall5117
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5117) = raw2142Labels := by decide +kernel
  rw [hl, canonical2142 B hB] at h
  have hc0 : mixedMoment B raw2142 (Fin.cases (0 : Fin 2) singletonSmall5117) =
      mixedMoment B node2893 node2893Labels := by
    have ha : raw2142 = raw2143 := by apply Matrix.ext; unfold raw2142 raw2143; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5117 = raw2143Labels := by decide +kernel
    rw [ha, hj, canonical2143 B hB]
  have hc1 : mixedMoment B raw2142 (Fin.cases (1 : Fin 2) singletonSmall5117) =
      mixedMoment B node3599 node3599Labels := by
    have ha : raw2142 = raw2144 := by apply Matrix.ext; unfold raw2142 raw2144; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5117 = raw2144Labels := by decide +kernel
    rw [ha, hj, canonical2144 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5118 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5118 node5118Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2891 node2891Labels + mixedMoment B node3598 node3598Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2145 singletonSmall5118
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5118) = raw2145Labels := by decide +kernel
  rw [hl, canonical2145 B hB] at h
  have hc0 : mixedMoment B raw2145 (Fin.cases (0 : Fin 2) singletonSmall5118) =
      mixedMoment B node2891 node2891Labels := by
    have ha : raw2145 = raw2146 := by apply Matrix.ext; unfold raw2145 raw2146; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5118 = raw2146Labels := by decide +kernel
    rw [ha, hj, canonical2146 B hB]
  have hc1 : mixedMoment B raw2145 (Fin.cases (1 : Fin 2) singletonSmall5118) =
      mixedMoment B node3598 node3598Labels := by
    have ha : raw2145 = raw2147 := by apply Matrix.ext; unfold raw2145 raw2147; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5118 = raw2147Labels := by decide +kernel
    rw [ha, hj, canonical2147 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5119 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5119 node5119Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2845 node2845Labels + mixedMoment B node3604 node3604Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2148 singletonSmall5119
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5119) = raw2148Labels := by decide +kernel
  rw [hl, canonical2148 B hB] at h
  have hc0 : mixedMoment B raw2148 (Fin.cases (0 : Fin 2) singletonSmall5119) =
      mixedMoment B node2845 node2845Labels := by
    have ha : raw2148 = raw2149 := by apply Matrix.ext; unfold raw2148 raw2149; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5119 = raw2149Labels := by decide +kernel
    rw [ha, hj, canonical2149 B hB]
  have hc1 : mixedMoment B raw2148 (Fin.cases (1 : Fin 2) singletonSmall5119) =
      mixedMoment B node3604 node3604Labels := by
    have ha : raw2148 = raw2150 := by apply Matrix.ext; unfold raw2148 raw2150; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5119 = raw2150Labels := by decide +kernel
    rw [ha, hj, canonical2150 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical17

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5120 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5120 node5120Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2844 node2844Labels + mixedMoment B node3609 node3609Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2151 singletonSmall5120
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5120) = raw2151Labels := by decide +kernel
  rw [hl, canonical2151 B hB] at h
  have hc0 : mixedMoment B raw2151 (Fin.cases (0 : Fin 2) singletonSmall5120) =
      mixedMoment B node2844 node2844Labels := by
    have ha : raw2151 = raw2152 := by apply Matrix.ext; unfold raw2151 raw2152; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5120 = raw2152Labels := by decide +kernel
    rw [ha, hj, canonical2152 B hB]
  have hc1 : mixedMoment B raw2151 (Fin.cases (1 : Fin 2) singletonSmall5120) =
      mixedMoment B node3609 node3609Labels := by
    have ha : raw2151 = raw2153 := by apply Matrix.ext; unfold raw2151 raw2153; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5120 = raw2153Labels := by decide +kernel
    rw [ha, hj, canonical2153 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5123 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5123 node5123Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2536 node2536Labels + mixedMoment B node3370 node3370Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2154 singletonSmall5123
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5123) = raw2154Labels := by decide +kernel
  rw [hl, canonical2154 B hB] at h
  have hc0 : mixedMoment B raw2154 (Fin.cases (0 : Fin 2) singletonSmall5123) =
      mixedMoment B node2536 node2536Labels := by
    have ha : raw2154 = raw2155 := by apply Matrix.ext; unfold raw2154 raw2155; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5123 = raw2155Labels := by decide +kernel
    rw [ha, hj, canonical2155 B hB]
  have hc1 : mixedMoment B raw2154 (Fin.cases (1 : Fin 2) singletonSmall5123) =
      mixedMoment B node3370 node3370Labels := by
    have ha : raw2154 = raw2156 := by apply Matrix.ext; unfold raw2154 raw2156; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5123 = raw2156Labels := by decide +kernel
    rw [ha, hj, canonical2156 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5125 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5125 node5125Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2539 node2539Labels + mixedMoment B node3372 node3372Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2157 singletonSmall5125
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5125) = raw2157Labels := by decide +kernel
  rw [hl, canonical2157 B hB] at h
  have hc0 : mixedMoment B raw2157 (Fin.cases (0 : Fin 2) singletonSmall5125) =
      mixedMoment B node2539 node2539Labels := by
    have ha : raw2157 = raw2158 := by apply Matrix.ext; unfold raw2157 raw2158; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5125 = raw2158Labels := by decide +kernel
    rw [ha, hj, canonical2158 B hB]
  have hc1 : mixedMoment B raw2157 (Fin.cases (1 : Fin 2) singletonSmall5125) =
      mixedMoment B node3372 node3372Labels := by
    have ha : raw2157 = raw2159 := by apply Matrix.ext; unfold raw2157 raw2159; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5125 = raw2159Labels := by decide +kernel
    rw [ha, hj, canonical2159 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5126 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5126 node5126Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2541 node2541Labels + mixedMoment B node3487 node3487Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2160 singletonSmall5126
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5126) = raw2160Labels := by decide +kernel
  rw [hl, canonical2160 B hB] at h
  have hc0 : mixedMoment B raw2160 (Fin.cases (0 : Fin 2) singletonSmall5126) =
      mixedMoment B node2541 node2541Labels := by
    have ha : raw2160 = raw2161 := by apply Matrix.ext; unfold raw2160 raw2161; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5126 = raw2161Labels := by decide +kernel
    rw [ha, hj, canonical2161 B hB]
  have hc1 : mixedMoment B raw2160 (Fin.cases (1 : Fin 2) singletonSmall5126) =
      mixedMoment B node3487 node3487Labels := by
    have ha : raw2160 = raw2162 := by apply Matrix.ext; unfold raw2160 raw2162; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5126 = raw2162Labels := by decide +kernel
    rw [ha, hj, canonical2162 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5134 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5134 node5134Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2553 node2553Labels + mixedMoment B node3514 node3514Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2163 singletonSmall5134
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5134) = raw2163Labels := by decide +kernel
  rw [hl, canonical2163 B hB] at h
  have hc0 : mixedMoment B raw2163 (Fin.cases (0 : Fin 2) singletonSmall5134) =
      mixedMoment B node2553 node2553Labels := by
    have ha : raw2163 = raw2164 := by apply Matrix.ext; unfold raw2163 raw2164; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5134 = raw2164Labels := by decide +kernel
    rw [ha, hj, canonical2164 B hB]
  have hc1 : mixedMoment B raw2163 (Fin.cases (1 : Fin 2) singletonSmall5134) =
      mixedMoment B node3514 node3514Labels := by
    have ha : raw2163 = raw2165 := by apply Matrix.ext; unfold raw2163 raw2165; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5134 = raw2165Labels := by decide +kernel
    rw [ha, hj, canonical2165 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5137 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5137 node5137Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2556 node2556Labels + mixedMoment B node3521 node3521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2166 singletonSmall5137
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5137) = raw2166Labels := by decide +kernel
  rw [hl, canonical2166 B hB] at h
  have hc0 : mixedMoment B raw2166 (Fin.cases (0 : Fin 2) singletonSmall5137) =
      mixedMoment B node2556 node2556Labels := by
    have ha : raw2166 = raw2167 := by apply Matrix.ext; unfold raw2166 raw2167; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5137 = raw2167Labels := by decide +kernel
    rw [ha, hj, canonical2167 B hB]
  have hc1 : mixedMoment B raw2166 (Fin.cases (1 : Fin 2) singletonSmall5137) =
      mixedMoment B node3521 node3521Labels := by
    have ha : raw2166 = raw2168 := by apply Matrix.ext; unfold raw2166 raw2168; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5137 = raw2168Labels := by decide +kernel
    rw [ha, hj, canonical2168 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5141 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5141 node5141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2561 node2561Labels + mixedMoment B node3522 node3522Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2169 singletonSmall5141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5141) = raw2169Labels := by decide +kernel
  rw [hl, canonical2169 B hB] at h
  have hc0 : mixedMoment B raw2169 (Fin.cases (0 : Fin 2) singletonSmall5141) =
      mixedMoment B node2561 node2561Labels := by
    have ha : raw2169 = raw2170 := by apply Matrix.ext; unfold raw2169 raw2170; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5141 = raw2170Labels := by decide +kernel
    rw [ha, hj, canonical2170 B hB]
  have hc1 : mixedMoment B raw2169 (Fin.cases (1 : Fin 2) singletonSmall5141) =
      mixedMoment B node3522 node3522Labels := by
    have ha : raw2169 = raw2171 := by apply Matrix.ext; unfold raw2169 raw2171; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5141 = raw2171Labels := by decide +kernel
    rw [ha, hj, canonical2171 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5142 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5142 node5142Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2913 node2913Labels + mixedMoment B node3610 node3610Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2172 singletonSmall5142
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5142) = raw2172Labels := by decide +kernel
  rw [hl, canonical2172 B hB] at h
  have hc0 : mixedMoment B raw2172 (Fin.cases (0 : Fin 2) singletonSmall5142) =
      mixedMoment B node2913 node2913Labels := by
    have ha : raw2172 = raw2173 := by apply Matrix.ext; unfold raw2172 raw2173; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5142 = raw2173Labels := by decide +kernel
    rw [ha, hj, canonical2173 B hB]
  have hc1 : mixedMoment B raw2172 (Fin.cases (1 : Fin 2) singletonSmall5142) =
      mixedMoment B node3610 node3610Labels := by
    have ha : raw2172 = raw2174 := by apply Matrix.ext; unfold raw2172 raw2174; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5142 = raw2174Labels := by decide +kernel
    rw [ha, hj, canonical2174 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5149 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5149 node5149Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2924 node2924Labels + mixedMoment B node3605 node3605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2175 singletonSmall5149
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5149) = raw2175Labels := by decide +kernel
  rw [hl, canonical2175 B hB] at h
  have hc0 : mixedMoment B raw2175 (Fin.cases (0 : Fin 2) singletonSmall5149) =
      mixedMoment B node2924 node2924Labels := by
    have ha : raw2175 = raw2176 := by apply Matrix.ext; unfold raw2175 raw2176; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5149 = raw2176Labels := by decide +kernel
    rw [ha, hj, canonical2176 B hB]
  have hc1 : mixedMoment B raw2175 (Fin.cases (1 : Fin 2) singletonSmall5149) =
      mixedMoment B node3605 node3605Labels := by
    have ha : raw2175 = raw2177 := by apply Matrix.ext; unfold raw2175 raw2177; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5149 = raw2177Labels := by decide +kernel
    rw [ha, hj, canonical2177 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5152 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5152 node5152Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2931 node2931Labels + mixedMoment B node3612 node3612Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2178 singletonSmall5152
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5152) = raw2178Labels := by decide +kernel
  rw [hl, canonical2178 B hB] at h
  have hc0 : mixedMoment B raw2178 (Fin.cases (0 : Fin 2) singletonSmall5152) =
      mixedMoment B node2931 node2931Labels := by
    have ha : raw2178 = raw2179 := by apply Matrix.ext; unfold raw2178 raw2179; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5152 = raw2179Labels := by decide +kernel
    rw [ha, hj, canonical2179 B hB]
  have hc1 : mixedMoment B raw2178 (Fin.cases (1 : Fin 2) singletonSmall5152) =
      mixedMoment B node3612 node3612Labels := by
    have ha : raw2178 = raw2180 := by apply Matrix.ext; unfold raw2178 raw2180; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5152 = raw2180Labels := by decide +kernel
    rw [ha, hj, canonical2180 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5155 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5155 node5155Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2908 node2908Labels + mixedMoment B node3600 node3600Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2181 singletonSmall5155
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5155) = raw2181Labels := by decide +kernel
  rw [hl, canonical2181 B hB] at h
  have hc0 : mixedMoment B raw2181 (Fin.cases (0 : Fin 2) singletonSmall5155) =
      mixedMoment B node2908 node2908Labels := by
    have ha : raw2181 = raw2182 := by apply Matrix.ext; unfold raw2181 raw2182; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5155 = raw2182Labels := by decide +kernel
    rw [ha, hj, canonical2182 B hB]
  have hc1 : mixedMoment B raw2181 (Fin.cases (1 : Fin 2) singletonSmall5155) =
      mixedMoment B node3600 node3600Labels := by
    have ha : raw2181 = raw2183 := by apply Matrix.ext; unfold raw2181 raw2183; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5155 = raw2183Labels := by decide +kernel
    rw [ha, hj, canonical2183 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5156 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5156 node5156Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2911 node2911Labels + mixedMoment B node3611 node3611Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2184 singletonSmall5156
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5156) = raw2184Labels := by decide +kernel
  rw [hl, canonical2184 B hB] at h
  have hc0 : mixedMoment B raw2184 (Fin.cases (0 : Fin 2) singletonSmall5156) =
      mixedMoment B node2911 node2911Labels := by
    have ha : raw2184 = raw2185 := by apply Matrix.ext; unfold raw2184 raw2185; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5156 = raw2185Labels := by decide +kernel
    rw [ha, hj, canonical2185 B hB]
  have hc1 : mixedMoment B raw2184 (Fin.cases (1 : Fin 2) singletonSmall5156) =
      mixedMoment B node3611 node3611Labels := by
    have ha : raw2184 = raw2186 := by apply Matrix.ext; unfold raw2184 raw2186; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5156 = raw2186Labels := by decide +kernel
    rw [ha, hj, canonical2186 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5162 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5162 node5162Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2589 node2589Labels + mixedMoment B node3563 node3563Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2187 singletonSmall5162
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5162) = raw2187Labels := by decide +kernel
  rw [hl, canonical2187 B hB] at h
  have hc0 : mixedMoment B raw2187 (Fin.cases (0 : Fin 2) singletonSmall5162) =
      mixedMoment B node2589 node2589Labels := by
    have ha : raw2187 = raw2188 := by apply Matrix.ext; unfold raw2187 raw2188; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5162 = raw2188Labels := by decide +kernel
    rw [ha, hj, canonical2188 B hB]
  have hc1 : mixedMoment B raw2187 (Fin.cases (1 : Fin 2) singletonSmall5162) =
      mixedMoment B node3563 node3563Labels := by
    have ha : raw2187 = raw2189 := by apply Matrix.ext; unfold raw2187 raw2189; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5162 = raw2189Labels := by decide +kernel
    rw [ha, hj, canonical2189 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5163 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5163 node5163Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2590 node2590Labels + mixedMoment B node3564 node3564Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2190 singletonSmall5163
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5163) = raw2190Labels := by decide +kernel
  rw [hl, canonical2190 B hB] at h
  have hc0 : mixedMoment B raw2190 (Fin.cases (0 : Fin 2) singletonSmall5163) =
      mixedMoment B node2590 node2590Labels := by
    have ha : raw2190 = raw2191 := by apply Matrix.ext; unfold raw2190 raw2191; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5163 = raw2191Labels := by decide +kernel
    rw [ha, hj, canonical2191 B hB]
  have hc1 : mixedMoment B raw2190 (Fin.cases (1 : Fin 2) singletonSmall5163) =
      mixedMoment B node3564 node3564Labels := by
    have ha : raw2190 = raw2192 := by apply Matrix.ext; unfold raw2190 raw2192; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5163 = raw2192Labels := by decide +kernel
    rw [ha, hj, canonical2192 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5167 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5167 node5167Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2593 node2593Labels + mixedMoment B node3602 node3602Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2193 singletonSmall5167
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5167) = raw2193Labels := by decide +kernel
  rw [hl, canonical2193 B hB] at h
  have hc0 : mixedMoment B raw2193 (Fin.cases (0 : Fin 2) singletonSmall5167) =
      mixedMoment B node2593 node2593Labels := by
    have ha : raw2193 = raw2194 := by apply Matrix.ext; unfold raw2193 raw2194; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5167 = raw2194Labels := by decide +kernel
    rw [ha, hj, canonical2194 B hB]
  have hc1 : mixedMoment B raw2193 (Fin.cases (1 : Fin 2) singletonSmall5167) =
      mixedMoment B node3602 node3602Labels := by
    have ha : raw2193 = raw2195 := by apply Matrix.ext; unfold raw2193 raw2195; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5167 = raw2195Labels := by decide +kernel
    rw [ha, hj, canonical2195 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5168 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5168 node5168Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2594 node2594Labels + mixedMoment B node3603 node3603Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2196 singletonSmall5168
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5168) = raw2196Labels := by decide +kernel
  rw [hl, canonical2196 B hB] at h
  have hc0 : mixedMoment B raw2196 (Fin.cases (0 : Fin 2) singletonSmall5168) =
      mixedMoment B node2594 node2594Labels := by
    have ha : raw2196 = raw2197 := by apply Matrix.ext; unfold raw2196 raw2197; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5168 = raw2197Labels := by decide +kernel
    rw [ha, hj, canonical2197 B hB]
  have hc1 : mixedMoment B raw2196 (Fin.cases (1 : Fin 2) singletonSmall5168) =
      mixedMoment B node3603 node3603Labels := by
    have ha : raw2196 = raw2198 := by apply Matrix.ext; unfold raw2196 raw2198; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5168 = raw2198Labels := by decide +kernel
    rw [ha, hj, canonical2198 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5169 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5169 node5169Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2595 node2595Labels + mixedMoment B node3607 node3607Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2199 singletonSmall5169
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5169) = raw2199Labels := by decide +kernel
  rw [hl, canonical2199 B hB] at h
  have hc0 : mixedMoment B raw2199 (Fin.cases (0 : Fin 2) singletonSmall5169) =
      mixedMoment B node2595 node2595Labels := by
    have ha : raw2199 = raw2200 := by apply Matrix.ext; unfold raw2199 raw2200; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5169 = raw2200Labels := by decide +kernel
    rw [ha, hj, canonical2200 B hB]
  have hc1 : mixedMoment B raw2199 (Fin.cases (1 : Fin 2) singletonSmall5169) =
      mixedMoment B node3607 node3607Labels := by
    have ha : raw2199 = raw2201 := by apply Matrix.ext; unfold raw2199 raw2201; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5169 = raw2201Labels := by decide +kernel
    rw [ha, hj, canonical2201 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5170 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5170 node5170Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2954 node2954Labels + mixedMoment B node3606 node3606Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2202 singletonSmall5170
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5170) = raw2202Labels := by decide +kernel
  rw [hl, canonical2202 B hB] at h
  have hc0 : mixedMoment B raw2202 (Fin.cases (0 : Fin 2) singletonSmall5170) =
      mixedMoment B node2954 node2954Labels := by
    have ha : raw2202 = raw2203 := by apply Matrix.ext; unfold raw2202 raw2203; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5170 = raw2203Labels := by decide +kernel
    rw [ha, hj, canonical2203 B hB]
  have hc1 : mixedMoment B raw2202 (Fin.cases (1 : Fin 2) singletonSmall5170) =
      mixedMoment B node3606 node3606Labels := by
    have ha : raw2202 = raw2204 := by apply Matrix.ext; unfold raw2202 raw2204; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5170 = raw2204Labels := by decide +kernel
    rw [ha, hj, canonical2204 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5171 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5171 node5171Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2598 node2598Labels + mixedMoment B node3608 node3608Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2205 singletonSmall5171
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5171) = raw2205Labels := by decide +kernel
  rw [hl, canonical2205 B hB] at h
  have hc0 : mixedMoment B raw2205 (Fin.cases (0 : Fin 2) singletonSmall5171) =
      mixedMoment B node2598 node2598Labels := by
    have ha : raw2205 = raw2206 := by apply Matrix.ext; unfold raw2205 raw2206; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5171 = raw2206Labels := by decide +kernel
    rw [ha, hj, canonical2206 B hB]
  have hc1 : mixedMoment B raw2205 (Fin.cases (1 : Fin 2) singletonSmall5171) =
      mixedMoment B node3608 node3608Labels := by
    have ha : raw2205 = raw2207 := by apply Matrix.ext; unfold raw2205 raw2207; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5171 = raw2207Labels := by decide +kernel
    rw [ha, hj, canonical2207 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5172 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5172 node5172Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2599 node2599Labels + mixedMoment B node3613 node3613Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2208 singletonSmall5172
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5172) = raw2208Labels := by decide +kernel
  rw [hl, canonical2208 B hB] at h
  have hc0 : mixedMoment B raw2208 (Fin.cases (0 : Fin 2) singletonSmall5172) =
      mixedMoment B node2599 node2599Labels := by
    have ha : raw2208 = raw2209 := by apply Matrix.ext; unfold raw2208 raw2209; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5172 = raw2209Labels := by decide +kernel
    rw [ha, hj, canonical2209 B hB]
  have hc1 : mixedMoment B raw2208 (Fin.cases (1 : Fin 2) singletonSmall5172) =
      mixedMoment B node3613 node3613Labels := by
    have ha : raw2208 = raw2210 := by apply Matrix.ext; unfold raw2208 raw2210; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5172 = raw2210Labels := by decide +kernel
    rw [ha, hj, canonical2210 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5174 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5174 node5174Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2601 node2601Labels + mixedMoment B node3615 node3615Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2211 singletonSmall5174
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5174) = raw2211Labels := by decide +kernel
  rw [hl, canonical2211 B hB] at h
  have hc0 : mixedMoment B raw2211 (Fin.cases (0 : Fin 2) singletonSmall5174) =
      mixedMoment B node2601 node2601Labels := by
    have ha : raw2211 = raw2212 := by apply Matrix.ext; unfold raw2211 raw2212; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5174 = raw2212Labels := by decide +kernel
    rw [ha, hj, canonical2212 B hB]
  have hc1 : mixedMoment B raw2211 (Fin.cases (1 : Fin 2) singletonSmall5174) =
      mixedMoment B node3615 node3615Labels := by
    have ha : raw2211 = raw2213 := by apply Matrix.ext; unfold raw2211 raw2213; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5174 = raw2213Labels := by decide +kernel
    rw [ha, hj, canonical2213 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5176 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5176 node5176Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2604 node2604Labels + mixedMoment B node3614 node3614Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2214 singletonSmall5176
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5176) = raw2214Labels := by decide +kernel
  rw [hl, canonical2214 B hB] at h
  have hc0 : mixedMoment B raw2214 (Fin.cases (0 : Fin 2) singletonSmall5176) =
      mixedMoment B node2604 node2604Labels := by
    have ha : raw2214 = raw2215 := by apply Matrix.ext; unfold raw2214 raw2215; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5176 = raw2215Labels := by decide +kernel
    rw [ha, hj, canonical2215 B hB]
  have hc1 : mixedMoment B raw2214 (Fin.cases (1 : Fin 2) singletonSmall5176) =
      mixedMoment B node3614 node3614Labels := by
    have ha : raw2214 = raw2216 := by apply Matrix.ext; unfold raw2214 raw2216; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5176 = raw2216Labels := by decide +kernel
    rw [ha, hj, canonical2216 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5177 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5177 node5177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2605 node2605Labels + mixedMoment B node3616 node3616Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2217 singletonSmall5177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5177) = raw2217Labels := by decide +kernel
  rw [hl, canonical2217 B hB] at h
  have hc0 : mixedMoment B raw2217 (Fin.cases (0 : Fin 2) singletonSmall5177) =
      mixedMoment B node2605 node2605Labels := by
    have ha : raw2217 = raw2218 := by apply Matrix.ext; unfold raw2217 raw2218; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5177 = raw2218Labels := by decide +kernel
    rw [ha, hj, canonical2218 B hB]
  have hc1 : mixedMoment B raw2217 (Fin.cases (1 : Fin 2) singletonSmall5177) =
      mixedMoment B node3616 node3616Labels := by
    have ha : raw2217 = raw2219 := by apply Matrix.ext; unfold raw2217 raw2219; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5177 = raw2219Labels := by decide +kernel
    rw [ha, hj, canonical2219 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

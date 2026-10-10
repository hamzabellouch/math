import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical17

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5192 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5192 node5192Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2853 node2853Labels + mixedMoment B node3620 node3620Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2220 singletonSmall5192
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5192) = raw2220Labels := by decide +kernel
  rw [hl, canonical2220 B hB] at h
  have hc0 : mixedMoment B raw2220 (Fin.cases (0 : Fin 2) singletonSmall5192) =
      mixedMoment B node2853 node2853Labels := by
    have ha : raw2220 = raw2221 := by apply Matrix.ext; unfold raw2220 raw2221; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5192 = raw2221Labels := by decide +kernel
    rw [ha, hj, canonical2221 B hB]
  have hc1 : mixedMoment B raw2220 (Fin.cases (1 : Fin 2) singletonSmall5192) =
      mixedMoment B node3620 node3620Labels := by
    have ha : raw2220 = raw2222 := by apply Matrix.ext; unfold raw2220 raw2222; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5192 = raw2222Labels := by decide +kernel
    rw [ha, hj, canonical2222 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5193 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5193 node5193Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2856 node2856Labels + mixedMoment B node3630 node3630Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2223 singletonSmall5193
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5193) = raw2223Labels := by decide +kernel
  rw [hl, canonical2223 B hB] at h
  have hc0 : mixedMoment B raw2223 (Fin.cases (0 : Fin 2) singletonSmall5193) =
      mixedMoment B node2856 node2856Labels := by
    have ha : raw2223 = raw2224 := by apply Matrix.ext; unfold raw2223 raw2224; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5193 = raw2224Labels := by decide +kernel
    rw [ha, hj, canonical2224 B hB]
  have hc1 : mixedMoment B raw2223 (Fin.cases (1 : Fin 2) singletonSmall5193) =
      mixedMoment B node3630 node3630Labels := by
    have ha : raw2223 = raw2225 := by apply Matrix.ext; unfold raw2223 raw2225; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5193 = raw2225Labels := by decide +kernel
    rw [ha, hj, canonical2225 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5202 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5202 node5202Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2880 node2880Labels + mixedMoment B node3617 node3617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2226 singletonSmall5202
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5202) = raw2226Labels := by decide +kernel
  rw [hl, canonical2226 B hB] at h
  have hc0 : mixedMoment B raw2226 (Fin.cases (0 : Fin 2) singletonSmall5202) =
      mixedMoment B node2880 node2880Labels := by
    have ha : raw2226 = raw2227 := by apply Matrix.ext; unfold raw2226 raw2227; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5202 = raw2227Labels := by decide +kernel
    rw [ha, hj, canonical2227 B hB]
  have hc1 : mixedMoment B raw2226 (Fin.cases (1 : Fin 2) singletonSmall5202) =
      mixedMoment B node3617 node3617Labels := by
    have ha : raw2226 = raw2228 := by apply Matrix.ext; unfold raw2226 raw2228; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5202 = raw2228Labels := by decide +kernel
    rw [ha, hj, canonical2228 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5203 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5203 node5203Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2884 node2884Labels + mixedMoment B node3621 node3621Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2229 singletonSmall5203
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5203) = raw2229Labels := by decide +kernel
  rw [hl, canonical2229 B hB] at h
  have hc0 : mixedMoment B raw2229 (Fin.cases (0 : Fin 2) singletonSmall5203) =
      mixedMoment B node2884 node2884Labels := by
    have ha : raw2229 = raw2230 := by apply Matrix.ext; unfold raw2229 raw2230; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5203 = raw2230Labels := by decide +kernel
    rw [ha, hj, canonical2230 B hB]
  have hc1 : mixedMoment B raw2229 (Fin.cases (1 : Fin 2) singletonSmall5203) =
      mixedMoment B node3621 node3621Labels := by
    have ha : raw2229 = raw2231 := by apply Matrix.ext; unfold raw2229 raw2231; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5203 = raw2231Labels := by decide +kernel
    rw [ha, hj, canonical2231 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5204 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5204 node5204Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2881 node2881Labels + mixedMoment B node3624 node3624Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2232 singletonSmall5204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5204) = raw2232Labels := by decide +kernel
  rw [hl, canonical2232 B hB] at h
  have hc0 : mixedMoment B raw2232 (Fin.cases (0 : Fin 2) singletonSmall5204) =
      mixedMoment B node2881 node2881Labels := by
    have ha : raw2232 = raw2233 := by apply Matrix.ext; unfold raw2232 raw2233; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5204 = raw2233Labels := by decide +kernel
    rw [ha, hj, canonical2233 B hB]
  have hc1 : mixedMoment B raw2232 (Fin.cases (1 : Fin 2) singletonSmall5204) =
      mixedMoment B node3624 node3624Labels := by
    have ha : raw2232 = raw2234 := by apply Matrix.ext; unfold raw2232 raw2234; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5204 = raw2234Labels := by decide +kernel
    rw [ha, hj, canonical2234 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5207 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5207 node5207Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2889 node2889Labels + mixedMoment B node3631 node3631Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2235 singletonSmall5207
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5207) = raw2235Labels := by decide +kernel
  rw [hl, canonical2235 B hB] at h
  have hc0 : mixedMoment B raw2235 (Fin.cases (0 : Fin 2) singletonSmall5207) =
      mixedMoment B node2889 node2889Labels := by
    have ha : raw2235 = raw2236 := by apply Matrix.ext; unfold raw2235 raw2236; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5207 = raw2236Labels := by decide +kernel
    rw [ha, hj, canonical2236 B hB]
  have hc1 : mixedMoment B raw2235 (Fin.cases (1 : Fin 2) singletonSmall5207) =
      mixedMoment B node3631 node3631Labels := by
    have ha : raw2235 = raw2237 := by apply Matrix.ext; unfold raw2235 raw2237; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5207 = raw2237Labels := by decide +kernel
    rw [ha, hj, canonical2237 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5212 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5212 node5212Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2839 node2839Labels + mixedMoment B node2839 node2839Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2238 singletonSmall5212
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5212) = raw2238Labels := by decide +kernel
  rw [hl, canonical2238 B hB] at h
  have hc0 : mixedMoment B raw2238 (Fin.cases (0 : Fin 2) singletonSmall5212) =
      mixedMoment B node2839 node2839Labels := by
    have ha : raw2238 = raw2239 := by apply Matrix.ext; unfold raw2238 raw2239; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5212 = raw2239Labels := by decide +kernel
    rw [ha, hj, canonical2239 B hB]
  have hc1 : mixedMoment B raw2238 (Fin.cases (1 : Fin 2) singletonSmall5212) =
      mixedMoment B node2839 node2839Labels := by
    have ha : raw2238 = raw2240 := by apply Matrix.ext; unfold raw2238 raw2240; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5212 = raw2240Labels := by decide +kernel
    rw [ha, hj, canonical2240 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5213 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5213 node5213Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2840 node2840Labels + mixedMoment B node2840 node2840Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2241 singletonSmall5213
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5213) = raw2241Labels := by decide +kernel
  rw [hl, canonical2241 B hB] at h
  have hc0 : mixedMoment B raw2241 (Fin.cases (0 : Fin 2) singletonSmall5213) =
      mixedMoment B node2840 node2840Labels := by
    have ha : raw2241 = raw2242 := by apply Matrix.ext; unfold raw2241 raw2242; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5213 = raw2242Labels := by decide +kernel
    rw [ha, hj, canonical2242 B hB]
  have hc1 : mixedMoment B raw2241 (Fin.cases (1 : Fin 2) singletonSmall5213) =
      mixedMoment B node2840 node2840Labels := by
    have ha : raw2241 = raw2243 := by apply Matrix.ext; unfold raw2241 raw2243; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5213 = raw2243Labels := by decide +kernel
    rw [ha, hj, canonical2243 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5214 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5214 node5214Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2843 node2843Labels + mixedMoment B node2843 node2843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2244 singletonSmall5214
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5214) = raw2244Labels := by decide +kernel
  rw [hl, canonical2244 B hB] at h
  have hc0 : mixedMoment B raw2244 (Fin.cases (0 : Fin 2) singletonSmall5214) =
      mixedMoment B node2843 node2843Labels := by
    have ha : raw2244 = raw2245 := by apply Matrix.ext; unfold raw2244 raw2245; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5214 = raw2245Labels := by decide +kernel
    rw [ha, hj, canonical2245 B hB]
  have hc1 : mixedMoment B raw2244 (Fin.cases (1 : Fin 2) singletonSmall5214) =
      mixedMoment B node2843 node2843Labels := by
    have ha : raw2244 = raw2246 := by apply Matrix.ext; unfold raw2244 raw2246; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5214 = raw2246Labels := by decide +kernel
    rw [ha, hj, canonical2246 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5227 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5227 node5227Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2671 node2671Labels + mixedMoment B node3390 node3390Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2247 singletonSmall5227
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5227) = raw2247Labels := by decide +kernel
  rw [hl, canonical2247 B hB] at h
  have hc0 : mixedMoment B raw2247 (Fin.cases (0 : Fin 2) singletonSmall5227) =
      mixedMoment B node2671 node2671Labels := by
    have ha : raw2247 = raw2248 := by apply Matrix.ext; unfold raw2247 raw2248; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5227 = raw2248Labels := by decide +kernel
    rw [ha, hj, canonical2248 B hB]
  have hc1 : mixedMoment B raw2247 (Fin.cases (1 : Fin 2) singletonSmall5227) =
      mixedMoment B node3390 node3390Labels := by
    have ha : raw2247 = raw2249 := by apply Matrix.ext; unfold raw2247 raw2249; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5227 = raw2249Labels := by decide +kernel
    rw [ha, hj, canonical2249 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5228 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5228 node5228Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2672 node2672Labels + mixedMoment B node3391 node3391Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2250 singletonSmall5228
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5228) = raw2250Labels := by decide +kernel
  rw [hl, canonical2250 B hB] at h
  have hc0 : mixedMoment B raw2250 (Fin.cases (0 : Fin 2) singletonSmall5228) =
      mixedMoment B node2672 node2672Labels := by
    have ha : raw2250 = raw2251 := by apply Matrix.ext; unfold raw2250 raw2251; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5228 = raw2251Labels := by decide +kernel
    rw [ha, hj, canonical2251 B hB]
  have hc1 : mixedMoment B raw2250 (Fin.cases (1 : Fin 2) singletonSmall5228) =
      mixedMoment B node3391 node3391Labels := by
    have ha : raw2250 = raw2252 := by apply Matrix.ext; unfold raw2250 raw2252; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5228 = raw2252Labels := by decide +kernel
    rw [ha, hj, canonical2252 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5237 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5237 node5237Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2684 node2684Labels + mixedMoment B node3394 node3394Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2253 singletonSmall5237
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5237) = raw2253Labels := by decide +kernel
  rw [hl, canonical2253 B hB] at h
  have hc0 : mixedMoment B raw2253 (Fin.cases (0 : Fin 2) singletonSmall5237) =
      mixedMoment B node2684 node2684Labels := by
    have ha : raw2253 = raw2254 := by apply Matrix.ext; unfold raw2253 raw2254; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5237 = raw2254Labels := by decide +kernel
    rw [ha, hj, canonical2254 B hB]
  have hc1 : mixedMoment B raw2253 (Fin.cases (1 : Fin 2) singletonSmall5237) =
      mixedMoment B node3394 node3394Labels := by
    have ha : raw2253 = raw2255 := by apply Matrix.ext; unfold raw2253 raw2255; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5237 = raw2255Labels := by decide +kernel
    rw [ha, hj, canonical2255 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5238 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5238 node5238Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2686 node2686Labels + mixedMoment B node3397 node3397Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2256 singletonSmall5238
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5238) = raw2256Labels := by decide +kernel
  rw [hl, canonical2256 B hB] at h
  have hc0 : mixedMoment B raw2256 (Fin.cases (0 : Fin 2) singletonSmall5238) =
      mixedMoment B node2686 node2686Labels := by
    have ha : raw2256 = raw2257 := by apply Matrix.ext; unfold raw2256 raw2257; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5238 = raw2257Labels := by decide +kernel
    rw [ha, hj, canonical2257 B hB]
  have hc1 : mixedMoment B raw2256 (Fin.cases (1 : Fin 2) singletonSmall5238) =
      mixedMoment B node3397 node3397Labels := by
    have ha : raw2256 = raw2258 := by apply Matrix.ext; unfold raw2256 raw2258; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5238 = raw2258Labels := by decide +kernel
    rw [ha, hj, canonical2258 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5241 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5241 node5241Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2694 node2694Labels + mixedMoment B node3493 node3493Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2259 singletonSmall5241
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5241) = raw2259Labels := by decide +kernel
  rw [hl, canonical2259 B hB] at h
  have hc0 : mixedMoment B raw2259 (Fin.cases (0 : Fin 2) singletonSmall5241) =
      mixedMoment B node2694 node2694Labels := by
    have ha : raw2259 = raw2260 := by apply Matrix.ext; unfold raw2259 raw2260; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5241 = raw2260Labels := by decide +kernel
    rw [ha, hj, canonical2260 B hB]
  have hc1 : mixedMoment B raw2259 (Fin.cases (1 : Fin 2) singletonSmall5241) =
      mixedMoment B node3493 node3493Labels := by
    have ha : raw2259 = raw2261 := by apply Matrix.ext; unfold raw2259 raw2261; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5241 = raw2261Labels := by decide +kernel
    rw [ha, hj, canonical2261 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5247 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5247 node5247Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2703 node2703Labels + mixedMoment B node3496 node3496Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2262 singletonSmall5247
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5247) = raw2262Labels := by decide +kernel
  rw [hl, canonical2262 B hB] at h
  have hc0 : mixedMoment B raw2262 (Fin.cases (0 : Fin 2) singletonSmall5247) =
      mixedMoment B node2703 node2703Labels := by
    have ha : raw2262 = raw2263 := by apply Matrix.ext; unfold raw2262 raw2263; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5247 = raw2263Labels := by decide +kernel
    rw [ha, hj, canonical2263 B hB]
  have hc1 : mixedMoment B raw2262 (Fin.cases (1 : Fin 2) singletonSmall5247) =
      mixedMoment B node3496 node3496Labels := by
    have ha : raw2262 = raw2264 := by apply Matrix.ext; unfold raw2262 raw2264; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5247 = raw2264Labels := by decide +kernel
    rw [ha, hj, canonical2264 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

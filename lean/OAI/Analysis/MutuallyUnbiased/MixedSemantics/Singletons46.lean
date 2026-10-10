import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical2

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2948 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2948 node2948Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node202 node202Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw312 singletonSmall2948
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2948) = raw312Labels := by decide +kernel
  rw [hl, canonical312 B hB] at h
  have hc0 : mixedMoment B raw312 (Fin.cases (0 : Fin 1) singletonSmall2948) =
      mixedMoment B node202 node202Labels := by
    have ha : raw312 = raw313 := by apply Matrix.ext; unfold raw312 raw313; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2948 = raw313Labels := by decide +kernel
    rw [ha, hj, canonical313 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2957 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2957 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2957 node2957Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node331 node331Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw314 singletonSmall2957
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2957) = raw314Labels := by decide +kernel
  rw [hl, canonical314 B hB] at h
  have hc0 : mixedMoment B raw314 (Fin.cases (0 : Fin 1) singletonSmall2957) =
      mixedMoment B node331 node331Labels := by
    have ha : raw314 = raw315 := by apply Matrix.ext; unfold raw314 raw315; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2957 = raw315Labels := by decide +kernel
    rw [ha, hj, canonical315 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2958 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2958 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2958 node2958Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node334 node334Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw316 singletonSmall2958
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2958) = raw316Labels := by decide +kernel
  rw [hl, canonical316 B hB] at h
  have hc0 : mixedMoment B raw316 (Fin.cases (0 : Fin 1) singletonSmall2958) =
      mixedMoment B node334 node334Labels := by
    have ha : raw316 = raw317 := by apply Matrix.ext; unfold raw316 raw317; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2958 = raw317Labels := by decide +kernel
    rw [ha, hj, canonical317 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2959 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2959 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2959 node2959Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node339 node339Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw318 singletonSmall2959
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2959) = raw318Labels := by decide +kernel
  rw [hl, canonical318 B hB] at h
  have hc0 : mixedMoment B raw318 (Fin.cases (0 : Fin 1) singletonSmall2959) =
      mixedMoment B node339 node339Labels := by
    have ha : raw318 = raw319 := by apply Matrix.ext; unfold raw318 raw319; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2959 = raw319Labels := by decide +kernel
    rw [ha, hj, canonical319 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2960 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2960 node2960Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node336 node336Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw320 singletonSmall2960
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2960) = raw320Labels := by decide +kernel
  rw [hl, canonical320 B hB] at h
  have hc0 : mixedMoment B raw320 (Fin.cases (0 : Fin 1) singletonSmall2960) =
      mixedMoment B node336 node336Labels := by
    have ha : raw320 = raw321 := by apply Matrix.ext; unfold raw320 raw321; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2960 = raw321Labels := by decide +kernel
    rw [ha, hj, canonical321 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2961 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2961 node2961Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node332 node332Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw322 singletonSmall2961
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2961) = raw322Labels := by decide +kernel
  rw [hl, canonical322 B hB] at h
  have hc0 : mixedMoment B raw322 (Fin.cases (0 : Fin 1) singletonSmall2961) =
      mixedMoment B node332 node332Labels := by
    have ha : raw322 = raw323 := by apply Matrix.ext; unfold raw322 raw323; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2961 = raw323Labels := by decide +kernel
    rw [ha, hj, canonical323 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2963 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2963 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2963 node2963Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node335 node335Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw324 singletonSmall2963
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2963) = raw324Labels := by decide +kernel
  rw [hl, canonical324 B hB] at h
  have hc0 : mixedMoment B raw324 (Fin.cases (0 : Fin 1) singletonSmall2963) =
      mixedMoment B node335 node335Labels := by
    have ha : raw324 = raw325 := by apply Matrix.ext; unfold raw324 raw325; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2963 = raw325Labels := by decide +kernel
    rw [ha, hj, canonical325 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2965 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2965 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2965 node2965Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node338 node338Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw326 singletonSmall2965
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2965) = raw326Labels := by decide +kernel
  rw [hl, canonical326 B hB] at h
  have hc0 : mixedMoment B raw326 (Fin.cases (0 : Fin 1) singletonSmall2965) =
      mixedMoment B node338 node338Labels := by
    have ha : raw326 = raw327 := by apply Matrix.ext; unfold raw326 raw327; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2965 = raw327Labels := by decide +kernel
    rw [ha, hj, canonical327 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2966 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2966 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2966 node2966Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node247 node247Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw328 singletonSmall2966
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2966) = raw328Labels := by decide +kernel
  rw [hl, canonical328 B hB] at h
  have hc0 : mixedMoment B raw328 (Fin.cases (0 : Fin 1) singletonSmall2966) =
      mixedMoment B node247 node247Labels := by
    have ha : raw328 = raw329 := by apply Matrix.ext; unfold raw328 raw329; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2966 = raw329Labels := by decide +kernel
    rw [ha, hj, canonical329 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2968 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2968 node2968Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node343 node343Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw330 singletonSmall2968
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2968) = raw330Labels := by decide +kernel
  rw [hl, canonical330 B hB] at h
  have hc0 : mixedMoment B raw330 (Fin.cases (0 : Fin 1) singletonSmall2968) =
      mixedMoment B node343 node343Labels := by
    have ha : raw330 = raw331 := by apply Matrix.ext; unfold raw330 raw331; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2968 = raw331Labels := by decide +kernel
    rw [ha, hj, canonical331 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2969 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2969 node2969Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node344 node344Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw332 singletonSmall2969
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2969) = raw332Labels := by decide +kernel
  rw [hl, canonical332 B hB] at h
  have hc0 : mixedMoment B raw332 (Fin.cases (0 : Fin 1) singletonSmall2969) =
      mixedMoment B node344 node344Labels := by
    have ha : raw332 = raw333 := by apply Matrix.ext; unfold raw332 raw333; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2969 = raw333Labels := by decide +kernel
    rw [ha, hj, canonical333 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2982 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2982 node2982Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node216 node216Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw334 singletonSmall2982
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2982) = raw334Labels := by decide +kernel
  rw [hl, canonical334 B hB] at h
  have hc0 : mixedMoment B raw334 (Fin.cases (0 : Fin 1) singletonSmall2982) =
      mixedMoment B node216 node216Labels := by
    have ha : raw334 = raw335 := by apply Matrix.ext; unfold raw334 raw335; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2982 = raw335Labels := by decide +kernel
    rw [ha, hj, canonical335 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2986 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2986 node2986Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node304 node304Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw336 singletonSmall2986
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2986) = raw336Labels := by decide +kernel
  rw [hl, canonical336 B hB] at h
  have hc0 : mixedMoment B raw336 (Fin.cases (0 : Fin 1) singletonSmall2986) =
      mixedMoment B node304 node304Labels := by
    have ha : raw336 = raw337 := by apply Matrix.ext; unfold raw336 raw337; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2986 = raw337Labels := by decide +kernel
    rw [ha, hj, canonical337 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2987 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2987 node2987Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node302 node302Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw338 singletonSmall2987
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2987) = raw338Labels := by decide +kernel
  rw [hl, canonical338 B hB] at h
  have hc0 : mixedMoment B raw338 (Fin.cases (0 : Fin 1) singletonSmall2987) =
      mixedMoment B node302 node302Labels := by
    have ha : raw338 = raw339 := by apply Matrix.ext; unfold raw338 raw339; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2987 = raw339Labels := by decide +kernel
    rw [ha, hj, canonical339 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2988 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2988 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2988 node2988Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node301 node301Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw340 singletonSmall2988
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2988) = raw340Labels := by decide +kernel
  rw [hl, canonical340 B hB] at h
  have hc0 : mixedMoment B raw340 (Fin.cases (0 : Fin 1) singletonSmall2988) =
      mixedMoment B node301 node301Labels := by
    have ha : raw340 = raw341 := by apply Matrix.ext; unfold raw340 raw341; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2988 = raw341Labels := by decide +kernel
    rw [ha, hj, canonical341 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2989 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2989 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2989 node2989Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node230 node230Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw342 singletonSmall2989
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2989) = raw342Labels := by decide +kernel
  rw [hl, canonical342 B hB] at h
  have hc0 : mixedMoment B raw342 (Fin.cases (0 : Fin 1) singletonSmall2989) =
      mixedMoment B node230 node230Labels := by
    have ha : raw342 = raw343 := by apply Matrix.ext; unfold raw342 raw343; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2989 = raw343Labels := by decide +kernel
    rw [ha, hj, canonical343 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2990 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2990 node2990Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node306 node306Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw344 singletonSmall2990
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2990) = raw344Labels := by decide +kernel
  rw [hl, canonical344 B hB] at h
  have hc0 : mixedMoment B raw344 (Fin.cases (0 : Fin 1) singletonSmall2990) =
      mixedMoment B node306 node306Labels := by
    have ha : raw344 = raw345 := by apply Matrix.ext; unfold raw344 raw345; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2990 = raw345Labels := by decide +kernel
    rw [ha, hj, canonical345 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2991 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2991 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2991 node2991Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node307 node307Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw346 singletonSmall2991
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2991) = raw346Labels := by decide +kernel
  rw [hl, canonical346 B hB] at h
  have hc0 : mixedMoment B raw346 (Fin.cases (0 : Fin 1) singletonSmall2991) =
      mixedMoment B node307 node307Labels := by
    have ha : raw346 = raw347 := by apply Matrix.ext; unfold raw346 raw347; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2991 = raw347Labels := by decide +kernel
    rw [ha, hj, canonical347 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2996 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2996 node2996Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node310 node310Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw348 singletonSmall2996
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2996) = raw348Labels := by decide +kernel
  rw [hl, canonical348 B hB] at h
  have hc0 : mixedMoment B raw348 (Fin.cases (0 : Fin 1) singletonSmall2996) =
      mixedMoment B node310 node310Labels := by
    have ha : raw348 = raw349 := by apply Matrix.ext; unfold raw348 raw349; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2996 = raw349Labels := by decide +kernel
    rw [ha, hj, canonical349 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2997 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2997 node2997Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node314 node314Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw350 singletonSmall2997
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2997) = raw350Labels := by decide +kernel
  rw [hl, canonical350 B hB] at h
  have hc0 : mixedMoment B raw350 (Fin.cases (0 : Fin 1) singletonSmall2997) =
      mixedMoment B node314 node314Labels := by
    have ha : raw350 = raw351 := by apply Matrix.ext; unfold raw350 raw351; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2997 = raw351Labels := by decide +kernel
    rw [ha, hj, canonical351 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2998 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2998 node2998Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node312 node312Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw352 singletonSmall2998
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2998) = raw352Labels := by decide +kernel
  rw [hl, canonical352 B hB] at h
  have hc0 : mixedMoment B raw352 (Fin.cases (0 : Fin 1) singletonSmall2998) =
      mixedMoment B node312 node312Labels := by
    have ha : raw352 = raw353 := by apply Matrix.ext; unfold raw352 raw353; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2998 = raw353Labels := by decide +kernel
    rw [ha, hj, canonical353 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3003 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3003 node3003Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node311 node311Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw354 singletonSmall3003
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3003) = raw354Labels := by decide +kernel
  rw [hl, canonical354 B hB] at h
  have hc0 : mixedMoment B raw354 (Fin.cases (0 : Fin 1) singletonSmall3003) =
      mixedMoment B node311 node311Labels := by
    have ha : raw354 = raw355 := by apply Matrix.ext; unfold raw354 raw355; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3003 = raw355Labels := by decide +kernel
    rw [ha, hj, canonical355 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3005 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3005 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3005 node3005Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node316 node316Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw356 singletonSmall3005
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3005) = raw356Labels := by decide +kernel
  rw [hl, canonical356 B hB] at h
  have hc0 : mixedMoment B raw356 (Fin.cases (0 : Fin 1) singletonSmall3005) =
      mixedMoment B node316 node316Labels := by
    have ha : raw356 = raw357 := by apply Matrix.ext; unfold raw356 raw357; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3005 = raw357Labels := by decide +kernel
    rw [ha, hj, canonical357 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

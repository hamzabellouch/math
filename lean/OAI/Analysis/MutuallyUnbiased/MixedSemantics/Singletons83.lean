import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical18

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5315 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5315 node5315Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3638 node3638Labels + mixedMoment B node3643 node3643Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2328 singletonSmall5315
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5315) = raw2328Labels := by decide +kernel
  rw [hl, canonical2328 B hB] at h
  have hc0 : mixedMoment B raw2328 (Fin.cases (0 : Fin 2) singletonSmall5315) =
      mixedMoment B node3638 node3638Labels := by
    have ha : raw2328 = raw2329 := by apply Matrix.ext; unfold raw2328 raw2329; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5315 = raw2329Labels := by decide +kernel
    rw [ha, hj, canonical2329 B hB]
  have hc1 : mixedMoment B raw2328 (Fin.cases (1 : Fin 2) singletonSmall5315) =
      mixedMoment B node3643 node3643Labels := by
    have ha : raw2328 = raw2330 := by apply Matrix.ext; unfold raw2328 raw2330; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5315 = raw2330Labels := by decide +kernel
    rw [ha, hj, canonical2330 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5316 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5316 node5316Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3639 node3639Labels + mixedMoment B node3645 node3645Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2331 singletonSmall5316
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5316) = raw2331Labels := by decide +kernel
  rw [hl, canonical2331 B hB] at h
  have hc0 : mixedMoment B raw2331 (Fin.cases (0 : Fin 2) singletonSmall5316) =
      mixedMoment B node3639 node3639Labels := by
    have ha : raw2331 = raw2332 := by apply Matrix.ext; unfold raw2331 raw2332; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5316 = raw2332Labels := by decide +kernel
    rw [ha, hj, canonical2332 B hB]
  have hc1 : mixedMoment B raw2331 (Fin.cases (1 : Fin 2) singletonSmall5316) =
      mixedMoment B node3645 node3645Labels := by
    have ha : raw2331 = raw2333 := by apply Matrix.ext; unfold raw2331 raw2333; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5316 = raw2333Labels := by decide +kernel
    rw [ha, hj, canonical2333 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5317 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5317 node5317Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3640 node3640Labels + mixedMoment B node3649 node3649Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2334 singletonSmall5317
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5317) = raw2334Labels := by decide +kernel
  rw [hl, canonical2334 B hB] at h
  have hc0 : mixedMoment B raw2334 (Fin.cases (0 : Fin 2) singletonSmall5317) =
      mixedMoment B node3640 node3640Labels := by
    have ha : raw2334 = raw2335 := by apply Matrix.ext; unfold raw2334 raw2335; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5317 = raw2335Labels := by decide +kernel
    rw [ha, hj, canonical2335 B hB]
  have hc1 : mixedMoment B raw2334 (Fin.cases (1 : Fin 2) singletonSmall5317) =
      mixedMoment B node3649 node3649Labels := by
    have ha : raw2334 = raw2336 := by apply Matrix.ext; unfold raw2334 raw2336; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5317 = raw2336Labels := by decide +kernel
    rw [ha, hj, canonical2336 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5318 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5318 node5318Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3641 node3641Labels + mixedMoment B node3655 node3655Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2337 singletonSmall5318
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5318) = raw2337Labels := by decide +kernel
  rw [hl, canonical2337 B hB] at h
  have hc0 : mixedMoment B raw2337 (Fin.cases (0 : Fin 2) singletonSmall5318) =
      mixedMoment B node3641 node3641Labels := by
    have ha : raw2337 = raw2338 := by apply Matrix.ext; unfold raw2337 raw2338; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5318 = raw2338Labels := by decide +kernel
    rw [ha, hj, canonical2338 B hB]
  have hc1 : mixedMoment B raw2337 (Fin.cases (1 : Fin 2) singletonSmall5318) =
      mixedMoment B node3655 node3655Labels := by
    have ha : raw2337 = raw2339 := by apply Matrix.ext; unfold raw2337 raw2339; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5318 = raw2339Labels := by decide +kernel
    rw [ha, hj, canonical2339 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5319 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5319 node5319Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3642 node3642Labels + mixedMoment B node3662 node3662Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2340 singletonSmall5319
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5319) = raw2340Labels := by decide +kernel
  rw [hl, canonical2340 B hB] at h
  have hc0 : mixedMoment B raw2340 (Fin.cases (0 : Fin 2) singletonSmall5319) =
      mixedMoment B node3642 node3642Labels := by
    have ha : raw2340 = raw2341 := by apply Matrix.ext; unfold raw2340 raw2341; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5319 = raw2341Labels := by decide +kernel
    rw [ha, hj, canonical2341 B hB]
  have hc1 : mixedMoment B raw2340 (Fin.cases (1 : Fin 2) singletonSmall5319) =
      mixedMoment B node3662 node3662Labels := by
    have ha : raw2340 = raw2342 := by apply Matrix.ext; unfold raw2340 raw2342; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5319 = raw2342Labels := by decide +kernel
    rw [ha, hj, canonical2342 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5320 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5320 node5320Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3646 node3646Labels + mixedMoment B node3656 node3656Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2343 singletonSmall5320
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5320) = raw2343Labels := by decide +kernel
  rw [hl, canonical2343 B hB] at h
  have hc0 : mixedMoment B raw2343 (Fin.cases (0 : Fin 2) singletonSmall5320) =
      mixedMoment B node3646 node3646Labels := by
    have ha : raw2343 = raw2344 := by apply Matrix.ext; unfold raw2343 raw2344; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5320 = raw2344Labels := by decide +kernel
    rw [ha, hj, canonical2344 B hB]
  have hc1 : mixedMoment B raw2343 (Fin.cases (1 : Fin 2) singletonSmall5320) =
      mixedMoment B node3656 node3656Labels := by
    have ha : raw2343 = raw2345 := by apply Matrix.ext; unfold raw2343 raw2345; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5320 = raw2345Labels := by decide +kernel
    rw [ha, hj, canonical2345 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5321 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5321 node5321Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3647 node3647Labels + mixedMoment B node3663 node3663Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2346 singletonSmall5321
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5321) = raw2346Labels := by decide +kernel
  rw [hl, canonical2346 B hB] at h
  have hc0 : mixedMoment B raw2346 (Fin.cases (0 : Fin 2) singletonSmall5321) =
      mixedMoment B node3647 node3647Labels := by
    have ha : raw2346 = raw2347 := by apply Matrix.ext; unfold raw2346 raw2347; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5321 = raw2347Labels := by decide +kernel
    rw [ha, hj, canonical2347 B hB]
  have hc1 : mixedMoment B raw2346 (Fin.cases (1 : Fin 2) singletonSmall5321) =
      mixedMoment B node3663 node3663Labels := by
    have ha : raw2346 = raw2348 := by apply Matrix.ext; unfold raw2346 raw2348; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5321 = raw2348Labels := by decide +kernel
    rw [ha, hj, canonical2348 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5324 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5324 node5324Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3651 node3651Labels + mixedMoment B node3651 node3651Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2349 singletonSmall5324
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5324) = raw2349Labels := by decide +kernel
  rw [hl, canonical2349 B hB] at h
  have hc0 : mixedMoment B raw2349 (Fin.cases (0 : Fin 2) singletonSmall5324) =
      mixedMoment B node3651 node3651Labels := by
    have ha : raw2349 = raw2350 := by apply Matrix.ext; unfold raw2349 raw2350; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5324 = raw2350Labels := by decide +kernel
    rw [ha, hj, canonical2350 B hB]
  have hc1 : mixedMoment B raw2349 (Fin.cases (1 : Fin 2) singletonSmall5324) =
      mixedMoment B node3651 node3651Labels := by
    have ha : raw2349 = raw2351 := by apply Matrix.ext; unfold raw2349 raw2351; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5324 = raw2351Labels := by decide +kernel
    rw [ha, hj, canonical2351 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5326 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5326 node5326Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3653 node3653Labels + mixedMoment B node3657 node3657Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2352 singletonSmall5326
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5326) = raw2352Labels := by decide +kernel
  rw [hl, canonical2352 B hB] at h
  have hc0 : mixedMoment B raw2352 (Fin.cases (0 : Fin 2) singletonSmall5326) =
      mixedMoment B node3653 node3653Labels := by
    have ha : raw2352 = raw2353 := by apply Matrix.ext; unfold raw2352 raw2353; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5326 = raw2353Labels := by decide +kernel
    rw [ha, hj, canonical2353 B hB]
  have hc1 : mixedMoment B raw2352 (Fin.cases (1 : Fin 2) singletonSmall5326) =
      mixedMoment B node3657 node3657Labels := by
    have ha : raw2352 = raw2354 := by apply Matrix.ext; unfold raw2352 raw2354; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5326 = raw2354Labels := by decide +kernel
    rw [ha, hj, canonical2354 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5328 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5328 node5328Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3659 node3659Labels + mixedMoment B node3659 node3659Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2355 singletonSmall5328
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5328) = raw2355Labels := by decide +kernel
  rw [hl, canonical2355 B hB] at h
  have hc0 : mixedMoment B raw2355 (Fin.cases (0 : Fin 2) singletonSmall5328) =
      mixedMoment B node3659 node3659Labels := by
    have ha : raw2355 = raw2356 := by apply Matrix.ext; unfold raw2355 raw2356; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5328 = raw2356Labels := by decide +kernel
    rw [ha, hj, canonical2356 B hB]
  have hc1 : mixedMoment B raw2355 (Fin.cases (1 : Fin 2) singletonSmall5328) =
      mixedMoment B node3659 node3659Labels := by
    have ha : raw2355 = raw2357 := by apply Matrix.ext; unfold raw2355 raw2357; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5328 = raw2357Labels := by decide +kernel
    rw [ha, hj, canonical2357 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5329 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5329 node5329Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3660 node3660Labels + mixedMoment B node3660 node3660Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2358 singletonSmall5329
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5329) = raw2358Labels := by decide +kernel
  rw [hl, canonical2358 B hB] at h
  have hc0 : mixedMoment B raw2358 (Fin.cases (0 : Fin 2) singletonSmall5329) =
      mixedMoment B node3660 node3660Labels := by
    have ha : raw2358 = raw2359 := by apply Matrix.ext; unfold raw2358 raw2359; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5329 = raw2359Labels := by decide +kernel
    rw [ha, hj, canonical2359 B hB]
  have hc1 : mixedMoment B raw2358 (Fin.cases (1 : Fin 2) singletonSmall5329) =
      mixedMoment B node3660 node3660Labels := by
    have ha : raw2358 = raw2360 := by apply Matrix.ext; unfold raw2358 raw2360; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5329 = raw2360Labels := by decide +kernel
    rw [ha, hj, canonical2360 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5330 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5330 node5330Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3661 node3661Labels + mixedMoment B node3666 node3666Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2361 singletonSmall5330
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5330) = raw2361Labels := by decide +kernel
  rw [hl, canonical2361 B hB] at h
  have hc0 : mixedMoment B raw2361 (Fin.cases (0 : Fin 2) singletonSmall5330) =
      mixedMoment B node3661 node3661Labels := by
    have ha : raw2361 = raw2362 := by apply Matrix.ext; unfold raw2361 raw2362; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5330 = raw2362Labels := by decide +kernel
    rw [ha, hj, canonical2362 B hB]
  have hc1 : mixedMoment B raw2361 (Fin.cases (1 : Fin 2) singletonSmall5330) =
      mixedMoment B node3666 node3666Labels := by
    have ha : raw2361 = raw2363 := by apply Matrix.ext; unfold raw2361 raw2363; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5330 = raw2363Labels := by decide +kernel
    rw [ha, hj, canonical2363 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5333 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5333 node5333Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3668 node3668Labels + mixedMoment B node3677 node3677Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2364 singletonSmall5333
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5333) = raw2364Labels := by decide +kernel
  rw [hl, canonical2364 B hB] at h
  have hc0 : mixedMoment B raw2364 (Fin.cases (0 : Fin 2) singletonSmall5333) =
      mixedMoment B node3668 node3668Labels := by
    have ha : raw2364 = raw2365 := by apply Matrix.ext; unfold raw2364 raw2365; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5333 = raw2365Labels := by decide +kernel
    rw [ha, hj, canonical2365 B hB]
  have hc1 : mixedMoment B raw2364 (Fin.cases (1 : Fin 2) singletonSmall5333) =
      mixedMoment B node3677 node3677Labels := by
    have ha : raw2364 = raw2366 := by apply Matrix.ext; unfold raw2364 raw2366; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5333 = raw2366Labels := by decide +kernel
    rw [ha, hj, canonical2366 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5334 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5334 node5334Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3669 node3669Labels + mixedMoment B node3742 node3742Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2367 singletonSmall5334
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5334) = raw2367Labels := by decide +kernel
  rw [hl, canonical2367 B hB] at h
  have hc0 : mixedMoment B raw2367 (Fin.cases (0 : Fin 2) singletonSmall5334) =
      mixedMoment B node3669 node3669Labels := by
    have ha : raw2367 = raw2368 := by apply Matrix.ext; unfold raw2367 raw2368; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5334 = raw2368Labels := by decide +kernel
    rw [ha, hj, canonical2368 B hB]
  have hc1 : mixedMoment B raw2367 (Fin.cases (1 : Fin 2) singletonSmall5334) =
      mixedMoment B node3742 node3742Labels := by
    have ha : raw2367 = raw2369 := by apply Matrix.ext; unfold raw2367 raw2369; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5334 = raw2369Labels := by decide +kernel
    rw [ha, hj, canonical2369 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5335 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5335 node5335Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3670 node3670Labels + mixedMoment B node3753 node3753Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2370 singletonSmall5335
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5335) = raw2370Labels := by decide +kernel
  rw [hl, canonical2370 B hB] at h
  have hc0 : mixedMoment B raw2370 (Fin.cases (0 : Fin 2) singletonSmall5335) =
      mixedMoment B node3670 node3670Labels := by
    have ha : raw2370 = raw2371 := by apply Matrix.ext; unfold raw2370 raw2371; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5335 = raw2371Labels := by decide +kernel
    rw [ha, hj, canonical2371 B hB]
  have hc1 : mixedMoment B raw2370 (Fin.cases (1 : Fin 2) singletonSmall5335) =
      mixedMoment B node3753 node3753Labels := by
    have ha : raw2370 = raw2372 := by apply Matrix.ext; unfold raw2370 raw2372; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5335 = raw2372Labels := by decide +kernel
    rw [ha, hj, canonical2372 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5336 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5336 node5336Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3671 node3671Labels + mixedMoment B node3754 node3754Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2373 singletonSmall5336
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5336) = raw2373Labels := by decide +kernel
  rw [hl, canonical2373 B hB] at h
  have hc0 : mixedMoment B raw2373 (Fin.cases (0 : Fin 2) singletonSmall5336) =
      mixedMoment B node3671 node3671Labels := by
    have ha : raw2373 = raw2374 := by apply Matrix.ext; unfold raw2373 raw2374; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5336 = raw2374Labels := by decide +kernel
    rw [ha, hj, canonical2374 B hB]
  have hc1 : mixedMoment B raw2373 (Fin.cases (1 : Fin 2) singletonSmall5336) =
      mixedMoment B node3754 node3754Labels := by
    have ha : raw2373 = raw2375 := by apply Matrix.ext; unfold raw2373 raw2375; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5336 = raw2375Labels := by decide +kernel
    rw [ha, hj, canonical2375 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5337 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5337 node5337Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3672 node3672Labels + mixedMoment B node3756 node3756Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2376 singletonSmall5337
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5337) = raw2376Labels := by decide +kernel
  rw [hl, canonical2376 B hB] at h
  have hc0 : mixedMoment B raw2376 (Fin.cases (0 : Fin 2) singletonSmall5337) =
      mixedMoment B node3672 node3672Labels := by
    have ha : raw2376 = raw2377 := by apply Matrix.ext; unfold raw2376 raw2377; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5337 = raw2377Labels := by decide +kernel
    rw [ha, hj, canonical2377 B hB]
  have hc1 : mixedMoment B raw2376 (Fin.cases (1 : Fin 2) singletonSmall5337) =
      mixedMoment B node3756 node3756Labels := by
    have ha : raw2376 = raw2378 := by apply Matrix.ext; unfold raw2376 raw2378; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5337 = raw2378Labels := by decide +kernel
    rw [ha, hj, canonical2378 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5341 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5341 node5341Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3678 node3678Labels + mixedMoment B node3744 node3744Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2379 singletonSmall5341
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5341) = raw2379Labels := by decide +kernel
  rw [hl, canonical2379 B hB] at h
  have hc0 : mixedMoment B raw2379 (Fin.cases (0 : Fin 2) singletonSmall5341) =
      mixedMoment B node3678 node3678Labels := by
    have ha : raw2379 = raw2380 := by apply Matrix.ext; unfold raw2379 raw2380; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5341 = raw2380Labels := by decide +kernel
    rw [ha, hj, canonical2380 B hB]
  have hc1 : mixedMoment B raw2379 (Fin.cases (1 : Fin 2) singletonSmall5341) =
      mixedMoment B node3744 node3744Labels := by
    have ha : raw2379 = raw2381 := by apply Matrix.ext; unfold raw2379 raw2381; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5341 = raw2381Labels := by decide +kernel
    rw [ha, hj, canonical2381 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5344 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5344 node5344Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3681 node3681Labels + mixedMoment B node3681 node3681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2382 singletonSmall5344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5344) = raw2382Labels := by decide +kernel
  rw [hl, canonical2382 B hB] at h
  have hc0 : mixedMoment B raw2382 (Fin.cases (0 : Fin 2) singletonSmall5344) =
      mixedMoment B node3681 node3681Labels := by
    have ha : raw2382 = raw2383 := by apply Matrix.ext; unfold raw2382 raw2383; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5344 = raw2383Labels := by decide +kernel
    rw [ha, hj, canonical2383 B hB]
  have hc1 : mixedMoment B raw2382 (Fin.cases (1 : Fin 2) singletonSmall5344) =
      mixedMoment B node3681 node3681Labels := by
    have ha : raw2382 = raw2384 := by apply Matrix.ext; unfold raw2382 raw2384; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5344 = raw2384Labels := by decide +kernel
    rw [ha, hj, canonical2384 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5346 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5346 node5346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3683 node3683Labels + mixedMoment B node3746 node3746Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2385 singletonSmall5346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5346) = raw2385Labels := by decide +kernel
  rw [hl, canonical2385 B hB] at h
  have hc0 : mixedMoment B raw2385 (Fin.cases (0 : Fin 2) singletonSmall5346) =
      mixedMoment B node3683 node3683Labels := by
    have ha : raw2385 = raw2386 := by apply Matrix.ext; unfold raw2385 raw2386; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5346 = raw2386Labels := by decide +kernel
    rw [ha, hj, canonical2386 B hB]
  have hc1 : mixedMoment B raw2385 (Fin.cases (1 : Fin 2) singletonSmall5346) =
      mixedMoment B node3746 node3746Labels := by
    have ha : raw2385 = raw2387 := by apply Matrix.ext; unfold raw2385 raw2387; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5346 = raw2387Labels := by decide +kernel
    rw [ha, hj, canonical2387 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5349 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5349 node5349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3687 node3687Labels + mixedMoment B node3749 node3749Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2388 singletonSmall5349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5349) = raw2388Labels := by decide +kernel
  rw [hl, canonical2388 B hB] at h
  have hc0 : mixedMoment B raw2388 (Fin.cases (0 : Fin 2) singletonSmall5349) =
      mixedMoment B node3687 node3687Labels := by
    have ha : raw2388 = raw2389 := by apply Matrix.ext; unfold raw2388 raw2389; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5349 = raw2389Labels := by decide +kernel
    rw [ha, hj, canonical2389 B hB]
  have hc1 : mixedMoment B raw2388 (Fin.cases (1 : Fin 2) singletonSmall5349) =
      mixedMoment B node3749 node3749Labels := by
    have ha : raw2388 = raw2390 := by apply Matrix.ext; unfold raw2388 raw2390; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5349 = raw2390Labels := by decide +kernel
    rw [ha, hj, canonical2390 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5351 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5351 node5351Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3689 node3689Labels + mixedMoment B node3757 node3757Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2391 singletonSmall5351
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5351) = raw2391Labels := by decide +kernel
  rw [hl, canonical2391 B hB] at h
  have hc0 : mixedMoment B raw2391 (Fin.cases (0 : Fin 2) singletonSmall5351) =
      mixedMoment B node3689 node3689Labels := by
    have ha : raw2391 = raw2392 := by apply Matrix.ext; unfold raw2391 raw2392; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5351 = raw2392Labels := by decide +kernel
    rw [ha, hj, canonical2392 B hB]
  have hc1 : mixedMoment B raw2391 (Fin.cases (1 : Fin 2) singletonSmall5351) =
      mixedMoment B node3757 node3757Labels := by
    have ha : raw2391 = raw2393 := by apply Matrix.ext; unfold raw2391 raw2393; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5351 = raw2393Labels := by decide +kernel
    rw [ha, hj, canonical2393 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5352 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5352 node5352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3690 node3690Labels + mixedMoment B node3764 node3764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2394 singletonSmall5352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5352) = raw2394Labels := by decide +kernel
  rw [hl, canonical2394 B hB] at h
  have hc0 : mixedMoment B raw2394 (Fin.cases (0 : Fin 2) singletonSmall5352) =
      mixedMoment B node3690 node3690Labels := by
    have ha : raw2394 = raw2395 := by apply Matrix.ext; unfold raw2394 raw2395; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5352 = raw2395Labels := by decide +kernel
    rw [ha, hj, canonical2395 B hB]
  have hc1 : mixedMoment B raw2394 (Fin.cases (1 : Fin 2) singletonSmall5352) =
      mixedMoment B node3764 node3764Labels := by
    have ha : raw2394 = raw2396 := by apply Matrix.ext; unfold raw2394 raw2396; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5352 = raw2396Labels := by decide +kernel
    rw [ha, hj, canonical2396 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5354 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5354 node5354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3692 node3692Labels + mixedMoment B node3769 node3769Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2397 singletonSmall5354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5354) = raw2397Labels := by decide +kernel
  rw [hl, canonical2397 B hB] at h
  have hc0 : mixedMoment B raw2397 (Fin.cases (0 : Fin 2) singletonSmall5354) =
      mixedMoment B node3692 node3692Labels := by
    have ha : raw2397 = raw2398 := by apply Matrix.ext; unfold raw2397 raw2398; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5354 = raw2398Labels := by decide +kernel
    rw [ha, hj, canonical2398 B hB]
  have hc1 : mixedMoment B raw2397 (Fin.cases (1 : Fin 2) singletonSmall5354) =
      mixedMoment B node3769 node3769Labels := by
    have ha : raw2397 = raw2399 := by apply Matrix.ext; unfold raw2397 raw2399; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5354 = raw2399Labels := by decide +kernel
    rw [ha, hj, canonical2399 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5355 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5355 node5355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3693 node3693Labels + mixedMoment B node3770 node3770Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2400 singletonSmall5355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5355) = raw2400Labels := by decide +kernel
  rw [hl, canonical2400 B hB] at h
  have hc0 : mixedMoment B raw2400 (Fin.cases (0 : Fin 2) singletonSmall5355) =
      mixedMoment B node3693 node3693Labels := by
    have ha : raw2400 = raw2401 := by apply Matrix.ext; unfold raw2400 raw2401; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5355 = raw2401Labels := by decide +kernel
    rw [ha, hj, canonical2401 B hB]
  have hc1 : mixedMoment B raw2400 (Fin.cases (1 : Fin 2) singletonSmall5355) =
      mixedMoment B node3770 node3770Labels := by
    have ha : raw2400 = raw2402 := by apply Matrix.ext; unfold raw2400 raw2402; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5355 = raw2402Labels := by decide +kernel
    rw [ha, hj, canonical2402 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5356 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5356 node5356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3694 node3694Labels + mixedMoment B node3773 node3773Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2403 singletonSmall5356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5356) = raw2403Labels := by decide +kernel
  rw [hl, canonical2403 B hB] at h
  have hc0 : mixedMoment B raw2403 (Fin.cases (0 : Fin 2) singletonSmall5356) =
      mixedMoment B node3694 node3694Labels := by
    have ha : raw2403 = raw2404 := by apply Matrix.ext; unfold raw2403 raw2404; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5356 = raw2404Labels := by decide +kernel
    rw [ha, hj, canonical2404 B hB]
  have hc1 : mixedMoment B raw2403 (Fin.cases (1 : Fin 2) singletonSmall5356) =
      mixedMoment B node3773 node3773Labels := by
    have ha : raw2403 = raw2405 := by apply Matrix.ext; unfold raw2403 raw2405; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5356 = raw2405Labels := by decide +kernel
    rw [ha, hj, canonical2405 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5363 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5363 node5363Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3701 node3701Labels + mixedMoment B node3751 node3751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2406 singletonSmall5363
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5363) = raw2406Labels := by decide +kernel
  rw [hl, canonical2406 B hB] at h
  have hc0 : mixedMoment B raw2406 (Fin.cases (0 : Fin 2) singletonSmall5363) =
      mixedMoment B node3701 node3701Labels := by
    have ha : raw2406 = raw2407 := by apply Matrix.ext; unfold raw2406 raw2407; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5363 = raw2407Labels := by decide +kernel
    rw [ha, hj, canonical2407 B hB]
  have hc1 : mixedMoment B raw2406 (Fin.cases (1 : Fin 2) singletonSmall5363) =
      mixedMoment B node3751 node3751Labels := by
    have ha : raw2406 = raw2408 := by apply Matrix.ext; unfold raw2406 raw2408; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5363 = raw2408Labels := by decide +kernel
    rw [ha, hj, canonical2408 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5364 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5364 node5364Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3702 node3702Labels + mixedMoment B node3702 node3702Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2409 singletonSmall5364
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5364) = raw2409Labels := by decide +kernel
  rw [hl, canonical2409 B hB] at h
  have hc0 : mixedMoment B raw2409 (Fin.cases (0 : Fin 2) singletonSmall5364) =
      mixedMoment B node3702 node3702Labels := by
    have ha : raw2409 = raw2410 := by apply Matrix.ext; unfold raw2409 raw2410; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5364 = raw2410Labels := by decide +kernel
    rw [ha, hj, canonical2410 B hB]
  have hc1 : mixedMoment B raw2409 (Fin.cases (1 : Fin 2) singletonSmall5364) =
      mixedMoment B node3702 node3702Labels := by
    have ha : raw2409 = raw2411 := by apply Matrix.ext; unfold raw2409 raw2411; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5364 = raw2411Labels := by decide +kernel
    rw [ha, hj, canonical2411 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5365 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5365 node5365Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3703 node3703Labels + mixedMoment B node3758 node3758Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2412 singletonSmall5365
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5365) = raw2412Labels := by decide +kernel
  rw [hl, canonical2412 B hB] at h
  have hc0 : mixedMoment B raw2412 (Fin.cases (0 : Fin 2) singletonSmall5365) =
      mixedMoment B node3703 node3703Labels := by
    have ha : raw2412 = raw2413 := by apply Matrix.ext; unfold raw2412 raw2413; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5365 = raw2413Labels := by decide +kernel
    rw [ha, hj, canonical2413 B hB]
  have hc1 : mixedMoment B raw2412 (Fin.cases (1 : Fin 2) singletonSmall5365) =
      mixedMoment B node3758 node3758Labels := by
    have ha : raw2412 = raw2414 := by apply Matrix.ext; unfold raw2412 raw2414; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5365 = raw2414Labels := by decide +kernel
    rw [ha, hj, canonical2414 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5368 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5368 node5368Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3705 node3705Labels + mixedMoment B node3767 node3767Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2415 singletonSmall5368
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5368) = raw2415Labels := by decide +kernel
  rw [hl, canonical2415 B hB] at h
  have hc0 : mixedMoment B raw2415 (Fin.cases (0 : Fin 2) singletonSmall5368) =
      mixedMoment B node3705 node3705Labels := by
    have ha : raw2415 = raw2416 := by apply Matrix.ext; unfold raw2415 raw2416; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5368 = raw2416Labels := by decide +kernel
    rw [ha, hj, canonical2416 B hB]
  have hc1 : mixedMoment B raw2415 (Fin.cases (1 : Fin 2) singletonSmall5368) =
      mixedMoment B node3767 node3767Labels := by
    have ha : raw2415 = raw2417 := by apply Matrix.ext; unfold raw2415 raw2417; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5368 = raw2417Labels := by decide +kernel
    rw [ha, hj, canonical2417 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5370 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5370 node5370Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3706 node3706Labels + mixedMoment B node3771 node3771Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2418 singletonSmall5370
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5370) = raw2418Labels := by decide +kernel
  rw [hl, canonical2418 B hB] at h
  have hc0 : mixedMoment B raw2418 (Fin.cases (0 : Fin 2) singletonSmall5370) =
      mixedMoment B node3706 node3706Labels := by
    have ha : raw2418 = raw2419 := by apply Matrix.ext; unfold raw2418 raw2419; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5370 = raw2419Labels := by decide +kernel
    rw [ha, hj, canonical2419 B hB]
  have hc1 : mixedMoment B raw2418 (Fin.cases (1 : Fin 2) singletonSmall5370) =
      mixedMoment B node3771 node3771Labels := by
    have ha : raw2418 = raw2420 := by apply Matrix.ext; unfold raw2418 raw2420; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5370 = raw2420Labels := by decide +kernel
    rw [ha, hj, canonical2420 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5372 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5372 node5372Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3708 node3708Labels + mixedMoment B node3791 node3791Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2421 singletonSmall5372
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5372) = raw2421Labels := by decide +kernel
  rw [hl, canonical2421 B hB] at h
  have hc0 : mixedMoment B raw2421 (Fin.cases (0 : Fin 2) singletonSmall5372) =
      mixedMoment B node3708 node3708Labels := by
    have ha : raw2421 = raw2422 := by apply Matrix.ext; unfold raw2421 raw2422; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5372 = raw2422Labels := by decide +kernel
    rw [ha, hj, canonical2422 B hB]
  have hc1 : mixedMoment B raw2421 (Fin.cases (1 : Fin 2) singletonSmall5372) =
      mixedMoment B node3791 node3791Labels := by
    have ha : raw2421 = raw2423 := by apply Matrix.ext; unfold raw2421 raw2423; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5372 = raw2423Labels := by decide +kernel
    rw [ha, hj, canonical2423 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5373 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5373 node5373Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3709 node3709Labels + mixedMoment B node3792 node3792Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2424 singletonSmall5373
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5373) = raw2424Labels := by decide +kernel
  rw [hl, canonical2424 B hB] at h
  have hc0 : mixedMoment B raw2424 (Fin.cases (0 : Fin 2) singletonSmall5373) =
      mixedMoment B node3709 node3709Labels := by
    have ha : raw2424 = raw2425 := by apply Matrix.ext; unfold raw2424 raw2425; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5373 = raw2425Labels := by decide +kernel
    rw [ha, hj, canonical2425 B hB]
  have hc1 : mixedMoment B raw2424 (Fin.cases (1 : Fin 2) singletonSmall5373) =
      mixedMoment B node3792 node3792Labels := by
    have ha : raw2424 = raw2426 := by apply Matrix.ext; unfold raw2424 raw2426; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5373 = raw2426Labels := by decide +kernel
    rw [ha, hj, canonical2426 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5374 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5374 node5374Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3713 node3713Labels + mixedMoment B node3713 node3713Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2427 singletonSmall5374
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5374) = raw2427Labels := by decide +kernel
  rw [hl, canonical2427 B hB] at h
  have hc0 : mixedMoment B raw2427 (Fin.cases (0 : Fin 2) singletonSmall5374) =
      mixedMoment B node3713 node3713Labels := by
    have ha : raw2427 = raw2428 := by apply Matrix.ext; unfold raw2427 raw2428; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5374 = raw2428Labels := by decide +kernel
    rw [ha, hj, canonical2428 B hB]
  have hc1 : mixedMoment B raw2427 (Fin.cases (1 : Fin 2) singletonSmall5374) =
      mixedMoment B node3713 node3713Labels := by
    have ha : raw2427 = raw2429 := by apply Matrix.ext; unfold raw2427 raw2429; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5374 = raw2429Labels := by decide +kernel
    rw [ha, hj, canonical2429 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical19

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5378 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5378 node5378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3719 node3719Labels + mixedMoment B node3795 node3795Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2430 singletonSmall5378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5378) = raw2430Labels := by decide +kernel
  rw [hl, canonical2430 B hB] at h
  have hc0 : mixedMoment B raw2430 (Fin.cases (0 : Fin 2) singletonSmall5378) =
      mixedMoment B node3719 node3719Labels := by
    have ha : raw2430 = raw2431 := by apply Matrix.ext; unfold raw2430 raw2431; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5378 = raw2431Labels := by decide +kernel
    rw [ha, hj, canonical2431 B hB]
  have hc1 : mixedMoment B raw2430 (Fin.cases (1 : Fin 2) singletonSmall5378) =
      mixedMoment B node3795 node3795Labels := by
    have ha : raw2430 = raw2432 := by apply Matrix.ext; unfold raw2430 raw2432; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5378 = raw2432Labels := by decide +kernel
    rw [ha, hj, canonical2432 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5380 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5380 node5380Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3721 node3721Labels + mixedMoment B node3836 node3836Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2433 singletonSmall5380
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5380) = raw2433Labels := by decide +kernel
  rw [hl, canonical2433 B hB] at h
  have hc0 : mixedMoment B raw2433 (Fin.cases (0 : Fin 2) singletonSmall5380) =
      mixedMoment B node3721 node3721Labels := by
    have ha : raw2433 = raw2434 := by apply Matrix.ext; unfold raw2433 raw2434; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5380 = raw2434Labels := by decide +kernel
    rw [ha, hj, canonical2434 B hB]
  have hc1 : mixedMoment B raw2433 (Fin.cases (1 : Fin 2) singletonSmall5380) =
      mixedMoment B node3836 node3836Labels := by
    have ha : raw2433 = raw2435 := by apply Matrix.ext; unfold raw2433 raw2435; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5380 = raw2435Labels := by decide +kernel
    rw [ha, hj, canonical2435 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5383 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5383 node5383Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3731 node3731Labels + mixedMoment B node3867 node3867Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2436 singletonSmall5383
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5383) = raw2436Labels := by decide +kernel
  rw [hl, canonical2436 B hB] at h
  have hc0 : mixedMoment B raw2436 (Fin.cases (0 : Fin 2) singletonSmall5383) =
      mixedMoment B node3731 node3731Labels := by
    have ha : raw2436 = raw2437 := by apply Matrix.ext; unfold raw2436 raw2437; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5383 = raw2437Labels := by decide +kernel
    rw [ha, hj, canonical2437 B hB]
  have hc1 : mixedMoment B raw2436 (Fin.cases (1 : Fin 2) singletonSmall5383) =
      mixedMoment B node3867 node3867Labels := by
    have ha : raw2436 = raw2438 := by apply Matrix.ext; unfold raw2436 raw2438; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5383 = raw2438Labels := by decide +kernel
    rw [ha, hj, canonical2438 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5384 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5384 node5384Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3732 node3732Labels + mixedMoment B node3811 node3811Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2439 singletonSmall5384
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5384) = raw2439Labels := by decide +kernel
  rw [hl, canonical2439 B hB] at h
  have hc0 : mixedMoment B raw2439 (Fin.cases (0 : Fin 2) singletonSmall5384) =
      mixedMoment B node3732 node3732Labels := by
    have ha : raw2439 = raw2440 := by apply Matrix.ext; unfold raw2439 raw2440; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5384 = raw2440Labels := by decide +kernel
    rw [ha, hj, canonical2440 B hB]
  have hc1 : mixedMoment B raw2439 (Fin.cases (1 : Fin 2) singletonSmall5384) =
      mixedMoment B node3811 node3811Labels := by
    have ha : raw2439 = raw2441 := by apply Matrix.ext; unfold raw2439 raw2441; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5384 = raw2441Labels := by decide +kernel
    rw [ha, hj, canonical2441 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5386 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5386 node5386Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3735 node3735Labels + mixedMoment B node3890 node3890Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2442 singletonSmall5386
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5386) = raw2442Labels := by decide +kernel
  rw [hl, canonical2442 B hB] at h
  have hc0 : mixedMoment B raw2442 (Fin.cases (0 : Fin 2) singletonSmall5386) =
      mixedMoment B node3735 node3735Labels := by
    have ha : raw2442 = raw2443 := by apply Matrix.ext; unfold raw2442 raw2443; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5386 = raw2443Labels := by decide +kernel
    rw [ha, hj, canonical2443 B hB]
  have hc1 : mixedMoment B raw2442 (Fin.cases (1 : Fin 2) singletonSmall5386) =
      mixedMoment B node3890 node3890Labels := by
    have ha : raw2442 = raw2444 := by apply Matrix.ext; unfold raw2442 raw2444; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5386 = raw2444Labels := by decide +kernel
    rw [ha, hj, canonical2444 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5387 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5387 node5387Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3736 node3736Labels + mixedMoment B node3891 node3891Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2445 singletonSmall5387
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5387) = raw2445Labels := by decide +kernel
  rw [hl, canonical2445 B hB] at h
  have hc0 : mixedMoment B raw2445 (Fin.cases (0 : Fin 2) singletonSmall5387) =
      mixedMoment B node3736 node3736Labels := by
    have ha : raw2445 = raw2446 := by apply Matrix.ext; unfold raw2445 raw2446; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5387 = raw2446Labels := by decide +kernel
    rw [ha, hj, canonical2446 B hB]
  have hc1 : mixedMoment B raw2445 (Fin.cases (1 : Fin 2) singletonSmall5387) =
      mixedMoment B node3891 node3891Labels := by
    have ha : raw2445 = raw2447 := by apply Matrix.ext; unfold raw2445 raw2447; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5387 = raw2447Labels := by decide +kernel
    rw [ha, hj, canonical2447 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5388 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5388 node5388Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3737 node3737Labels + mixedMoment B node3892 node3892Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2448 singletonSmall5388
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5388) = raw2448Labels := by decide +kernel
  rw [hl, canonical2448 B hB] at h
  have hc0 : mixedMoment B raw2448 (Fin.cases (0 : Fin 2) singletonSmall5388) =
      mixedMoment B node3737 node3737Labels := by
    have ha : raw2448 = raw2449 := by apply Matrix.ext; unfold raw2448 raw2449; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5388 = raw2449Labels := by decide +kernel
    rw [ha, hj, canonical2449 B hB]
  have hc1 : mixedMoment B raw2448 (Fin.cases (1 : Fin 2) singletonSmall5388) =
      mixedMoment B node3892 node3892Labels := by
    have ha : raw2448 = raw2450 := by apply Matrix.ext; unfold raw2448 raw2450; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5388 = raw2450Labels := by decide +kernel
    rw [ha, hj, canonical2450 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5389 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5389 node5389Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3740 node3740Labels + mixedMoment B node3893 node3893Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2451 singletonSmall5389
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5389) = raw2451Labels := by decide +kernel
  rw [hl, canonical2451 B hB] at h
  have hc0 : mixedMoment B raw2451 (Fin.cases (0 : Fin 2) singletonSmall5389) =
      mixedMoment B node3740 node3740Labels := by
    have ha : raw2451 = raw2452 := by apply Matrix.ext; unfold raw2451 raw2452; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5389 = raw2452Labels := by decide +kernel
    rw [ha, hj, canonical2452 B hB]
  have hc1 : mixedMoment B raw2451 (Fin.cases (1 : Fin 2) singletonSmall5389) =
      mixedMoment B node3893 node3893Labels := by
    have ha : raw2451 = raw2453 := by apply Matrix.ext; unfold raw2451 raw2453; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5389 = raw2453Labels := by decide +kernel
    rw [ha, hj, canonical2453 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5390 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5390 node5390Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3741 node3741Labels + mixedMoment B node3894 node3894Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2454 singletonSmall5390
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5390) = raw2454Labels := by decide +kernel
  rw [hl, canonical2454 B hB] at h
  have hc0 : mixedMoment B raw2454 (Fin.cases (0 : Fin 2) singletonSmall5390) =
      mixedMoment B node3741 node3741Labels := by
    have ha : raw2454 = raw2455 := by apply Matrix.ext; unfold raw2454 raw2455; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5390 = raw2455Labels := by decide +kernel
    rw [ha, hj, canonical2455 B hB]
  have hc1 : mixedMoment B raw2454 (Fin.cases (1 : Fin 2) singletonSmall5390) =
      mixedMoment B node3894 node3894Labels := by
    have ha : raw2454 = raw2456 := by apply Matrix.ext; unfold raw2454 raw2456; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5390 = raw2456Labels := by decide +kernel
    rw [ha, hj, canonical2456 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5391 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5391 node5391Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3776 node3776Labels + mixedMoment B node3778 node3778Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2457 singletonSmall5391
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5391) = raw2457Labels := by decide +kernel
  rw [hl, canonical2457 B hB] at h
  have hc0 : mixedMoment B raw2457 (Fin.cases (0 : Fin 2) singletonSmall5391) =
      mixedMoment B node3776 node3776Labels := by
    have ha : raw2457 = raw2458 := by apply Matrix.ext; unfold raw2457 raw2458; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5391 = raw2458Labels := by decide +kernel
    rw [ha, hj, canonical2458 B hB]
  have hc1 : mixedMoment B raw2457 (Fin.cases (1 : Fin 2) singletonSmall5391) =
      mixedMoment B node3778 node3778Labels := by
    have ha : raw2457 = raw2459 := by apply Matrix.ext; unfold raw2457 raw2459; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5391 = raw2459Labels := by decide +kernel
    rw [ha, hj, canonical2459 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5393 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5393 node5393Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3779 node3779Labels + mixedMoment B node3797 node3797Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2460 singletonSmall5393
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5393) = raw2460Labels := by decide +kernel
  rw [hl, canonical2460 B hB] at h
  have hc0 : mixedMoment B raw2460 (Fin.cases (0 : Fin 2) singletonSmall5393) =
      mixedMoment B node3779 node3779Labels := by
    have ha : raw2460 = raw2461 := by apply Matrix.ext; unfold raw2460 raw2461; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5393 = raw2461Labels := by decide +kernel
    rw [ha, hj, canonical2461 B hB]
  have hc1 : mixedMoment B raw2460 (Fin.cases (1 : Fin 2) singletonSmall5393) =
      mixedMoment B node3797 node3797Labels := by
    have ha : raw2460 = raw2462 := by apply Matrix.ext; unfold raw2460 raw2462; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5393 = raw2462Labels := by decide +kernel
    rw [ha, hj, canonical2462 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5395 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5395 node5395Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3781 node3781Labels + mixedMoment B node3794 node3794Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2463 singletonSmall5395
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5395) = raw2463Labels := by decide +kernel
  rw [hl, canonical2463 B hB] at h
  have hc0 : mixedMoment B raw2463 (Fin.cases (0 : Fin 2) singletonSmall5395) =
      mixedMoment B node3781 node3781Labels := by
    have ha : raw2463 = raw2464 := by apply Matrix.ext; unfold raw2463 raw2464; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5395 = raw2464Labels := by decide +kernel
    rw [ha, hj, canonical2464 B hB]
  have hc1 : mixedMoment B raw2463 (Fin.cases (1 : Fin 2) singletonSmall5395) =
      mixedMoment B node3794 node3794Labels := by
    have ha : raw2463 = raw2465 := by apply Matrix.ext; unfold raw2463 raw2465; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5395 = raw2465Labels := by decide +kernel
    rw [ha, hj, canonical2465 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5397 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5397 node5397Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3782 node3782Labels + mixedMoment B node3796 node3796Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2466 singletonSmall5397
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5397) = raw2466Labels := by decide +kernel
  rw [hl, canonical2466 B hB] at h
  have hc0 : mixedMoment B raw2466 (Fin.cases (0 : Fin 2) singletonSmall5397) =
      mixedMoment B node3782 node3782Labels := by
    have ha : raw2466 = raw2467 := by apply Matrix.ext; unfold raw2466 raw2467; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5397 = raw2467Labels := by decide +kernel
    rw [ha, hj, canonical2467 B hB]
  have hc1 : mixedMoment B raw2466 (Fin.cases (1 : Fin 2) singletonSmall5397) =
      mixedMoment B node3796 node3796Labels := by
    have ha : raw2466 = raw2468 := by apply Matrix.ext; unfold raw2466 raw2468; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5397 = raw2468Labels := by decide +kernel
    rw [ha, hj, canonical2468 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5398 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5398 node5398Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3784 node3784Labels + mixedMoment B node3784 node3784Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2469 singletonSmall5398
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5398) = raw2469Labels := by decide +kernel
  rw [hl, canonical2469 B hB] at h
  have hc0 : mixedMoment B raw2469 (Fin.cases (0 : Fin 2) singletonSmall5398) =
      mixedMoment B node3784 node3784Labels := by
    have ha : raw2469 = raw2470 := by apply Matrix.ext; unfold raw2469 raw2470; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5398 = raw2470Labels := by decide +kernel
    rw [ha, hj, canonical2470 B hB]
  have hc1 : mixedMoment B raw2469 (Fin.cases (1 : Fin 2) singletonSmall5398) =
      mixedMoment B node3784 node3784Labels := by
    have ha : raw2469 = raw2471 := by apply Matrix.ext; unfold raw2469 raw2471; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5398 = raw2471Labels := by decide +kernel
    rw [ha, hj, canonical2471 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5400 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5400 node5400Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3786 node3786Labels + mixedMoment B node3799 node3799Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2472 singletonSmall5400
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5400) = raw2472Labels := by decide +kernel
  rw [hl, canonical2472 B hB] at h
  have hc0 : mixedMoment B raw2472 (Fin.cases (0 : Fin 2) singletonSmall5400) =
      mixedMoment B node3786 node3786Labels := by
    have ha : raw2472 = raw2473 := by apply Matrix.ext; unfold raw2472 raw2473; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5400 = raw2473Labels := by decide +kernel
    rw [ha, hj, canonical2473 B hB]
  have hc1 : mixedMoment B raw2472 (Fin.cases (1 : Fin 2) singletonSmall5400) =
      mixedMoment B node3799 node3799Labels := by
    have ha : raw2472 = raw2474 := by apply Matrix.ext; unfold raw2472 raw2474; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5400 = raw2474Labels := by decide +kernel
    rw [ha, hj, canonical2474 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5401 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5401 node5401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3787 node3787Labels + mixedMoment B node3804 node3804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2475 singletonSmall5401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5401) = raw2475Labels := by decide +kernel
  rw [hl, canonical2475 B hB] at h
  have hc0 : mixedMoment B raw2475 (Fin.cases (0 : Fin 2) singletonSmall5401) =
      mixedMoment B node3787 node3787Labels := by
    have ha : raw2475 = raw2476 := by apply Matrix.ext; unfold raw2475 raw2476; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5401 = raw2476Labels := by decide +kernel
    rw [ha, hj, canonical2476 B hB]
  have hc1 : mixedMoment B raw2475 (Fin.cases (1 : Fin 2) singletonSmall5401) =
      mixedMoment B node3804 node3804Labels := by
    have ha : raw2475 = raw2477 := by apply Matrix.ext; unfold raw2475 raw2477; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5401 = raw2477Labels := by decide +kernel
    rw [ha, hj, canonical2477 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5403 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5403 node5403Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3789 node3789Labels + mixedMoment B node3810 node3810Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2478 singletonSmall5403
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5403) = raw2478Labels := by decide +kernel
  rw [hl, canonical2478 B hB] at h
  have hc0 : mixedMoment B raw2478 (Fin.cases (0 : Fin 2) singletonSmall5403) =
      mixedMoment B node3789 node3789Labels := by
    have ha : raw2478 = raw2479 := by apply Matrix.ext; unfold raw2478 raw2479; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5403 = raw2479Labels := by decide +kernel
    rw [ha, hj, canonical2479 B hB]
  have hc1 : mixedMoment B raw2478 (Fin.cases (1 : Fin 2) singletonSmall5403) =
      mixedMoment B node3810 node3810Labels := by
    have ha : raw2478 = raw2480 := by apply Matrix.ext; unfold raw2478 raw2480; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5403 = raw2480Labels := by decide +kernel
    rw [ha, hj, canonical2480 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5404 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5404 node5404Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3790 node3790Labels + mixedMoment B node3815 node3815Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2481 singletonSmall5404
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5404) = raw2481Labels := by decide +kernel
  rw [hl, canonical2481 B hB] at h
  have hc0 : mixedMoment B raw2481 (Fin.cases (0 : Fin 2) singletonSmall5404) =
      mixedMoment B node3790 node3790Labels := by
    have ha : raw2481 = raw2482 := by apply Matrix.ext; unfold raw2481 raw2482; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5404 = raw2482Labels := by decide +kernel
    rw [ha, hj, canonical2482 B hB]
  have hc1 : mixedMoment B raw2481 (Fin.cases (1 : Fin 2) singletonSmall5404) =
      mixedMoment B node3815 node3815Labels := by
    have ha : raw2481 = raw2483 := by apply Matrix.ext; unfold raw2481 raw2483; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5404 = raw2483Labels := by decide +kernel
    rw [ha, hj, canonical2483 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5405 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5405 node5405Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3800 node3800Labels + mixedMoment B node3805 node3805Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2484 singletonSmall5405
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5405) = raw2484Labels := by decide +kernel
  rw [hl, canonical2484 B hB] at h
  have hc0 : mixedMoment B raw2484 (Fin.cases (0 : Fin 2) singletonSmall5405) =
      mixedMoment B node3800 node3800Labels := by
    have ha : raw2484 = raw2485 := by apply Matrix.ext; unfold raw2484 raw2485; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5405 = raw2485Labels := by decide +kernel
    rw [ha, hj, canonical2485 B hB]
  have hc1 : mixedMoment B raw2484 (Fin.cases (1 : Fin 2) singletonSmall5405) =
      mixedMoment B node3805 node3805Labels := by
    have ha : raw2484 = raw2486 := by apply Matrix.ext; unfold raw2484 raw2486; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5405 = raw2486Labels := by decide +kernel
    rw [ha, hj, canonical2486 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5406 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5406 node5406Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3801 node3801Labels + mixedMoment B node3812 node3812Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2487 singletonSmall5406
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5406) = raw2487Labels := by decide +kernel
  rw [hl, canonical2487 B hB] at h
  have hc0 : mixedMoment B raw2487 (Fin.cases (0 : Fin 2) singletonSmall5406) =
      mixedMoment B node3801 node3801Labels := by
    have ha : raw2487 = raw2488 := by apply Matrix.ext; unfold raw2487 raw2488; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5406 = raw2488Labels := by decide +kernel
    rw [ha, hj, canonical2488 B hB]
  have hc1 : mixedMoment B raw2487 (Fin.cases (1 : Fin 2) singletonSmall5406) =
      mixedMoment B node3812 node3812Labels := by
    have ha : raw2487 = raw2489 := by apply Matrix.ext; unfold raw2487 raw2489; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5406 = raw2489Labels := by decide +kernel
    rw [ha, hj, canonical2489 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5411 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5411 node5411Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3809 node3809Labels + mixedMoment B node3813 node3813Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2490 singletonSmall5411
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5411) = raw2490Labels := by decide +kernel
  rw [hl, canonical2490 B hB] at h
  have hc0 : mixedMoment B raw2490 (Fin.cases (0 : Fin 2) singletonSmall5411) =
      mixedMoment B node3809 node3809Labels := by
    have ha : raw2490 = raw2491 := by apply Matrix.ext; unfold raw2490 raw2491; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5411 = raw2491Labels := by decide +kernel
    rw [ha, hj, canonical2491 B hB]
  have hc1 : mixedMoment B raw2490 (Fin.cases (1 : Fin 2) singletonSmall5411) =
      mixedMoment B node3813 node3813Labels := by
    have ha : raw2490 = raw2492 := by apply Matrix.ext; unfold raw2490 raw2492; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5411 = raw2492Labels := by decide +kernel
    rw [ha, hj, canonical2492 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5412 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5412 node5412Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3814 node3814Labels + mixedMoment B node3814 node3814Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2493 singletonSmall5412
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5412) = raw2493Labels := by decide +kernel
  rw [hl, canonical2493 B hB] at h
  have hc0 : mixedMoment B raw2493 (Fin.cases (0 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2494 := by apply Matrix.ext; unfold raw2493 raw2494; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5412 = raw2494Labels := by decide +kernel
    rw [ha, hj, canonical2494 B hB]
  have hc1 : mixedMoment B raw2493 (Fin.cases (1 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2495 := by apply Matrix.ext; unfold raw2493 raw2495; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5412 = raw2495Labels := by decide +kernel
    rw [ha, hj, canonical2495 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5415 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5415 node5415Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3820 node3820Labels + mixedMoment B node3895 node3895Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2496 singletonSmall5415
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5415) = raw2496Labels := by decide +kernel
  rw [hl, canonical2496 B hB] at h
  have hc0 : mixedMoment B raw2496 (Fin.cases (0 : Fin 2) singletonSmall5415) =
      mixedMoment B node3820 node3820Labels := by
    have ha : raw2496 = raw2497 := by apply Matrix.ext; unfold raw2496 raw2497; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5415 = raw2497Labels := by decide +kernel
    rw [ha, hj, canonical2497 B hB]
  have hc1 : mixedMoment B raw2496 (Fin.cases (1 : Fin 2) singletonSmall5415) =
      mixedMoment B node3895 node3895Labels := by
    have ha : raw2496 = raw2498 := by apply Matrix.ext; unfold raw2496 raw2498; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5415 = raw2498Labels := by decide +kernel
    rw [ha, hj, canonical2498 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5416 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5416 node5416Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3821 node3821Labels + mixedMoment B node3896 node3896Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2499 singletonSmall5416
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5416) = raw2499Labels := by decide +kernel
  rw [hl, canonical2499 B hB] at h
  have hc0 : mixedMoment B raw2499 (Fin.cases (0 : Fin 2) singletonSmall5416) =
      mixedMoment B node3821 node3821Labels := by
    have ha : raw2499 = raw2500 := by apply Matrix.ext; unfold raw2499 raw2500; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5416 = raw2500Labels := by decide +kernel
    rw [ha, hj, canonical2500 B hB]
  have hc1 : mixedMoment B raw2499 (Fin.cases (1 : Fin 2) singletonSmall5416) =
      mixedMoment B node3896 node3896Labels := by
    have ha : raw2499 = raw2501 := by apply Matrix.ext; unfold raw2499 raw2501; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5416 = raw2501Labels := by decide +kernel
    rw [ha, hj, canonical2501 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5417 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5417 node5417Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3823 node3823Labels + mixedMoment B node3897 node3897Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2502 singletonSmall5417
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5417) = raw2502Labels := by decide +kernel
  rw [hl, canonical2502 B hB] at h
  have hc0 : mixedMoment B raw2502 (Fin.cases (0 : Fin 2) singletonSmall5417) =
      mixedMoment B node3823 node3823Labels := by
    have ha : raw2502 = raw2503 := by apply Matrix.ext; unfold raw2502 raw2503; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5417 = raw2503Labels := by decide +kernel
    rw [ha, hj, canonical2503 B hB]
  have hc1 : mixedMoment B raw2502 (Fin.cases (1 : Fin 2) singletonSmall5417) =
      mixedMoment B node3897 node3897Labels := by
    have ha : raw2502 = raw2504 := by apply Matrix.ext; unfold raw2502 raw2504; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5417 = raw2504Labels := by decide +kernel
    rw [ha, hj, canonical2504 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5418 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5418 node5418Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3824 node3824Labels + mixedMoment B node3898 node3898Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2505 singletonSmall5418
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5418) = raw2505Labels := by decide +kernel
  rw [hl, canonical2505 B hB] at h
  have hc0 : mixedMoment B raw2505 (Fin.cases (0 : Fin 2) singletonSmall5418) =
      mixedMoment B node3824 node3824Labels := by
    have ha : raw2505 = raw2506 := by apply Matrix.ext; unfold raw2505 raw2506; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5418 = raw2506Labels := by decide +kernel
    rw [ha, hj, canonical2506 B hB]
  have hc1 : mixedMoment B raw2505 (Fin.cases (1 : Fin 2) singletonSmall5418) =
      mixedMoment B node3898 node3898Labels := by
    have ha : raw2505 = raw2507 := by apply Matrix.ext; unfold raw2505 raw2507; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5418 = raw2507Labels := by decide +kernel
    rw [ha, hj, canonical2507 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5422 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5422 node5422Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3964 node3964Labels + mixedMoment B node3900 node3900Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2508 singletonSmall5422
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5422) = raw2508Labels := by decide +kernel
  rw [hl, canonical2508 B hB] at h
  have hc0 : mixedMoment B raw2508 (Fin.cases (0 : Fin 2) singletonSmall5422) =
      mixedMoment B node3964 node3964Labels := by
    have ha : raw2508 = raw2509 := by apply Matrix.ext; unfold raw2508 raw2509; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5422 = raw2509Labels := by decide +kernel
    rw [ha, hj, canonical2509 B hB]
  have hc1 : mixedMoment B raw2508 (Fin.cases (1 : Fin 2) singletonSmall5422) =
      mixedMoment B node3900 node3900Labels := by
    have ha : raw2508 = raw2510 := by apply Matrix.ext; unfold raw2508 raw2510; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5422 = raw2510Labels := by decide +kernel
    rw [ha, hj, canonical2510 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5423 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5423 node5423Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3837 node3837Labels + mixedMoment B node3837 node3837Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2511 singletonSmall5423
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5423) = raw2511Labels := by decide +kernel
  rw [hl, canonical2511 B hB] at h
  have hc0 : mixedMoment B raw2511 (Fin.cases (0 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2512 := by apply Matrix.ext; unfold raw2511 raw2512; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5423 = raw2512Labels := by decide +kernel
    rw [ha, hj, canonical2512 B hB]
  have hc1 : mixedMoment B raw2511 (Fin.cases (1 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2513 := by apply Matrix.ext; unfold raw2511 raw2513; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5423 = raw2513Labels := by decide +kernel
    rw [ha, hj, canonical2513 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5424 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5424 node5424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3838 node3838Labels + mixedMoment B node3843 node3843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2514 singletonSmall5424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5424) = raw2514Labels := by decide +kernel
  rw [hl, canonical2514 B hB] at h
  have hc0 : mixedMoment B raw2514 (Fin.cases (0 : Fin 2) singletonSmall5424) =
      mixedMoment B node3838 node3838Labels := by
    have ha : raw2514 = raw2515 := by apply Matrix.ext; unfold raw2514 raw2515; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5424 = raw2515Labels := by decide +kernel
    rw [ha, hj, canonical2515 B hB]
  have hc1 : mixedMoment B raw2514 (Fin.cases (1 : Fin 2) singletonSmall5424) =
      mixedMoment B node3843 node3843Labels := by
    have ha : raw2514 = raw2516 := by apply Matrix.ext; unfold raw2514 raw2516; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5424 = raw2516Labels := by decide +kernel
    rw [ha, hj, canonical2516 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5428 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5428 node5428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3845 node3845Labels + mixedMoment B node3845 node3845Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2517 singletonSmall5428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5428) = raw2517Labels := by decide +kernel
  rw [hl, canonical2517 B hB] at h
  have hc0 : mixedMoment B raw2517 (Fin.cases (0 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2518 := by apply Matrix.ext; unfold raw2517 raw2518; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5428 = raw2518Labels := by decide +kernel
    rw [ha, hj, canonical2518 B hB]
  have hc1 : mixedMoment B raw2517 (Fin.cases (1 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2519 := by apply Matrix.ext; unfold raw2517 raw2519; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5428 = raw2519Labels := by decide +kernel
    rw [ha, hj, canonical2519 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5431 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5431 node5431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3849 node3849Labels + mixedMoment B node3875 node3875Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2520 singletonSmall5431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5431) = raw2520Labels := by decide +kernel
  rw [hl, canonical2520 B hB] at h
  have hc0 : mixedMoment B raw2520 (Fin.cases (0 : Fin 2) singletonSmall5431) =
      mixedMoment B node3849 node3849Labels := by
    have ha : raw2520 = raw2521 := by apply Matrix.ext; unfold raw2520 raw2521; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5431 = raw2521Labels := by decide +kernel
    rw [ha, hj, canonical2521 B hB]
  have hc1 : mixedMoment B raw2520 (Fin.cases (1 : Fin 2) singletonSmall5431) =
      mixedMoment B node3875 node3875Labels := by
    have ha : raw2520 = raw2522 := by apply Matrix.ext; unfold raw2520 raw2522; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5431 = raw2522Labels := by decide +kernel
    rw [ha, hj, canonical2522 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5432 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5432 node5432Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3850 node3850Labels + mixedMoment B node3850 node3850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2523 singletonSmall5432
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5432) = raw2523Labels := by decide +kernel
  rw [hl, canonical2523 B hB] at h
  have hc0 : mixedMoment B raw2523 (Fin.cases (0 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2524 := by apply Matrix.ext; unfold raw2523 raw2524; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5432 = raw2524Labels := by decide +kernel
    rw [ha, hj, canonical2524 B hB]
  have hc1 : mixedMoment B raw2523 (Fin.cases (1 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2525 := by apply Matrix.ext; unfold raw2523 raw2525; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5432 = raw2525Labels := by decide +kernel
    rw [ha, hj, canonical2525 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5433 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5433 node5433Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3851 node3851Labels + mixedMoment B node3901 node3901Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2526 singletonSmall5433
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5433) = raw2526Labels := by decide +kernel
  rw [hl, canonical2526 B hB] at h
  have hc0 : mixedMoment B raw2526 (Fin.cases (0 : Fin 2) singletonSmall5433) =
      mixedMoment B node3851 node3851Labels := by
    have ha : raw2526 = raw2527 := by apply Matrix.ext; unfold raw2526 raw2527; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5433 = raw2527Labels := by decide +kernel
    rw [ha, hj, canonical2527 B hB]
  have hc1 : mixedMoment B raw2526 (Fin.cases (1 : Fin 2) singletonSmall5433) =
      mixedMoment B node3901 node3901Labels := by
    have ha : raw2526 = raw2528 := by apply Matrix.ext; unfold raw2526 raw2528; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5433 = raw2528Labels := by decide +kernel
    rw [ha, hj, canonical2528 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5434 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5434 node5434Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3852 node3852Labels + mixedMoment B node3903 node3903Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2529 singletonSmall5434
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5434) = raw2529Labels := by decide +kernel
  rw [hl, canonical2529 B hB] at h
  have hc0 : mixedMoment B raw2529 (Fin.cases (0 : Fin 2) singletonSmall5434) =
      mixedMoment B node3852 node3852Labels := by
    have ha : raw2529 = raw2530 := by apply Matrix.ext; unfold raw2529 raw2530; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5434 = raw2530Labels := by decide +kernel
    rw [ha, hj, canonical2530 B hB]
  have hc1 : mixedMoment B raw2529 (Fin.cases (1 : Fin 2) singletonSmall5434) =
      mixedMoment B node3903 node3903Labels := by
    have ha : raw2529 = raw2531 := by apply Matrix.ext; unfold raw2529 raw2531; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5434 = raw2531Labels := by decide +kernel
    rw [ha, hj, canonical2531 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5435 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5435 node5435Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3853 node3853Labels + mixedMoment B node3906 node3906Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2532 singletonSmall5435
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5435) = raw2532Labels := by decide +kernel
  rw [hl, canonical2532 B hB] at h
  have hc0 : mixedMoment B raw2532 (Fin.cases (0 : Fin 2) singletonSmall5435) =
      mixedMoment B node3853 node3853Labels := by
    have ha : raw2532 = raw2533 := by apply Matrix.ext; unfold raw2532 raw2533; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5435 = raw2533Labels := by decide +kernel
    rw [ha, hj, canonical2533 B hB]
  have hc1 : mixedMoment B raw2532 (Fin.cases (1 : Fin 2) singletonSmall5435) =
      mixedMoment B node3906 node3906Labels := by
    have ha : raw2532 = raw2534 := by apply Matrix.ext; unfold raw2532 raw2534; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5435 = raw2534Labels := by decide +kernel
    rw [ha, hj, canonical2534 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5437 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5437 node5437Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3899 node3899Labels + mixedMoment B node3899 node3899Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2535 singletonSmall5437
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5437) = raw2535Labels := by decide +kernel
  rw [hl, canonical2535 B hB] at h
  have hc0 : mixedMoment B raw2535 (Fin.cases (0 : Fin 2) singletonSmall5437) =
      mixedMoment B node3899 node3899Labels := by
    have ha : raw2535 = raw2536 := by apply Matrix.ext; unfold raw2535 raw2536; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5437 = raw2536Labels := by decide +kernel
    rw [ha, hj, canonical2536 B hB]
  have hc1 : mixedMoment B raw2535 (Fin.cases (1 : Fin 2) singletonSmall5437) =
      mixedMoment B node3899 node3899Labels := by
    have ha : raw2535 = raw2537 := by apply Matrix.ext; unfold raw2535 raw2537; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5437 = raw2537Labels := by decide +kernel
    rw [ha, hj, canonical2537 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5438 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5438 node5438Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3857 node3857Labels + mixedMoment B node3876 node3876Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2538 singletonSmall5438
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5438) = raw2538Labels := by decide +kernel
  rw [hl, canonical2538 B hB] at h
  have hc0 : mixedMoment B raw2538 (Fin.cases (0 : Fin 2) singletonSmall5438) =
      mixedMoment B node3857 node3857Labels := by
    have ha : raw2538 = raw2539 := by apply Matrix.ext; unfold raw2538 raw2539; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5438 = raw2539Labels := by decide +kernel
    rw [ha, hj, canonical2539 B hB]
  have hc1 : mixedMoment B raw2538 (Fin.cases (1 : Fin 2) singletonSmall5438) =
      mixedMoment B node3876 node3876Labels := by
    have ha : raw2538 = raw2540 := by apply Matrix.ext; unfold raw2538 raw2540; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5438 = raw2540Labels := by decide +kernel
    rw [ha, hj, canonical2540 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5439 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5439 node5439Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3858 node3858Labels + mixedMoment B node3902 node3902Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2541 singletonSmall5439
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5439) = raw2541Labels := by decide +kernel
  rw [hl, canonical2541 B hB] at h
  have hc0 : mixedMoment B raw2541 (Fin.cases (0 : Fin 2) singletonSmall5439) =
      mixedMoment B node3858 node3858Labels := by
    have ha : raw2541 = raw2542 := by apply Matrix.ext; unfold raw2541 raw2542; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5439 = raw2542Labels := by decide +kernel
    rw [ha, hj, canonical2542 B hB]
  have hc1 : mixedMoment B raw2541 (Fin.cases (1 : Fin 2) singletonSmall5439) =
      mixedMoment B node3902 node3902Labels := by
    have ha : raw2541 = raw2543 := by apply Matrix.ext; unfold raw2541 raw2543; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5439 = raw2543Labels := by decide +kernel
    rw [ha, hj, canonical2543 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

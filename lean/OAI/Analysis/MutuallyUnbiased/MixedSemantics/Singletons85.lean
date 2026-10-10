import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5443 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5443 node5443Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3862 node3862Labels + mixedMoment B node3907 node3907Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2544 singletonSmall5443
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5443) = raw2544Labels := by decide +kernel
  rw [hl, canonical2544 B hB] at h
  have hc0 : mixedMoment B raw2544 (Fin.cases (0 : Fin 2) singletonSmall5443) =
      mixedMoment B node3862 node3862Labels := by
    have ha : raw2544 = raw2545 := by apply Matrix.ext; unfold raw2544 raw2545; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5443 = raw2545Labels := by decide +kernel
    rw [ha, hj, canonical2545 B hB]
  have hc1 : mixedMoment B raw2544 (Fin.cases (1 : Fin 2) singletonSmall5443) =
      mixedMoment B node3907 node3907Labels := by
    have ha : raw2544 = raw2546 := by apply Matrix.ext; unfold raw2544 raw2546; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5443 = raw2546Labels := by decide +kernel
    rw [ha, hj, canonical2546 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5447 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5447 node5447Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4025 node4025Labels + mixedMoment B node3909 node3909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2547 singletonSmall5447
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5447) = raw2547Labels := by decide +kernel
  rw [hl, canonical2547 B hB] at h
  have hc0 : mixedMoment B raw2547 (Fin.cases (0 : Fin 2) singletonSmall5447) =
      mixedMoment B node4025 node4025Labels := by
    have ha : raw2547 = raw2548 := by apply Matrix.ext; unfold raw2547 raw2548; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5447 = raw2548Labels := by decide +kernel
    rw [ha, hj, canonical2548 B hB]
  have hc1 : mixedMoment B raw2547 (Fin.cases (1 : Fin 2) singletonSmall5447) =
      mixedMoment B node3909 node3909Labels := by
    have ha : raw2547 = raw2549 := by apply Matrix.ext; unfold raw2547 raw2549; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5447 = raw2549Labels := by decide +kernel
    rw [ha, hj, canonical2549 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5448 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5448 node5448Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3885 node3885Labels + mixedMoment B node3885 node3885Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2550 singletonSmall5448
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5448) = raw2550Labels := by decide +kernel
  rw [hl, canonical2550 B hB] at h
  have hc0 : mixedMoment B raw2550 (Fin.cases (0 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2551 := by apply Matrix.ext; unfold raw2550 raw2551; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5448 = raw2551Labels := by decide +kernel
    rw [ha, hj, canonical2551 B hB]
  have hc1 : mixedMoment B raw2550 (Fin.cases (1 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2552 := by apply Matrix.ext; unfold raw2550 raw2552; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5448 = raw2552Labels := by decide +kernel
    rw [ha, hj, canonical2552 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5449 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5449 node5449Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3886 node3886Labels + mixedMoment B node3886 node3886Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2553 singletonSmall5449
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5449) = raw2553Labels := by decide +kernel
  rw [hl, canonical2553 B hB] at h
  have hc0 : mixedMoment B raw2553 (Fin.cases (0 : Fin 2) singletonSmall5449) =
      mixedMoment B node3886 node3886Labels := by
    have ha : raw2553 = raw2554 := by apply Matrix.ext; unfold raw2553 raw2554; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5449 = raw2554Labels := by decide +kernel
    rw [ha, hj, canonical2554 B hB]
  have hc1 : mixedMoment B raw2553 (Fin.cases (1 : Fin 2) singletonSmall5449) =
      mixedMoment B node3886 node3886Labels := by
    have ha : raw2553 = raw2555 := by apply Matrix.ext; unfold raw2553 raw2555; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5449 = raw2555Labels := by decide +kernel
    rw [ha, hj, canonical2555 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5450 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5450 node5450Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3887 node3887Labels + mixedMoment B node3910 node3910Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2556 singletonSmall5450
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5450) = raw2556Labels := by decide +kernel
  rw [hl, canonical2556 B hB] at h
  have hc0 : mixedMoment B raw2556 (Fin.cases (0 : Fin 2) singletonSmall5450) =
      mixedMoment B node3887 node3887Labels := by
    have ha : raw2556 = raw2557 := by apply Matrix.ext; unfold raw2556 raw2557; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5450 = raw2557Labels := by decide +kernel
    rw [ha, hj, canonical2557 B hB]
  have hc1 : mixedMoment B raw2556 (Fin.cases (1 : Fin 2) singletonSmall5450) =
      mixedMoment B node3910 node3910Labels := by
    have ha : raw2556 = raw2558 := by apply Matrix.ext; unfold raw2556 raw2558; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5450 = raw2558Labels := by decide +kernel
    rw [ha, hj, canonical2558 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5451 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5451 node5451Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3888 node3888Labels + mixedMoment B node3913 node3913Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2559 singletonSmall5451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5451) = raw2559Labels := by decide +kernel
  rw [hl, canonical2559 B hB] at h
  have hc0 : mixedMoment B raw2559 (Fin.cases (0 : Fin 2) singletonSmall5451) =
      mixedMoment B node3888 node3888Labels := by
    have ha : raw2559 = raw2560 := by apply Matrix.ext; unfold raw2559 raw2560; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5451 = raw2560Labels := by decide +kernel
    rw [ha, hj, canonical2560 B hB]
  have hc1 : mixedMoment B raw2559 (Fin.cases (1 : Fin 2) singletonSmall5451) =
      mixedMoment B node3913 node3913Labels := by
    have ha : raw2559 = raw2561 := by apply Matrix.ext; unfold raw2559 raw2561; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5451 = raw2561Labels := by decide +kernel
    rw [ha, hj, canonical2561 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5452 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5452 node5452Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3911 node3911Labels + mixedMoment B node4039 node4039Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2562 singletonSmall5452
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5452) = raw2562Labels := by decide +kernel
  rw [hl, canonical2562 B hB] at h
  have hc0 : mixedMoment B raw2562 (Fin.cases (0 : Fin 2) singletonSmall5452) =
      mixedMoment B node3911 node3911Labels := by
    have ha : raw2562 = raw2563 := by apply Matrix.ext; unfold raw2562 raw2563; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5452 = raw2563Labels := by decide +kernel
    rw [ha, hj, canonical2563 B hB]
  have hc1 : mixedMoment B raw2562 (Fin.cases (1 : Fin 2) singletonSmall5452) =
      mixedMoment B node4039 node4039Labels := by
    have ha : raw2562 = raw2564 := by apply Matrix.ext; unfold raw2562 raw2564; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5452 = raw2564Labels := by decide +kernel
    rw [ha, hj, canonical2564 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5453 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5453 node5453Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3912 node3912Labels + mixedMoment B node3912 node3912Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2565 singletonSmall5453
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5453) = raw2565Labels := by decide +kernel
  rw [hl, canonical2565 B hB] at h
  have hc0 : mixedMoment B raw2565 (Fin.cases (0 : Fin 2) singletonSmall5453) =
      mixedMoment B node3912 node3912Labels := by
    have ha : raw2565 = raw2566 := by apply Matrix.ext; unfold raw2565 raw2566; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5453 = raw2566Labels := by decide +kernel
    rw [ha, hj, canonical2566 B hB]
  have hc1 : mixedMoment B raw2565 (Fin.cases (1 : Fin 2) singletonSmall5453) =
      mixedMoment B node3912 node3912Labels := by
    have ha : raw2565 = raw2567 := by apply Matrix.ext; unfold raw2565 raw2567; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5453 = raw2567Labels := by decide +kernel
    rw [ha, hj, canonical2567 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5456 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5456 node5456Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3916 node3916Labels + mixedMoment B node3916 node3916Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2568 singletonSmall5456
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5456) = raw2568Labels := by decide +kernel
  rw [hl, canonical2568 B hB] at h
  have hc0 : mixedMoment B raw2568 (Fin.cases (0 : Fin 2) singletonSmall5456) =
      mixedMoment B node3916 node3916Labels := by
    have ha : raw2568 = raw2569 := by apply Matrix.ext; unfold raw2568 raw2569; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5456 = raw2569Labels := by decide +kernel
    rw [ha, hj, canonical2569 B hB]
  have hc1 : mixedMoment B raw2568 (Fin.cases (1 : Fin 2) singletonSmall5456) =
      mixedMoment B node3916 node3916Labels := by
    have ha : raw2568 = raw2570 := by apply Matrix.ext; unfold raw2568 raw2570; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5456 = raw2570Labels := by decide +kernel
    rw [ha, hj, canonical2570 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5464 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5464 node5464Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3930 node3930Labels + mixedMoment B node4041 node4041Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2571 singletonSmall5464
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5464) = raw2571Labels := by decide +kernel
  rw [hl, canonical2571 B hB] at h
  have hc0 : mixedMoment B raw2571 (Fin.cases (0 : Fin 2) singletonSmall5464) =
      mixedMoment B node3930 node3930Labels := by
    have ha : raw2571 = raw2572 := by apply Matrix.ext; unfold raw2571 raw2572; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5464 = raw2572Labels := by decide +kernel
    rw [ha, hj, canonical2572 B hB]
  have hc1 : mixedMoment B raw2571 (Fin.cases (1 : Fin 2) singletonSmall5464) =
      mixedMoment B node4041 node4041Labels := by
    have ha : raw2571 = raw2573 := by apply Matrix.ext; unfold raw2571 raw2573; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5464 = raw2573Labels := by decide +kernel
    rw [ha, hj, canonical2573 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5465 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5465 node5465Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3931 node3931Labels + mixedMoment B node4042 node4042Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2574 singletonSmall5465
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5465) = raw2574Labels := by decide +kernel
  rw [hl, canonical2574 B hB] at h
  have hc0 : mixedMoment B raw2574 (Fin.cases (0 : Fin 2) singletonSmall5465) =
      mixedMoment B node3931 node3931Labels := by
    have ha : raw2574 = raw2575 := by apply Matrix.ext; unfold raw2574 raw2575; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5465 = raw2575Labels := by decide +kernel
    rw [ha, hj, canonical2575 B hB]
  have hc1 : mixedMoment B raw2574 (Fin.cases (1 : Fin 2) singletonSmall5465) =
      mixedMoment B node4042 node4042Labels := by
    have ha : raw2574 = raw2576 := by apply Matrix.ext; unfold raw2574 raw2576; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5465 = raw2576Labels := by decide +kernel
    rw [ha, hj, canonical2576 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5466 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5466 node5466Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3934 node3934Labels + mixedMoment B node4043 node4043Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2577 singletonSmall5466
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5466) = raw2577Labels := by decide +kernel
  rw [hl, canonical2577 B hB] at h
  have hc0 : mixedMoment B raw2577 (Fin.cases (0 : Fin 2) singletonSmall5466) =
      mixedMoment B node3934 node3934Labels := by
    have ha : raw2577 = raw2578 := by apply Matrix.ext; unfold raw2577 raw2578; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5466 = raw2578Labels := by decide +kernel
    rw [ha, hj, canonical2578 B hB]
  have hc1 : mixedMoment B raw2577 (Fin.cases (1 : Fin 2) singletonSmall5466) =
      mixedMoment B node4043 node4043Labels := by
    have ha : raw2577 = raw2579 := by apply Matrix.ext; unfold raw2577 raw2579; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5466 = raw2579Labels := by decide +kernel
    rw [ha, hj, canonical2579 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5467 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5467 node5467Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3942 node3942Labels + mixedMoment B node3942 node3942Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2580 singletonSmall5467
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5467) = raw2580Labels := by decide +kernel
  rw [hl, canonical2580 B hB] at h
  have hc0 : mixedMoment B raw2580 (Fin.cases (0 : Fin 2) singletonSmall5467) =
      mixedMoment B node3942 node3942Labels := by
    have ha : raw2580 = raw2581 := by apply Matrix.ext; unfold raw2580 raw2581; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5467 = raw2581Labels := by decide +kernel
    rw [ha, hj, canonical2581 B hB]
  have hc1 : mixedMoment B raw2580 (Fin.cases (1 : Fin 2) singletonSmall5467) =
      mixedMoment B node3942 node3942Labels := by
    have ha : raw2580 = raw2582 := by apply Matrix.ext; unfold raw2580 raw2582; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5467 = raw2582Labels := by decide +kernel
    rw [ha, hj, canonical2582 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5469 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5469 node5469Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3945 node3945Labels + mixedMoment B node3952 node3952Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2583 singletonSmall5469
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5469) = raw2583Labels := by decide +kernel
  rw [hl, canonical2583 B hB] at h
  have hc0 : mixedMoment B raw2583 (Fin.cases (0 : Fin 2) singletonSmall5469) =
      mixedMoment B node3945 node3945Labels := by
    have ha : raw2583 = raw2584 := by apply Matrix.ext; unfold raw2583 raw2584; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5469 = raw2584Labels := by decide +kernel
    rw [ha, hj, canonical2584 B hB]
  have hc1 : mixedMoment B raw2583 (Fin.cases (1 : Fin 2) singletonSmall5469) =
      mixedMoment B node3952 node3952Labels := by
    have ha : raw2583 = raw2585 := by apply Matrix.ext; unfold raw2583 raw2585; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5469 = raw2585Labels := by decide +kernel
    rw [ha, hj, canonical2585 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5472 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5472 node5472Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3957 node3957Labels + mixedMoment B node3957 node3957Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2586 singletonSmall5472
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5472) = raw2586Labels := by decide +kernel
  rw [hl, canonical2586 B hB] at h
  have hc0 : mixedMoment B raw2586 (Fin.cases (0 : Fin 2) singletonSmall5472) =
      mixedMoment B node3957 node3957Labels := by
    have ha : raw2586 = raw2587 := by apply Matrix.ext; unfold raw2586 raw2587; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5472 = raw2587Labels := by decide +kernel
    rw [ha, hj, canonical2587 B hB]
  have hc1 : mixedMoment B raw2586 (Fin.cases (1 : Fin 2) singletonSmall5472) =
      mixedMoment B node3957 node3957Labels := by
    have ha : raw2586 = raw2588 := by apply Matrix.ext; unfold raw2586 raw2588; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5472 = raw2588Labels := by decide +kernel
    rw [ha, hj, canonical2588 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5473 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5473 node5473Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3958 node3958Labels + mixedMoment B node3961 node3961Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2589 singletonSmall5473
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5473) = raw2589Labels := by decide +kernel
  rw [hl, canonical2589 B hB] at h
  have hc0 : mixedMoment B raw2589 (Fin.cases (0 : Fin 2) singletonSmall5473) =
      mixedMoment B node3958 node3958Labels := by
    have ha : raw2589 = raw2590 := by apply Matrix.ext; unfold raw2589 raw2590; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5473 = raw2590Labels := by decide +kernel
    rw [ha, hj, canonical2590 B hB]
  have hc1 : mixedMoment B raw2589 (Fin.cases (1 : Fin 2) singletonSmall5473) =
      mixedMoment B node3961 node3961Labels := by
    have ha : raw2589 = raw2591 := by apply Matrix.ext; unfold raw2589 raw2591; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5473 = raw2591Labels := by decide +kernel
    rw [ha, hj, canonical2591 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5475 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5475 node5475Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3963 node3963Labels + mixedMoment B node3963 node3963Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2592 singletonSmall5475
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5475) = raw2592Labels := by decide +kernel
  rw [hl, canonical2592 B hB] at h
  have hc0 : mixedMoment B raw2592 (Fin.cases (0 : Fin 2) singletonSmall5475) =
      mixedMoment B node3963 node3963Labels := by
    have ha : raw2592 = raw2593 := by apply Matrix.ext; unfold raw2592 raw2593; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5475 = raw2593Labels := by decide +kernel
    rw [ha, hj, canonical2593 B hB]
  have hc1 : mixedMoment B raw2592 (Fin.cases (1 : Fin 2) singletonSmall5475) =
      mixedMoment B node3963 node3963Labels := by
    have ha : raw2592 = raw2594 := by apply Matrix.ext; unfold raw2592 raw2594; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5475 = raw2594Labels := by decide +kernel
    rw [ha, hj, canonical2594 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5476 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5476 node5476Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3965 node3965Labels + mixedMoment B node4045 node4045Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2595 singletonSmall5476
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5476) = raw2595Labels := by decide +kernel
  rw [hl, canonical2595 B hB] at h
  have hc0 : mixedMoment B raw2595 (Fin.cases (0 : Fin 2) singletonSmall5476) =
      mixedMoment B node3965 node3965Labels := by
    have ha : raw2595 = raw2596 := by apply Matrix.ext; unfold raw2595 raw2596; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5476 = raw2596Labels := by decide +kernel
    rw [ha, hj, canonical2596 B hB]
  have hc1 : mixedMoment B raw2595 (Fin.cases (1 : Fin 2) singletonSmall5476) =
      mixedMoment B node4045 node4045Labels := by
    have ha : raw2595 = raw2597 := by apply Matrix.ext; unfold raw2595 raw2597; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5476 = raw2597Labels := by decide +kernel
    rw [ha, hj, canonical2597 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5478 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5478 node5478Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3974 node3974Labels + mixedMoment B node3974 node3974Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2598 singletonSmall5478
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5478) = raw2598Labels := by decide +kernel
  rw [hl, canonical2598 B hB] at h
  have hc0 : mixedMoment B raw2598 (Fin.cases (0 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2599 := by apply Matrix.ext; unfold raw2598 raw2599; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5478 = raw2599Labels := by decide +kernel
    rw [ha, hj, canonical2599 B hB]
  have hc1 : mixedMoment B raw2598 (Fin.cases (1 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2600 := by apply Matrix.ext; unfold raw2598 raw2600; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5478 = raw2600Labels := by decide +kernel
    rw [ha, hj, canonical2600 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5482 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5482 node5482Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3980 node3980Labels + mixedMoment B node4046 node4046Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2601 singletonSmall5482
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5482) = raw2601Labels := by decide +kernel
  rw [hl, canonical2601 B hB] at h
  have hc0 : mixedMoment B raw2601 (Fin.cases (0 : Fin 2) singletonSmall5482) =
      mixedMoment B node3980 node3980Labels := by
    have ha : raw2601 = raw2602 := by apply Matrix.ext; unfold raw2601 raw2602; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5482 = raw2602Labels := by decide +kernel
    rw [ha, hj, canonical2602 B hB]
  have hc1 : mixedMoment B raw2601 (Fin.cases (1 : Fin 2) singletonSmall5482) =
      mixedMoment B node4046 node4046Labels := by
    have ha : raw2601 = raw2603 := by apply Matrix.ext; unfold raw2601 raw2603; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5482 = raw2603Labels := by decide +kernel
    rw [ha, hj, canonical2603 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5483 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5483 node5483Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3981 node3981Labels + mixedMoment B node4047 node4047Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2604 singletonSmall5483
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5483) = raw2604Labels := by decide +kernel
  rw [hl, canonical2604 B hB] at h
  have hc0 : mixedMoment B raw2604 (Fin.cases (0 : Fin 2) singletonSmall5483) =
      mixedMoment B node3981 node3981Labels := by
    have ha : raw2604 = raw2605 := by apply Matrix.ext; unfold raw2604 raw2605; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5483 = raw2605Labels := by decide +kernel
    rw [ha, hj, canonical2605 B hB]
  have hc1 : mixedMoment B raw2604 (Fin.cases (1 : Fin 2) singletonSmall5483) =
      mixedMoment B node4047 node4047Labels := by
    have ha : raw2604 = raw2606 := by apply Matrix.ext; unfold raw2604 raw2606; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5483 = raw2606Labels := by decide +kernel
    rw [ha, hj, canonical2606 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5484 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5484 node5484Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3983 node3983Labels + mixedMoment B node3983 node3983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2607 singletonSmall5484
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5484) = raw2607Labels := by decide +kernel
  rw [hl, canonical2607 B hB] at h
  have hc0 : mixedMoment B raw2607 (Fin.cases (0 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2608 := by apply Matrix.ext; unfold raw2607 raw2608; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5484 = raw2608Labels := by decide +kernel
    rw [ha, hj, canonical2608 B hB]
  have hc1 : mixedMoment B raw2607 (Fin.cases (1 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2609 := by apply Matrix.ext; unfold raw2607 raw2609; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5484 = raw2609Labels := by decide +kernel
    rw [ha, hj, canonical2609 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5485 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5485 node5485Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3984 node3984Labels + mixedMoment B node4010 node4010Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2610 singletonSmall5485
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5485) = raw2610Labels := by decide +kernel
  rw [hl, canonical2610 B hB] at h
  have hc0 : mixedMoment B raw2610 (Fin.cases (0 : Fin 2) singletonSmall5485) =
      mixedMoment B node3984 node3984Labels := by
    have ha : raw2610 = raw2611 := by apply Matrix.ext; unfold raw2610 raw2611; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5485 = raw2611Labels := by decide +kernel
    rw [ha, hj, canonical2611 B hB]
  have hc1 : mixedMoment B raw2610 (Fin.cases (1 : Fin 2) singletonSmall5485) =
      mixedMoment B node4010 node4010Labels := by
    have ha : raw2610 = raw2612 := by apply Matrix.ext; unfold raw2610 raw2612; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5485 = raw2612Labels := by decide +kernel
    rw [ha, hj, canonical2612 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5490 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5490 node5490Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4013 node4013Labels + mixedMoment B node4013 node4013Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2613 singletonSmall5490
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5490) = raw2613Labels := by decide +kernel
  rw [hl, canonical2613 B hB] at h
  have hc0 : mixedMoment B raw2613 (Fin.cases (0 : Fin 2) singletonSmall5490) =
      mixedMoment B node4013 node4013Labels := by
    have ha : raw2613 = raw2614 := by apply Matrix.ext; unfold raw2613 raw2614; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5490 = raw2614Labels := by decide +kernel
    rw [ha, hj, canonical2614 B hB]
  have hc1 : mixedMoment B raw2613 (Fin.cases (1 : Fin 2) singletonSmall5490) =
      mixedMoment B node4013 node4013Labels := by
    have ha : raw2613 = raw2615 := by apply Matrix.ext; unfold raw2613 raw2615; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5490 = raw2615Labels := by decide +kernel
    rw [ha, hj, canonical2615 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5491 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5491 node5491Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4014 node4014Labels + mixedMoment B node4014 node4014Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2616 singletonSmall5491
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5491) = raw2616Labels := by decide +kernel
  rw [hl, canonical2616 B hB] at h
  have hc0 : mixedMoment B raw2616 (Fin.cases (0 : Fin 2) singletonSmall5491) =
      mixedMoment B node4014 node4014Labels := by
    have ha : raw2616 = raw2617 := by apply Matrix.ext; unfold raw2616 raw2617; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5491 = raw2617Labels := by decide +kernel
    rw [ha, hj, canonical2617 B hB]
  have hc1 : mixedMoment B raw2616 (Fin.cases (1 : Fin 2) singletonSmall5491) =
      mixedMoment B node4014 node4014Labels := by
    have ha : raw2616 = raw2618 := by apply Matrix.ext; unfold raw2616 raw2618; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5491 = raw2618Labels := by decide +kernel
    rw [ha, hj, canonical2618 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5492 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5492 node5492Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4015 node4015Labels + mixedMoment B node4017 node4017Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2619 singletonSmall5492
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5492) = raw2619Labels := by decide +kernel
  rw [hl, canonical2619 B hB] at h
  have hc0 : mixedMoment B raw2619 (Fin.cases (0 : Fin 2) singletonSmall5492) =
      mixedMoment B node4015 node4015Labels := by
    have ha : raw2619 = raw2620 := by apply Matrix.ext; unfold raw2619 raw2620; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5492 = raw2620Labels := by decide +kernel
    rw [ha, hj, canonical2620 B hB]
  have hc1 : mixedMoment B raw2619 (Fin.cases (1 : Fin 2) singletonSmall5492) =
      mixedMoment B node4017 node4017Labels := by
    have ha : raw2619 = raw2621 := by apply Matrix.ext; unfold raw2619 raw2621; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5492 = raw2621Labels := by decide +kernel
    rw [ha, hj, canonical2621 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5494 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5494 node5494Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4020 node4020Labels + mixedMoment B node4020 node4020Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2622 singletonSmall5494
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5494) = raw2622Labels := by decide +kernel
  rw [hl, canonical2622 B hB] at h
  have hc0 : mixedMoment B raw2622 (Fin.cases (0 : Fin 2) singletonSmall5494) =
      mixedMoment B node4020 node4020Labels := by
    have ha : raw2622 = raw2623 := by apply Matrix.ext; unfold raw2622 raw2623; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5494 = raw2623Labels := by decide +kernel
    rw [ha, hj, canonical2623 B hB]
  have hc1 : mixedMoment B raw2622 (Fin.cases (1 : Fin 2) singletonSmall5494) =
      mixedMoment B node4020 node4020Labels := by
    have ha : raw2622 = raw2624 := by apply Matrix.ext; unfold raw2622 raw2624; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5494 = raw2624Labels := by decide +kernel
    rw [ha, hj, canonical2624 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5498 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5498 node5498Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4051 node4051Labels + mixedMoment B node4051 node4051Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2625 singletonSmall5498
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5498) = raw2625Labels := by decide +kernel
  rw [hl, canonical2625 B hB] at h
  have hc0 : mixedMoment B raw2625 (Fin.cases (0 : Fin 2) singletonSmall5498) =
      mixedMoment B node4051 node4051Labels := by
    have ha : raw2625 = raw2626 := by apply Matrix.ext; unfold raw2625 raw2626; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5498 = raw2626Labels := by decide +kernel
    rw [ha, hj, canonical2626 B hB]
  have hc1 : mixedMoment B raw2625 (Fin.cases (1 : Fin 2) singletonSmall5498) =
      mixedMoment B node4051 node4051Labels := by
    have ha : raw2625 = raw2627 := by apply Matrix.ext; unfold raw2625 raw2627; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5498 = raw2627Labels := by decide +kernel
    rw [ha, hj, canonical2627 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall5500 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton5500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5500 node5500Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4053 node4053Labels + mixedMoment B node4053 node4053Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2628 singletonSmall5500
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5500) = raw2628Labels := by decide +kernel
  rw [hl, canonical2628 B hB] at h
  have hc0 : mixedMoment B raw2628 (Fin.cases (0 : Fin 2) singletonSmall5500) =
      mixedMoment B node4053 node4053Labels := by
    have ha : raw2628 = raw2629 := by apply Matrix.ext; unfold raw2628 raw2629; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5500 = raw2629Labels := by decide +kernel
    rw [ha, hj, canonical2629 B hB]
  have hc1 : mixedMoment B raw2628 (Fin.cases (1 : Fin 2) singletonSmall5500) =
      mixedMoment B node4053 node4053Labels := by
    have ha : raw2628 = raw2630 := by apply Matrix.ext; unfold raw2628 raw2630; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5500 = raw2630Labels := by decide +kernel
    rw [ha, hj, canonical2630 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

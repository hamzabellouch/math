import Mathlib
import OAI.Combinatorics.StripMass.ThreeBoxWeights
import OAI.Combinatorics.StripMass.RootOfUnityPowers

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

theorem braid_numerator_0 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 0 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 0 := by
  rw [coefficient_0, coefficient_0]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_1 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 1 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 31 := by
  rw [coefficient_1, coefficient_31]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_2 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 2 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 28 := by
  rw [coefficient_2, coefficient_28]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq]
  all_goals ring

theorem braid_numerator_3 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 3 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 29 := by
  rw [coefficient_3, coefficient_29]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_4 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 4 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 24 := by
  rw [coefficient_4, coefficient_24]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_5 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 5 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 15 := by
  rw [coefficient_5, coefficient_15]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_6 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 6 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 16 := by
  rw [coefficient_6, coefficient_16]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_7 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 7 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 34 := by
  rw [coefficient_7, coefficient_34]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq]
  all_goals ring

theorem braid_numerator_8 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 8 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 33 := by
  rw [coefficient_8, coefficient_33]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq]
  all_goals ring

theorem braid_numerator_9 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 9 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 32 := by
  rw [coefficient_9, coefficient_32]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_10 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 10 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 10 := by
  rw [coefficient_10, coefficient_10]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_11 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 11 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 13 := by
  rw [coefficient_11, coefficient_13]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq]
  all_goals ring

theorem braid_numerator_12 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 12 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 12 := by
  rw [coefficient_12, coefficient_12]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_13 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 13 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 11 := by
  rw [coefficient_13, coefficient_11]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq]
  all_goals ring

theorem braid_numerator_14 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 14 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 46 := by
  rw [coefficient_14, coefficient_46]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_38 hq]
  all_goals ring

theorem braid_numerator_15 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 15 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 5 := by
  rw [coefficient_15, coefficient_5]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_16 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 16 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 6 := by
  rw [coefficient_16, coefficient_6]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_17 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 17 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 40 := by
  rw [coefficient_17, coefficient_40]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_38 hq]
  all_goals ring

theorem braid_numerator_18 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 18 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 18 := by
  rw [coefficient_18, coefficient_18]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_19 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 19 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 37 := by
  rw [coefficient_19, coefficient_37]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_20 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 20 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 26 := by
  rw [coefficient_20, coefficient_26]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_21 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 21 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 21 := by
  rw [coefficient_21, coefficient_21]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_22 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 22 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 47 := by
  rw [coefficient_22, coefficient_47]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_23 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 23 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 45 := by
  rw [coefficient_23, coefficient_45]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_24 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 24 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 4 := by
  rw [coefficient_24, coefficient_4]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_25 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 25 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 36 := by
  rw [coefficient_25, coefficient_36]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_26 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 26 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 20 := by
  rw [coefficient_26, coefficient_20]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_27 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 27 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 43 := by
  rw [coefficient_27, coefficient_43]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_28 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 28 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 2 := by
  rw [coefficient_28, coefficient_2]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq]
  all_goals ring

theorem braid_numerator_29 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 29 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 3 := by
  rw [coefficient_29, coefficient_3]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_30 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 30 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 44 := by
  rw [coefficient_30, coefficient_44]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq]
  all_goals ring

theorem braid_numerator_31 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 31 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 1 := by
  rw [coefficient_31, coefficient_1]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_32 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 32 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 9 := by
  rw [coefficient_32, coefficient_9]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_33 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 33 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 8 := by
  rw [coefficient_33, coefficient_8]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq]
  all_goals ring

theorem braid_numerator_34 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 34 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 7 := by
  rw [coefficient_34, coefficient_7]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq]
  all_goals ring

theorem braid_numerator_35 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 35 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 41 := by
  rw [coefficient_35, coefficient_41]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_36 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 36 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 25 := by
  rw [coefficient_36, coefficient_25]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_37 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 37 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 19 := by
  rw [coefficient_37, coefficient_19]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_38 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 38 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 42 := by
  rw [coefficient_38, coefficient_42]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_39 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 39 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 39 := by
  rw [coefficient_39, coefficient_39]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_40 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 40 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 17 := by
  rw [coefficient_40, coefficient_17]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_38 hq]
  all_goals ring

theorem braid_numerator_41 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 41 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 35 := by
  rw [coefficient_41, coefficient_35]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_42 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 42 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 38 := by
  rw [coefficient_42, coefficient_38]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_43 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 43 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 27 := by
  rw [coefficient_43, coefficient_27]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_44 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 44 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 30 := by
  rw [coefficient_44, coefficient_30]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq]
  all_goals ring

theorem braid_numerator_45 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 45 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 23 := by
  rw [coefficient_45, coefficient_23]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_46 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 46 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 14 := by
  rw [coefficient_46, coefficient_14]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_38 hq]
  all_goals ring

theorem braid_numerator_47 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 47 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 22 := by
  rw [coefficient_47, coefficient_22]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_48 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 48 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 50 := by
  rw [coefficient_48, coefficient_50]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_49 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 49 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 49 := by
  rw [coefficient_49, coefficient_49]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_50 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 50 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 48 := by
  rw [coefficient_50, coefficient_48]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) (k : Fin 51) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) k =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) (mirrorIndex k) := by
  fin_cases k
  · exact braid_numerator_0 q z w hq
  · exact braid_numerator_1 q z w hq
  · exact braid_numerator_2 q z w hq
  · exact braid_numerator_3 q z w hq
  · exact braid_numerator_4 q z w hq
  · exact braid_numerator_5 q z w hq
  · exact braid_numerator_6 q z w hq
  · exact braid_numerator_7 q z w hq
  · exact braid_numerator_8 q z w hq
  · exact braid_numerator_9 q z w hq
  · exact braid_numerator_10 q z w hq
  · exact braid_numerator_11 q z w hq
  · exact braid_numerator_12 q z w hq
  · exact braid_numerator_13 q z w hq
  · exact braid_numerator_14 q z w hq
  · exact braid_numerator_15 q z w hq
  · exact braid_numerator_16 q z w hq
  · exact braid_numerator_17 q z w hq
  · exact braid_numerator_18 q z w hq
  · exact braid_numerator_19 q z w hq
  · exact braid_numerator_20 q z w hq
  · exact braid_numerator_21 q z w hq
  · exact braid_numerator_22 q z w hq
  · exact braid_numerator_23 q z w hq
  · exact braid_numerator_24 q z w hq
  · exact braid_numerator_25 q z w hq
  · exact braid_numerator_26 q z w hq
  · exact braid_numerator_27 q z w hq
  · exact braid_numerator_28 q z w hq
  · exact braid_numerator_29 q z w hq
  · exact braid_numerator_30 q z w hq
  · exact braid_numerator_31 q z w hq
  · exact braid_numerator_32 q z w hq
  · exact braid_numerator_33 q z w hq
  · exact braid_numerator_34 q z w hq
  · exact braid_numerator_35 q z w hq
  · exact braid_numerator_36 q z w hq
  · exact braid_numerator_37 q z w hq
  · exact braid_numerator_38 q z w hq
  · exact braid_numerator_39 q z w hq
  · exact braid_numerator_40 q z w hq
  · exact braid_numerator_41 q z w hq
  · exact braid_numerator_42 q z w hq
  · exact braid_numerator_43 q z w hq
  · exact braid_numerator_44 q z w hq
  · exact braid_numerator_45 q z w hq
  · exact braid_numerator_46 q z w hq
  · exact braid_numerator_47 q z w hq
  · exact braid_numerator_48 q z w hq
  · exact braid_numerator_49 q z w hq
  · exact braid_numerator_50 q z w hq

end
end CriticalStrip.Diagram.ThreeBox

end OAI

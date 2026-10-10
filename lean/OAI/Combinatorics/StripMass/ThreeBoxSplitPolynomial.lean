import Mathlib
import OAI.Combinatorics.StripMass.ThreeBoxWeights
import OAI.Combinatorics.StripMass.RootOfUnityPowers

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

def deletionTile {K : Type*} [Zero K] [One K] : Tile → K
  | .vacant | .cap | .cup | .capCup => 1
  | _ => 0

def swapTile {K : Type*} [Zero K] [One K] : Tile → K
  | .vacant | .diagonal₀ | .diagonal₁ => 1
  | _ => 0

def mergeNumerator {K : Type*} [CommRing K] (q : K) : Tile → K
  | .vacant => q^2+1
  | .vertical₀ | .vertical₁ | .diagonal₀ | .diagonal₁ | .cap | .cup => q
  | _ => 0

def commonNumerator {K : Type*} [CommRing K] (q z : K) : K :=
  (q^4*z^2-1)*(q^6*z^2-1)

theorem split3_numerator_0 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 0 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 0 := by
  rw [coefficient_0, coefficient_0]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf

theorem split3_numerator_14 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 14 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 46 := by
  rw [coefficient_14, coefficient_46]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf

theorem split3_numerator_22 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 22 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 47 := by
  rw [coefficient_22, coefficient_47]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_28 hq]
  all_goals ring

theorem split3_numerator_23 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 23 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 45 := by
  rw [coefficient_23, coefficient_45]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf

theorem split3_numerator_27 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 27 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 43 := by
  rw [coefficient_27, coefficient_43]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq]
  all_goals ring

theorem split3_numerator_30 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 30 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 44 := by
  rw [coefficient_30, coefficient_44]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_32 hq]
  all_goals ring

theorem split3_numerator_48 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 48 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 50 := by
  rw [coefficient_48, coefficient_50]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq]
  all_goals ring

theorem split3_numerator_49 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 49 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 49 := by
  rw [coefficient_49, coefficient_49]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf

theorem split3_numerator_50 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 50 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 48 := by
  rw [coefficient_50, coefficient_48]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_17 hq, eighthRoot_power_23 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem split2_numerator_0 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 0 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 0 := by
  rw [coefficient_0, coefficient_0]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf

theorem split2_numerator_1 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 1 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 31 := by
  rw [coefficient_1, coefficient_31]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_44 hq]
  all_goals ring

theorem split2_numerator_7 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 7 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 34 := by
  rw [coefficient_7, coefficient_34]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_8 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 8 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 33 := by
  rw [coefficient_8, coefficient_33]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq]
  all_goals ring

theorem split2_numerator_9 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 9 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 32 := by
  rw [coefficient_9, coefficient_32]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_14 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 14 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 46 := by
  rw [coefficient_14, coefficient_46]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_44 hq]
  all_goals ring

theorem split2_numerator_17 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 17 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 40 := by
  rw [coefficient_17, coefficient_40]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf

theorem split2_numerator_19 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 19 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 37 := by
  rw [coefficient_19, coefficient_37]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq]
  all_goals ring

theorem split2_numerator_22 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 22 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 47 := by
  rw [coefficient_22, coefficient_47]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_23 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 23 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 45 := by
  rw [coefficient_23, coefficient_45]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_44 hq]
  all_goals ring

theorem split2_numerator_25 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 25 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 36 := by
  rw [coefficient_25, coefficient_36]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq]
  all_goals ring

theorem split2_numerator_27 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 27 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 43 := by
  rw [coefficient_27, coefficient_43]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_46 hq]
  all_goals ring

theorem split2_numerator_30 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 30 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 44 := by
  rw [coefficient_30, coefficient_44]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq]
  all_goals ring

theorem split2_numerator_35 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 35 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 41 := by
  rw [coefficient_35, coefficient_41]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_38 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 38 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 42 := by
  rw [coefficient_38, coefficient_42]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf

theorem split2_numerator_39 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 39 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 39 := by
  rw [coefficient_39, coefficient_39]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq]
  all_goals ring

theorem split2_numerator_41 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 41 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 35 := by
  rw [coefficient_41, coefficient_35]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq, eighthRoot_power_47 hq]
  all_goals ring

theorem split2_numerator_42 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 42 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 38 := by
  rw [coefficient_42, coefficient_38]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_44 hq]
  all_goals ring

theorem split2_numerator_48 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 48 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 50 := by
  rw [coefficient_48, coefficient_50]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq, eighthRoot_power_47 hq]
  all_goals ring

theorem split2_numerator_49 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 49 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 49 := by
  rw [coefficient_49, coefficient_49]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_50 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 50 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 48 := by
  rw [coefficient_50, coefficient_48]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq]
  all_goals ring


 

 

open Finset

 

def diagramExterior {B : Type*} (d : Finset (Fin 6 × Fin 6))
    (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop) (x y : B) : Prop :=
  s x y ∨ ∃ i j, active i ∧ active j ∧ (i=j ∨ boundaryAdj d i j) ∧ x=b i ∧ y=b j

theorem realizes_boundary_reach {t : Config} {d : Finset (Fin 6 × Fin 6)}
    (h : Realizes t d) (i j : Fin 6) :
    Relation.ReflTransGen (Adj t) (boundary i) (boundary j) ↔ i=j ∨ boundaryAdj d i j := by
  by_cases he : i=j
  · subst j
    simp only [true_or, iff_true]
    exact .refl
  · simp only [he, false_or]
    exact (h.output i j he).symm

theorem realizes_compressed {B : Type*} {t : Config} {d : Finset (Fin 6 × Fin 6)}
    (h : Realizes t d) (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop) :
    Patch.compressed (Adj t) s boundary b active = diagramExterior d s b active := by
  funext x y
  apply propext
  simp only [Patch.compressed, diagramExterior, realizes_boundary_reach h]

theorem substitute_reach {B : Type*} {t : Config} {d : Finset (Fin 6 × Fin 6)}
    (h : Realizes t d) (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop)
    (x y : B) :
    Relation.ReflTransGen (Patch.glued (Adj t) s boundary b active) (.inr x) (.inr y) ↔
      Relation.ReflTransGen (diagramExterior d s b active) x y := by
  rw [Patch.exterior_reach_iff, realizes_compressed h]

theorem substitute_drains {B : Type*} {t : Config} {d : Finset (Fin 6 × Fin 6)}
    (h : Realizes t d) (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop)
    (ha : ∀ i, active i ↔ boundaryOccupied t i) (out : B → Prop) :
    Patch.drains (Patch.glued (Adj t) s boundary b active) (Patch.exteriorOutput out) ↔
      Patch.drains (diagramExterior d s b active) out := by
  rw [Patch.drains_glued_iff, realizes_compressed h]
  apply and_iff_right
  intro x y hxy
  obtain ⟨i,hi,hr⟩ := h.no_loop x y hxy
  exact ⟨i,(ha i).mpr hi,hr⟩

 

theorem profile_exists_of_drains {B : Type*} {t : Config} (hc : Compatible t)
    (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop)
    (ha : ∀ i, active i ↔ boundaryOccupied t i) (out : B → Prop)
    (hd : Patch.drains (Patch.glued (Adj t) s boundary b active) (Patch.exteriorOutput out)) :
    ∃ k, profile t = some k := by
  have hl := ((Patch.drains_glued_iff (Adj t) s boundary b active out).mp hd).1
  have hclean : Clean t := by
    intro x y hxy
    obtain ⟨i,hi,hr⟩ := hl x y hxy
    exact ⟨i,(ha i).mp hi,(reach_iff_root_eq t hc x (boundary i)).mp hr⟩
  have hp := profileCorrect t
  unfold ProfileCorrect at hp
  cases he : profile t with
  | none =>
    rw [he] at hp
    exact (hp.elim (fun hh => hh hc) (fun hh => hh hclean)).elim
  | some k => exact ⟨k,rfl⟩

 

def exteriorTest {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (out : B → Prop)
    (test : (B → B → Prop) → Prop) (k : Fin 51) : Prop :=
  (∀ i, active i ↔ boundarySupport (diagram k) i) ∧
  Patch.drains (diagramExterior (diagram k) s b active) out ∧
  test (Relation.ReflTransGen (diagramExterior (diagram k) s b active))

def patchTest {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (out : B → Prop)
    (test : (B → B → Prop) → Prop) (t : Config) : Prop :=
  Compatible t ∧ (∀ i, active i ↔ boundaryOccupied t i) ∧
  Patch.drains (Patch.glued (Adj t) s boundary b active) (Patch.exteriorOutput out) ∧
  test (fun x y => Relation.ReflTransGen (Patch.glued (Adj t) s boundary b active) (.inr x) (.inr y))

theorem patchTest_iff {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (out : B → Prop) (test : (B → B → Prop) → Prop)
    (t : Config) :
    patchTest s b active out test t ↔
      ∃ k, profile t = some k ∧ exteriorTest s b active out test k := by
  constructor
  · rintro ⟨hc,ha,hd,ht⟩
    obtain ⟨k,hk⟩ := profile_exists_of_drains hc s b active ha out hd
    have hr := profile_some_iff.mp hk
    refine ⟨k,hk,?_,(substitute_drains hr s b active ha out).mp hd,?_⟩
    · exact fun i => (ha i).trans (hr.occupied i)
    · have he : (fun x y => Relation.ReflTransGen
          (Patch.glued (Adj t) s boundary b active) (.inr x) (.inr y)) =
          Relation.ReflTransGen (diagramExterior (diagram k) s b active) := by
        funext x y
        exact propext (substitute_reach hr s b active x y)
      rwa [← he]
  · rintro ⟨k,hk,ha,hd,ht⟩
    have hr := profile_some_iff.mp hk
    have ha' : ∀ i, active i ↔ boundaryOccupied t i :=
      fun i => (ha i).trans (hr.occupied i).symm
    refine ⟨hr.compatible,ha',(substitute_drains hr s b active ha' out).mpr hd,?_⟩
    have he : (fun x y => Relation.ReflTransGen
        (Patch.glued (Adj t) s boundary b active) (.inr x) (.inr y)) =
        Relation.ReflTransGen (diagramExterior (diagram k) s b active) := by
      funext x y
      exact propext (substitute_reach hr s b active x y)
    simpa only [he] using ht

end
end CriticalStrip.Diagram.ThreeBox

end OAI

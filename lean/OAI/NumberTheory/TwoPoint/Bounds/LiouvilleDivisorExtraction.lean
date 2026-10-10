import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeDivisorBins
import OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix

namespace OAI

/-! The exact partial-centering substitution n=u*v. Only u must be a
unit modulo l; the progression class and the removed product may be nonunits. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma unit_progression_cancel (l : ℕ) (b : ZMod l) (u z v : ℕ)
    (hu : IsUnit (u : ZMod l)) :
    ((u * v : ℕ) : ZMod l) = b * ((u * z : ℕ) : ZMod l) ↔
      (v : ZMod l) = b * (z : ZMod l) := by
  simp only [Nat.cast_mul]
  rw [show b * ((u : ZMod l) * z) = (u : ZMod l) * (b * z) by ring,
    hu.mul_right_inj]

lemma liouville_pair_dilate (u v z h : ℕ) (hu : 0 < u) :
    liouville (u * v) * liouville (u * v + h * (u * z)) =
      liouville v * liouville (v + h * z) := by
  rw [show u * v + h * (u * z) = u * (v + h * z) by ring]
  simp only [liouville_mul]
  calc
    _ = liouville u ^ 2 * (liouville v * liouville (v + h * z)) := by ring
    _ = _ := by rw [liouville_sq hu.ne', one_mul]

lemma liouville_progression_dilate (l : ℕ) [NeZero l] (b : ZMod l)
    (u v z h : ℕ) (hu : 0 < u) (hunit : IsUnit (u : ZMod l)) :
    progressionSequence liouville l (b * ((u * z : ℕ) : ZMod l)) (u * v) *
        liouville (u * v + h * (u * z)) =
      progressionSequence liouville l (b * (z : ZMod l)) v * liouville (v + h * z) := by
  simp only [progressionSequence, unit_progression_cancel l b u z v hunit]
  split_ifs
  · exact liouville_pair_dilate u v z h hu
  · simp only [zero_mul]

noncomputable def partialLiouvilleProfile (l : ℕ) [NeZero l] (b : ZMod l)
    (u : ℕ) (Z : Finset ℕ) (h n : ℕ) : ℂ :=
  natDivisibilityIndicator u n * ∑ z ∈ Z, (z : ℂ)⁻¹ *
    (progressionSequence liouville l (b * ((u * z : ℕ) : ZMod l)) n *
      liouville (n + h * (u * z)))

lemma partialLiouvilleProfile_prefix (l : ℕ) [NeZero l] (b : ZMod l)
    (u : ℕ) (Z : Finset ℕ) (h X : ℕ) (hu : 0 < u)
    (hunit : IsUnit (u : ZMod l)) :
    positivePrefix (partialLiouvilleProfile l b u Z h) X =
      positivePrefix (residueScaledRoughProfile l b Z h) (X / u) := by
  unfold partialLiouvilleProfile
  rw [divisibility_positivePrefix _ u X hu]
  congr 1
  funext v
  apply sum_congr rfl
  intro z _
  rw [liouville_progression_dilate l b u v z h hu hunit]

lemma natDivisibilityIndicator_mul (a b n : ℕ) (hab : a.Coprime b) :
    natDivisibilityIndicator a n * natDivisibilityIndicator b n =
      natDivisibilityIndicator (a * b) n := by
  have he : a * b ∣ n ↔ a ∣ n ∧ b ∣ n :=
    ⟨fun h => ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩,
      fun h => hab.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  simp only [natDivisibilityIndicator, he]
  split_ifs <;> simp_all

end TwoPointCorrelations

end OAI

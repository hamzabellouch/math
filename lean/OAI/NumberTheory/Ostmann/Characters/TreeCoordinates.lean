import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.Tree.BottomPairCoordinates

namespace OAI

/-!
# Rational coordinates at a tree split

These identities are equations `tree-difference-ratio`, `tree-held-square`,
and `tree-p-square` of the manuscript. Nonzero hypotheses state precisely
that the reconstructed node is valid.
-/

namespace Ostmann

def reconstructedEntry {K : Type*} [Field K] (s sL sR u HL HR : K) : K :=
  (sL * HR - sR * HL) / (s * u)

def parentArgument {K : Type*} [Field K] (s D HL HR : K) : K := s / (D * HL * HR)

def childArgument {K : Type*} [Field K] (s D u H P : K) : K := s / (D * P * u * H)

theorem reconstructedEntry_relation {K : Type*} [Field K]
    (s sL sR u HL HR : K) (hs : s ≠ 0) (hu : u ≠ 0) :
    reconstructedEntry s sL sR u HL HR * (s * u) = sL * HR - sR * HL := by
  exact div_mul_cancel₀ _ (mul_ne_zero hs hu)

theorem tree_child_difference {K : Type*} [Field K]
    (s sL sR D u HL HR P : K)
    (hD : D ≠ 0) (hu : u ≠ 0) (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0)
    (hrel : P * (s * u) = sL * HR - sR * HL) :
    childArgument sL D u HL P - childArgument sR D u HR P = parentArgument s D HL HR := by
  unfold childArgument parentArgument
  field_simp
  linear_combination -hrel

theorem tree_child_ratio {K : Type*} [Field K]
    (sL sR D u HL HR P : K)
    (hsR : sR ≠ 0) (hD : D ≠ 0) (hu : u ≠ 0)
    (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0) :
    childArgument sL D u HL P / childArgument sR D u HR P = (sL / sR) * (HR / HL) := by
  unfold childArgument
  field_simp

theorem tree_reconstructed_square {K : Type*} [Field K]
    (s sL sR D u HL HR P : K)
    (hs : s ≠ 0) (hsL : sL ≠ 0) (hsR : sR ≠ 0)
    (hD : D ≠ 0) (hu : u ≠ 0) (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0) :
    P ^ 2 = (sL * sR / (s * D * u ^ 2)) *
      parentArgument s D HL HR /
        (childArgument sL D u HL P * childArgument sR D u HR P) := by
  unfold parentArgument childArgument
  field_simp

theorem tree_held_square {K : Type*} [Field K]
    (sPair sFree sHeld D u HFree HHeld P : K)
    (hsPair : sPair ≠ 0) (hsHeld : sHeld ≠ 0) (hD : D ≠ 0)
    (hu : u ≠ 0) (hFree : HFree ≠ 0) (hHeld : HHeld ≠ 0) (hP : P ≠ 0) :
    (childArgument sFree D u HFree P / childArgument sHeld D u HHeld P) /
        parentArgument sPair D HFree HHeld =
      (D * sFree / (sHeld * sPair)) * HHeld ^ 2 := by
  unfold childArgument parentArgument
  field_simp

/-- Exposing a child product makes its ratio an inverse square of the free product. -/
theorem tree_product_ratio {G : Type*} [CommGroup G]
    (sL sR XL XR CL CR P m : G) :
    (sL / sR) * ((XR * CR * (P / m)) / (XL * CL * m)) =
      ((sL / sR) * (XR * CR * P / (XL * CL))) * (m⁻¹) ^ 2 := by
  simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- Difference and ratio identify the child arguments with the sampling coordinates. -/
theorem children_eq_pair_coordinates {K : Type*} [Field K]
    (x z d t : K) (hz : z ≠ 0) (hd : d ≠ 0)
    (hdiff : x - z = d) (hratio : x / z = t) :
    (x, z) = (d * t / (t - 1), d / (t - 1)) := by
  have hxz : x ≠ z := by intro h; apply hd; rw [← hdiff, h, sub_self]
  rw [← hdiff, ← hratio]
  exact (pair_coordinates_reconstruct x z hz hxz).symm

/-- The rational tree formulas produce exactly the pair used by the density model. -/
theorem tree_children_eq_pair_coordinates {K : Type*} [Field K]
    (s sL sR D u HL HR P : K)
    (hs : s ≠ 0) (hsR : sR ≠ 0) (hD : D ≠ 0) (hu : u ≠ 0)
    (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0)
    (hrel : P * (s * u) = sL * HR - sR * HL) :
    (childArgument sL D u HL P, childArgument sR D u HR P) =
      (parentArgument s D HL HR * ((sL / sR) * (HR / HL)) /
        ((sL / sR) * (HR / HL) - 1),
       parentArgument s D HL HR / ((sL / sR) * (HR / HL) - 1)) := by
  apply children_eq_pair_coordinates
  · exact div_ne_zero hsR (by simp only [ne_eq, mul_eq_zero, hD, hP, hu, hR, or_self, not_false_eq_true])
  · exact div_ne_zero hs (mul_ne_zero (mul_ne_zero hD hL) hR)
  · exact tree_child_difference s sL sR D u HL HR P hD hu hL hR hP hrel
  · exact tree_child_ratio sL sR D u HL HR P hsR hD hu hL hR hP

/-- A reconstructed node is invalid precisely at the singular child ratio. -/
theorem reconstructedEntry_zero_iff_ratio_one {K : Type*} [Field K]
    (s sL sR u HL HR : K) (hs : s ≠ 0) (hsR : sR ≠ 0)
    (hu : u ≠ 0) (hL : HL ≠ 0) :
    reconstructedEntry s sL sR u HL HR = 0 ↔ (sL / sR) * (HR / HL) = 1 := by
  have hden : sR * HL ≠ 0 := mul_ne_zero hsR hL
  have heq : (sL / sR) * (HR / HL) = (sL * HR) / (sR * HL) := by ring
  rw [heq, div_eq_one_iff_eq hden]
  unfold reconstructedEntry
  rw [div_eq_zero_iff, or_iff_left (mul_ne_zero hs hu), sub_eq_zero]

/-- At a fixed node product the root argument is independent of the free split. -/
theorem tree_parent_fixed_product {K : Type*} [Field K]
    (s D XL XR CL CR P m : K) (hm : m ≠ 0) :
    parentArgument s D (XL * CL * m) (XR * CR * (P / m)) =
      s / (D * XL * CL * XR * CR * P) := by
  unfold parentArgument
  congr 1
  field_simp

end Ostmann

end OAI

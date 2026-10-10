import OAI.NumberTheory.TwoPoint.PublishedInputs
import Mathlib.Analysis.Fourier.ZMod

namespace OAI

/-!
# Additive Fourier resolution of every progression class

The coefficient mass is exactly one. There is no invertibility assumption
on the class, and no frequency supremum is put inside an integral.
-/

namespace TwoPointCorrelations

open scoped BigOperators

theorem additiveCharacter_add (α β : ℝ) (n : ℕ) :
    additiveCharacter (α + β) n = additiveCharacter α n * additiveCharacter β n := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stdAddChar_nat_mul (l : ℕ) [NeZero l] (a : ZMod l) (n : ℕ) :
    ZMod.stdAddChar (a * (n : ZMod l)) = additiveCharacter ((a.val : ℝ) / l) n := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a, ← Nat.cast_mul]
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

theorem zmod_indicator_fourier (l : ℕ) [NeZero l] (n b : ZMod l) :
    (if n = b then (1 : ℂ) else 0) =
      (l : ℂ)⁻¹ * ∑ a : ZMod l, ZMod.stdAddChar (a * (n - b)) := by
  classical
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar l), ZMod.card]
  have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne l
  by_cases h : n = b
  · simp [h, hlc]
  · simp [h, sub_ne_zero.mpr h]

theorem progression_fourier_identity (S : Finset ℕ) (v : ℕ → ℂ)
    (l : ℕ) [NeZero l] (b : ZMod l) (α : ℝ) :
    (∑ n ∈ S, if (n : ZMod l) = b then v n * additiveCharacter α n else 0) =
      (l : ℂ)⁻¹ * ∑ a : ZMod l, ZMod.stdAddChar (-(a * b)) *
        ∑ n ∈ S, v n * additiveCharacter (α + (a.val : ℝ) / l) n := by
  classical
  have hi (n : ℕ) :
      (if (n : ZMod l) = b then v n * additiveCharacter α n else 0) =
        (l : ℂ)⁻¹ * ∑ a : ZMod l,
          ZMod.stdAddChar (-(a * b)) * (v n * additiveCharacter (α + (a.val : ℝ) / l) n) := by
    have h := congrArg (fun z : ℂ => z * (v n * additiveCharacter α n))
      (zmod_indicator_fourier l (n : ZMod l) b)
    simp only [ite_mul, one_mul, zero_mul] at h
    rw [h, mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [additiveCharacter_add, ← stdAddChar_nat_mul l a n]
    have hm : a * ((n : ZMod l) - b) = -(a * b) + a * n := by ring
    rw [hm, AddChar.map_add_eq_mul]
    ring
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

/-- The progression mask averages `l` shifted frequencies with total
absolute coefficient mass one. -/
theorem norm_progression_fourier_le (S : Finset ℕ) (v : ℕ → ℂ)
    (l : ℕ) [NeZero l] (b : ZMod l) (α : ℝ) :
    ‖∑ n ∈ S, if (n : ZMod l) = b then v n * additiveCharacter α n else 0‖ ≤
      (l : ℝ)⁻¹ * ∑ a : ZMod l,
        ‖∑ n ∈ S, v n * additiveCharacter (α + (a.val : ℝ) / l) n‖ := by
  rw [progression_fourier_identity, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg l))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul, le_refl]

end TwoPointCorrelations

end OAI

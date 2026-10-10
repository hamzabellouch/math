import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-!
Finite weighted deficits used after the actual leaf-switching estimates.

The scalar argument allows zero leaf weights and returns a positive-weight leaf.
The application constructs its vectors using the strictly positive path weights,
then supplies the row estimates through `block_deficit_of_detection`.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- Sum of the nonnegative deficits on the path incident to a leaf. -/
def pathDeficit {V S : Type*} [Fintype V]
    (R : V → S → Prop) [DecidableRel R]
    (a : V → S → ℝ) (s : S) : ℝ :=
  ∑ v, if R v s then 1 - a v s else 0

/-- Equality at the threshold is bad, so a good leaf has a strict inequality. -/
def IsBadLeaf {V S : Type*}
    (R : V → S → Prop) (a : V → S → ℝ) (s : S) : Prop :=
  ∃ v, R v s ∧ a v s ≤ (1 : ℝ) / 2

/-- The total weight of leaves with at least one failing incident detector. -/
def badLeafMass {V S : Type*} [Fintype S]
    (R : V → S → Prop) (w : S → ℝ) (a : V → S → ℝ) : ℝ := by
  classical
  exact ∑ s, if IsBadLeaf R a s then w s else 0

/-- Finite double counting gives a common leaf without a lower bound on weights.

The first two conclusions retain the quantitative estimates. The
selected leaf has positive weight and satisfies every incident detector strictly.
-/
theorem finite_weighted_deficit
    {V S : Type*} [Fintype V] [Fintype S]
    (R : V → S → Prop) [DecidableRel R]
    (w : S → ℝ) (e : V → ℝ) (a : V → S → ℝ)
    (hw : ∀ s, 0 ≤ w s)
    (hw_sum : (∑ s, w s) = 1)
    (ha : ∀ v s, R v s → a v s ≤ 1)
    (hrow : ∀ v,
      (∑ s, if R v s then w s * (1 - a v s) else 0) ≤ 5 * e v)
    (he_sum : (∑ v, e v) ≤ (1 : ℝ) / 128) :
    (∑ s, w s * pathDeficit R a s) ≤ (5 : ℝ) / 128 ∧
      badLeafMass R w a ≤ (5 : ℝ) / 64 ∧
      ∃ s, 0 < w s ∧ ∀ v, R v s → (1 : ℝ) / 2 < a v s := by
  classical
  have hterm (v : V) (s : S) :
      0 ≤ (if R v s then 1 - a v s else 0) := by
    by_cases h : R v s
    · simpa only [ite_eq_left h] using sub_nonneg.mpr (ha v s h)
    · simp only [ite_eq_right h, le_refl]
  have hpath (s : S) : 0 ≤ pathDeficit R a s := by
    exact Finset.sum_nonneg fun v _ => hterm v s
  have hexchange :
      (∑ s, w s * pathDeficit R a s) =
        ∑ v, ∑ s, if R v s then w s * (1 - a v s) else 0 := by
    simp only [pathDeficit, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : R v s <;> simp only [h, ite_true, ite_false, mul_zero]
  have htotal :
      (∑ s, w s * pathDeficit R a s) ≤ (5 : ℝ) / 128 := by
    calc
      (∑ s, w s * pathDeficit R a s) =
          ∑ v, ∑ s, if R v s then w s * (1 - a v s) else 0 := hexchange
      _ ≤ ∑ v, 5 * e v := Finset.sum_le_sum fun v _ => hrow v
      _ = 5 * ∑ v, e v := (Finset.mul_sum _ _ _).symm
      _ ≤ (5 : ℝ) / 128 := by linarith
  have hbad_path (s : S) (hs : IsBadLeaf R a s) :
      (1 : ℝ) / 2 ≤ pathDeficit R a s := by
    obtain ⟨v, hv, hva⟩ := hs
    have hsingle := Finset.single_le_sum
      (fun u (_ : u ∈ (Finset.univ : Finset V)) => hterm u s)
      (Finset.mem_univ v)
    change (if R v s then 1 - a v s else 0) ≤ pathDeficit R a s at hsingle
    rw [ite_eq_left hv] at hsingle
    linarith
  have hbad_half :
      badLeafMass R w a / 2 ≤ ∑ s, w s * pathDeficit R a s := by
    unfold badLeafMass
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : IsBadLeaf R a s
    · rw [ite_eq_left hs]
      have hmul := mul_le_mul_of_nonneg_left (hbad_path s hs) (hw s)
      simpa only [div_eq_mul_inv, one_mul] using hmul
    · rw [ite_eq_right hs, zero_div]
      exact mul_nonneg (hw s) (hpath s)
  have hbad_mass : badLeafMass R w a ≤ (5 : ℝ) / 64 := by
    linarith
  refine ⟨htotal, hbad_mass, ?_⟩
  by_contra hnone
  have hbad_of_pos (s : S) (hs : 0 < w s) : IsBadLeaf R a s := by
    by_contra hgood
    apply hnone
    refine ⟨s, hs, ?_⟩
    intro v hv
    apply lt_of_not_ge
    intro hle
    exact hgood ⟨v, hv, hle⟩
  have hmass_one : badLeafMass R w a = 1 := by
    calc
      badLeafMass R w a = ∑ s, w s := by
        unfold badLeafMass
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : 0 < w s
        · exact ite_eq_left (hbad_of_pos s hs)
        · have hz : w s = 0 := le_antisymm (le_of_not_gt hs) (hw s)
          simp only [hz, ite_self]
      _ = 1 := hw_sum
  linarith

/-- A block's actual telescoping identity turns detection into weighted deficit.

Only the detector is linear. The block outputs may come from nonlinear maps;
their actual finite telescoping identity is the input `htelescope`.
-/
theorem block_deficit_of_detection
    {X S : Type*} [AddCommGroup X] [Module ℝ X]
    (block : Finset S) (w : S → ℝ) (d : S → X)
    (f : X →ₗ[ℝ] ℝ) (U V : X) (W e : ℝ)
    (hmass : (∑ s ∈ block, w s) = W)
    (htelescope : (∑ s ∈ block, w s • d s) = U - V)
    (hdetect : W - 5 * e ≤ f (U - V)) :
    (∑ s ∈ block, w s * (1 - f (d s))) ≤ 5 * e := by
  have hlinear : (∑ s ∈ block, w s * f (d s)) = f (U - V) := by
    rw [← htelescope, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [map_smul, smul_eq_mul]
  calc
    (∑ s ∈ block, w s * (1 - f (d s))) = W - f (U - V) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hmass, hlinear]
    _ ≤ 5 * e := by linarith

end ReflexiveFixedPoints

end

end OAI

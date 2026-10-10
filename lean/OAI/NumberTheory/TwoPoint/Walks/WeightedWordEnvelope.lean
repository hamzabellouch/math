import OAI.NumberTheory.TwoPoint.Bounds.WeightedDivisorWord
import OAI.NumberTheory.TwoPoint.Bounds.ObservedDesignationWeights

namespace OAI

/-! A single positive envelope for all lit designations of a weighted centered word. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def centeredWordEnvelope {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] {A : Type*} [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base : ι → A)
    (R G : (ι → A) → ℝ) (x : ι → A) : ℝ :=
  ∑ U ∈ (nonsingletonSlots label).powerset,
    if LitConsistent (nonsingletonSlots label \ U) label target then
      R x * |selectedMixedDifference (singletonLabels label)
        (singletonTarget label target base)
        (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|
    else 0

lemma centeredWordEnvelope_nonneg {ι τ A : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base : ι → A)
    (R G : (ι → A) → ℝ) (hR : ∀ x, 0 ≤ R x) (x : ι → A) :
    0 ≤ centeredWordEnvelope label target base R G x := by
  apply sum_nonneg
  intro U _
  split_ifs
  · exact mul_nonneg (hR x) (abs_nonneg _)
  · exact le_rfl

lemma centeredWordEnvelope_le {ι τ A : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base : ι → A)
    (R G : (ι → A) → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hRC : ∀ x, R x ≤ C)
    (hG : ∀ x, |G x| ≤ 1) (x : ι → A) :
    centeredWordEnvelope label target base R G x ≤
      C * 2 ^ (Fintype.card τ + (singletonLabels label).card) := by
  have hi (U : Finset τ) :
      (if LitConsistent (nonsingletonSlots label \ U) label target then
        R x * |selectedMixedDifference (singletonLabels label)
          (singletonTarget label target base)
          (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|
      else 0) ≤ C * 2 ^ (singletonLabels label).card := by
    split_ifs
    · exact mul_le_mul (hRC x)
        (selectedMixedDifference_bound _ _ _ (fun _ => hG _) x)
        (abs_nonneg _) hC
    · positivity
  calc
    _ ≤ ∑ _U ∈ (nonsingletonSlots label).powerset,
        C * 2 ^ (singletonLabels label).card := sum_le_sum (fun U _ => hi U)
    _ = ((nonsingletonSlots label).powerset.card : ℝ) *
        (C * 2 ^ (singletonLabels label).card) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ Fintype.card τ * (C * 2 ^ (singletonLabels label).card) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [card_powerset, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num) (card_le_univ _)
    _ = _ := by rw [pow_add]; ring

lemma centeredWordEnvelope_ne_zero {ι τ A : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base : ι → A)
    (R G : (ι → A) → ℝ) (x : ι → A)
    (hx : centeredWordEnvelope label target base R G x ≠ 0) :
    ∃ U ∈ (nonsingletonSlots label).powerset,
      LitConsistent (nonsingletonSlots label \ U) label target ∧ R x ≠ 0 ∧
      selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
        (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x ≠ 0 := by
  by_contra hn
  apply hx
  apply sum_eq_zero
  intro U hU
  split_ifs with hL
  · by_cases hRx : R x = 0
    · rw [hRx, zero_mul]
    · have hd : selectedMixedDifference (singletonLabels label)
          (singletonTarget label target base)
          (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x = 0 := by
        by_contra hd
        exact hn ⟨U, hU, hL, hRx, hd⟩
      rw [hd, abs_zero, mul_zero]
  · rfl

theorem uniform_weighted_centered_word_envelope {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t))
    (R G : (ι → Fin B) → ℝ) (hR : ∀ x, 0 ≤ R x)
    (hRdep : ∀ x y, (∀ i, i ∉ univ.image label → x i = y i) → R x = R y) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => R x * (∏ t,
        ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x)| ≤
      (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) *
        (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
          (centeredWordEnvelope label target base R G) := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  apply (uniform_weighted_centered_word_majorant B p hp hpB label target base
    htarget R G hR hRdep).trans
  calc
    _ ≤ ∑ U ∈ (nonsingletonSlots label).powerset,
        (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) * μ.average
          (fun x => if LitConsistent (nonsingletonSlots label \ U) label target then
            R x * |selectedMixedDifference (singletonLabels label)
              (singletonTarget label target base)
              (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
                (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|
          else 0) := by
      apply sum_le_sum
      intro U hU
      split_ifs
      · apply mul_le_mul_of_nonneg_right
        · simpa only [inv_one, one_pow, mul_one] using
            full_word_designated_reciprocal_bound label U (mem_powerset.mp hU) p 1
              (by norm_num) (fun i => by exact_mod_cast hp i)
        · exact μ.average_nonneg (fun x => mul_nonneg (hR x) (abs_nonneg _))
      · simp only [FiniteLaw.average_const, mul_zero, le_refl]
    _ = _ := by
      rw [← mul_sum]
      congr 1
      simp only [centeredWordEnvelope, FiniteLaw.average, mul_sum]
      rw [sum_comm]

end TwoPointCorrelations

end OAI

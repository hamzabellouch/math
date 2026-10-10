import OAI.NumberTheory.TwoPoint.Bounds.WeightedCenteredWord
import OAI.NumberTheory.TwoPoint.Bounds.ObservedReciprocalBound
import OAI.NumberTheory.TwoPoint.Walks.RetainedMainProbability
import OAI.NumberTheory.TwoPoint.Bounds.FiniteSupportAverage
import OAI.NumberTheory.TwoPoint.Bounds.ForcedSingletonDifference

namespace OAI

/-! A designated trace term retains its extra-reciprocal saving and pays actual padding tests. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem weighted_designation_bound {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (B h : ℕ) (p : ι → ℕ) (hinj : Function.Injective p)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (main : List SignedStep) (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (U : Finset τ) (hU : U ⊆ nonsingletonSlots label) (H C : ℝ)
    (hH : 0 < H) (hC : 0 ≤ C) (hpH : ∀ i ∈ nonsingletonLabels label, H ≤ p i)
    (hS : ∀ i ∈ univ.image label, p i ∈ wordDivisorPrimeSupport main)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport main, ∃ i, p i = q)
    (R G : (ι → Fin B) → ℝ) (hR : ∀ x, 0 ≤ R x) (hRC : ∀ x, R x ≤ C)
    (hG : ∀ x, |G x| ≤ 1)
    (hretain : ∀ x, R x ≠ 0 → RetainedMainTests p (univ.image label) h B main x) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
        (fun x => R x * |selectedMixedDifference (singletonLabels label)
          (singletonTarget label target base)
          (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|) ≤
      (C * 2 ^ (singletonLabels label).card) *
        H⁻¹ ^ (∑ i ∈ nonsingletonLabels label,
          extraReciprocalExponent (litOccurrences label (designationLit U) i).card
            (unlitOccurrences label (designationLit U) i).card) *
        ∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹ := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  let delta := selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
    (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
      (litForcedTarget (nonsingletonSlots label \ U) label target base) y))
  let E := ∑ i ∈ nonsingletonLabels label,
    extraReciprocalExponent (litOccurrences label (designationLit U) i).card
      (unlitOccurrences label (designationLit U) i).card
  have hdelta (x : ι → Fin B) : |delta x| ≤ 2 ^ (singletonLabels label).card :=
    selectedMixedDifference_bound _ _ _ (fun _ => hG _) x
  have habs (x : ι → Fin B) : |R x * delta x| = R x * |delta x| := by
    rw [abs_mul, abs_of_nonneg (hR x)]
  have hav : μ.average (fun x => R x * |delta x|) ≤
      (C * 2 ^ (singletonLabels label).card) *
        μ.probability (RetainedMainTests p (univ.image label) h B main) := by
    have hf := μ.average_abs_le_support (fun x => R x * delta x)
      (RetainedMainTests p (univ.image label) h B main) (C * 2 ^ (singletonLabels label).card)
      (fun x => by rw [habs]; exact mul_le_mul (hRC x) (hdelta x) (abs_nonneg _) hC)
      (fun x hx => hretain x (fun hr => hx (by rw [hr, zero_mul])))
    simpa only [habs] using hf
  have hc := full_word_designated_reciprocal_bound_on_support label U hU p H hH hpH
  have hprob := tuple_weight_mul_retained_main_probability_le B h p hinj hp hpB
    (univ.image label) main hS hcover
  calc
    _ ≤ ((∏ i ∈ univ.image label, (p i : ℝ)⁻¹) * H⁻¹ ^ E) *
        ((C * 2 ^ (singletonLabels label).card) *
          μ.probability (RetainedMainTests p (univ.image label) h B main)) := by
      apply mul_le_mul hc hav
      · exact μ.average_nonneg (fun x => mul_nonneg (hR x) (abs_nonneg _))
      · positivity
    _ = ((C * 2 ^ (singletonLabels label).card) * H⁻¹ ^ E) *
        ((∏ i ∈ univ.image label, (p i : ℝ)⁻¹) *
          μ.probability (RetainedMainTests p (univ.image label) h B main)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprob (by positivity)

theorem uniform_weighted_word_lit_bound {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι]
    (B h : ℕ) (p : ι → ℕ) (hinj : Function.Injective p)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (main : List SignedStep) (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t)) (H C : ℝ)
    (hH : 0 < H) (hC : 0 ≤ C) (hpH : ∀ i ∈ nonsingletonLabels label, H ≤ p i)
    (hS : ∀ i ∈ univ.image label, p i ∈ wordDivisorPrimeSupport main)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport main, ∃ i, p i = q)
    (R G : (ι → Fin B) → ℝ) (hR : ∀ x, 0 ≤ R x) (hRC : ∀ x, R x ≤ C)
    (hG : ∀ x, |G x| ≤ 1)
    (hRdep : ∀ x y, (∀ i, i ∉ univ.image label → x i = y i) → R x = R y)
    (hretain : ∀ x, R x ≠ 0 → RetainedMainTests p (univ.image label) h B main x) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => R x * (∏ t,
        ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x)| ≤
      ∑ U ∈ (nonsingletonSlots label).powerset,
        if LitConsistent (nonsingletonSlots label \ U) label target then
          (C * 2 ^ (singletonLabels label).card) *
            H⁻¹ ^ (∑ i ∈ nonsingletonLabels label,
              extraReciprocalExponent (litOccurrences label (designationLit U) i).card
                (unlitOccurrences label (designationLit U) i).card) *
            ∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹
        else 0 := by
  apply (uniform_weighted_centered_word_majorant B p hp hpB label target base
    htarget R G hR hRdep).trans
  apply sum_le_sum
  intro U hU
  split_ifs
  · exact weighted_designation_bound B h p hinj hp hpB main label target base U
      (mem_powerset.mp hU) H C hH hC hpH hS hcover R G hR hRC hG hretain
  · exact le_rfl

end TwoPointCorrelations

end OAI

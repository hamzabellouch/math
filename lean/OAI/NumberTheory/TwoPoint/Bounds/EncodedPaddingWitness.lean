import OAI.NumberTheory.TwoPoint.Bounds.EncodedWitnessProbability
import OAI.NumberTheory.TwoPoint.Bounds.PaddingWitnessProbability

namespace OAI

/-! The singleton trace term keeps the main padding event inside the residue average. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def EncodedPaddingWitnessEvent {R T n : ℕ} {P Q : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q)
    (main : List SignedStep) (p : ι → ℕ) (B h s J : ℕ)
    (supply : ℕ → ℕ → Prop) (x : ι → Fin B) : Prop :=
  e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
      h s J supply ∧ d.Realizes e main ∧ RetainedMainTests p S h B main x ∧
    ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
      ∀ j, AttachedResiduePositiveWord p h
        ((e.decode.drop (d.1.2.1 j).val).take (d.1.2.2 j).val)
        (wordDisplacement h (main.take (d.2 j).val)) B y

lemma EncodedPaddingWitnessEvent.congr {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (d : WitnessRecord n R)
    (e : PrimeWordEncoding R T P Q) (main : List SignedStep) (p : ι → ℕ)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop) (x z : ι → Fin B)
    (hxz : ∀ i, i ∉ S → x i = z i) :
    EncodedPaddingWitnessEvent S d e main p B h s J supply x ↔
      EncodedPaddingWitnessEvent S d e main p B h s J supply z := by
  constructor
  · rintro ⟨hw, hr, hm, y, hy, ht⟩
    refine ⟨hw, hr, (retainedMainTests_congr p S h B main x z hxz).mp hm, y, ?_, ht⟩
    intro i hi
    exact (hy i hi).trans (hxz i hi)
  · rintro ⟨hw, hr, hm, y, hy, ht⟩
    refine ⟨hw, hr, (retainedMainTests_congr p S h B main x z hxz).mpr hm, y, ?_, ht⟩
    intro i hi
    exact (hy i hi).trans (hxz i hi).symm

theorem encoded_padding_witness_probability_le {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q)
    (main : List SignedStep) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hS : ∀ i ∈ S, p i ∈ wordDivisorPrimeSupport main)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport e.decode, ∃ i, p i = q) :
    (∏ i ∈ S, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (EncodedPaddingWitnessEvent S d e main p B h s J supply) ≤
      if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
        h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  have hnonneg : 0 ≤ ∏ i ∈ S, (p i : ℝ)⁻¹ := by positivity
  by_cases hw : e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
      (fun i => (d.1.2.2 i).val) h s J supply
  · rw [ite_eq_left hw]
    by_cases hr : d.Realizes e main
    · have hc : ∀ q ∈ wordDivisorPrimeSupport (recordedWitnessWord main
          (fun i => (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val)),
          ∃ i, p i = q := by
        simpa only [← hr.2.1] using hcover
      have hb := tuple_weight_mul_padding_hybrid_probability_le n B h p hinj hp hpB S main
        (fun i => (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val)
        (fun i => wordDisplacement h (main.take (d.2 i).val)) hS hc
      have hmono := μ.probability_mono_of_imp
        (fun x (he : EncodedPaddingWitnessEvent S d e main p B h s J supply x) => he.2.2)
      apply (mul_le_mul_of_nonneg_left hmono hnonneg).trans
      simpa only [← hr.2.1, ← hr.2.2] using hb
    · have he : ∀ x, ¬EncodedPaddingWitnessEvent S d e main p B h s J supply x :=
        fun _ hx => hr hx.2.1
      simp only [FiniteLaw.probability, FiniteLaw.average, he, ite_false, mul_zero,
        sum_const_zero]
      exact e.weight_nonneg
  · rw [ite_eq_right hw]
    have he : ∀ x, ¬EncodedPaddingWitnessEvent S d e main p B h s J supply x :=
      fun _ hx => hw hx.1
    simp only [FiniteLaw.probability, FiniteLaw.average, he, ite_false, mul_zero,
      sum_const_zero, le_refl]

end TwoPointCorrelations

end OAI

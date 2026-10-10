import OAI.NumberTheory.TwoPoint.Bounds.ActualWitnessRecord
import OAI.NumberTheory.TwoPoint.Walks.WitnessProbabilityWeight

namespace OAI

/-! The encoded witness union has its actual reciprocal-probability majorant. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def WitnessRecord.Realizes {R T n : ℕ} {P Q : Finset ℕ}
    (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q) (main : List SignedStep) : Prop :=
  e.decode.take d.1.1.val = main ∧
    e.decode = recordedWitnessWord main
      (fun i => (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val) ∧
    e.weight = ∏ q ∈ wordDivisorPrimeSupport e.decode, (q : ℝ)⁻¹

def EncodedWitnessHybridEvent {R T n : ℕ} {P Q : Finset ℕ} {ι : Type*}
    (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q)
    (main : List SignedStep) (p : ι → ℕ) (B h s J : ℕ)
    (supply : ℕ → ℕ → Prop) (x : ι → Fin B) : Prop :=
  e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
      h s J supply ∧ d.Realizes e main ∧
    ∃ y : ι → Fin B, (∀ i, p i ∉ wordDivisorPrimeSupport main → y i = x i) ∧
      ∀ j, AttachedResiduePositiveWord p h
        ((e.decode.drop (d.1.2.1 j).val).take (d.1.2.2 j).val)
        (wordDisplacement h (main.take (d.2 j).val)) B y

theorem encoded_witness_hybrid_probability_le {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q)
    (main : List SignedStep) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport e.decode, ∃ i, p i = q) :
    (∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (EncodedWitnessHybridEvent d e main p B h s J supply) ≤
      if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
        h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  have hmain : 0 ≤ ∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹ := by positivity
  by_cases hw : e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
      (fun i => (d.1.2.2 i).val) h s J supply
  · rw [ite_eq_left hw]
    by_cases hr : d.Realizes e main
    · have hc : ∀ q ∈ wordDivisorPrimeSupport (recordedWitnessWord main
          (fun i => (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val)),
          ∃ i, p i = q := by
        simpa only [← hr.2.1] using hcover
      have hb := main_weight_mul_hybrid_probability_le n B h p hinj hp hpB main
        (fun i => (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val)
        (fun i => wordDisplacement h (main.take (d.2 i).val)) hc
      have hmono := μ.probability_mono_of_imp
        (fun x (he : EncodedWitnessHybridEvent d e main p B h s J supply x) => he.2.2)
      apply (mul_le_mul_of_nonneg_left hmono hmain).trans
      simpa only [← hr.2.1, ← hr.2.2] using hb
    · have he : ∀ x, ¬EncodedWitnessHybridEvent d e main p B h s J supply x :=
        fun _ hx => hr hx.2.1
      simp only [FiniteLaw.probability, FiniteLaw.average, he, ite_false, mul_zero,
        sum_const_zero]
      exact e.weight_nonneg
  · rw [ite_eq_right hw]
    have he : ∀ x, ¬EncodedWitnessHybridEvent d e main p B h s J supply x :=
      fun _ hx => hw hx.1
    simp only [FiniteLaw.probability, FiniteLaw.average, he, ite_false, mul_zero,
      sum_const_zero, le_refl]

end TwoPointCorrelations

end OAI

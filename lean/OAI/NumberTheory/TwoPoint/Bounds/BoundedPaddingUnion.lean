import OAI.NumberTheory.TwoPoint.Bounds.EncodedPaddingUnion
import OAI.NumberTheory.TwoPoint.Bounds.FiniteSupportAverage

namespace OAI

/-! The finite witness union includes all record lengths and all original main words. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem main_sum_bounded_padding_union_probability_le {D n : ℕ} (T : ℕ → ℕ) {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (List SignedStep)) (S : List SignedStep → Finset ι) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (hS : ∀ main ∈ F, ∀ i ∈ S main, p i ∈ wordDivisorPrimeSupport main) :
    (∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
          ∃ e : PrimeWordEncoding R.val (T R.val) P Q,
            EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x)) ≤
      ∑ R : Fin (D + 1), ∑ d : WitnessRecord n R.val,
        ∑ e : PrimeWordEncoding R.val (T R.val) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
            h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  calc
    _ ≤ ∑ main ∈ F, ∑ R : Fin (D + 1),
        (∏ i ∈ S main, (p i : ℝ)⁻¹) * μ.probability
          (fun x => ∃ d : WitnessRecord n R.val, ∃ e : PrimeWordEncoding R.val (T R.val) P Q,
            EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x) := by
      apply sum_le_sum
      intro main _
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (μ.probability_exists_le _)
        (prod_nonneg (fun _ _ => by positivity))
    _ ≤ _ := by
      rw [sum_comm]
      apply sum_le_sum
      intro R _
      exact main_sum_padding_witness_union_probability_le F S p hinj B h s J supply hp hpB hP hQ hcover hS

theorem weighted_supported_padding_averages_le_catalog {D n : ℕ} (T : ℕ → ℕ) {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (List SignedStep)) (S : List SignedStep → Finset ι) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (hS : ∀ main ∈ F, ∀ i ∈ S main, p i ∈ wordDivisorPrimeSupport main)
    (f : List SignedStep → (ι → Fin B) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ main ∈ F, ∀ x, |f main x| ≤ C)
    (hsupport : ∀ main ∈ F, ∀ x, f main x ≠ 0 →
      ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
        ∃ e : PrimeWordEncoding R.val (T R.val) P Q,
          EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x) :
    (∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
        (fun x => |f main x|)) ≤
      C * ∑ R : Fin (D + 1), ∑ d : WitnessRecord n R.val,
        ∑ e : PrimeWordEncoding R.val (T R.val) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
            h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  let E (main : List SignedStep) (x : ι → Fin B) :=
    ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
      ∃ e : PrimeWordEncoding R.val (T R.val) P Q, EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x
  calc
    _ ≤ ∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
        (C * μ.probability (E main)) := by
      apply sum_le_sum
      intro main hm
      exact mul_le_mul_of_nonneg_left
        (μ.average_abs_le_support (f main) (E main) C (hf main hm) (hsupport main hm))
        (prod_nonneg (fun _ _ => by positivity))
    _ = C * ∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
        μ.probability (E main) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro main _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (main_sum_bounded_padding_union_probability_le T F S p hinj B h s J supply hp hpB hP hQ hcover hS) hC

end TwoPointCorrelations

end OAI

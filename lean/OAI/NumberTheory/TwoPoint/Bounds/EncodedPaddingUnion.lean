import OAI.NumberTheory.TwoPoint.Bounds.EncodedPaddingWitness
import OAI.NumberTheory.TwoPoint.Bounds.EncodedPrimeSupport

namespace OAI

/-! Sum the retained padding-event probabilities over all main words exactly once. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem sum_main_encoded_padding_probability_le {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q)
    (F : Finset (List SignedStep)) (S : List SignedStep → Finset ι) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport e.decode, ∃ i, p i = q)
    (hS : ∀ main ∈ F, ∀ i ∈ S main, p i ∈ wordDivisorPrimeSupport main) :
    (∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (EncodedPaddingWitnessEvent (S main) d e main p B h s J supply)) ≤
      if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
        h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  let g (main : List SignedStep) :=
    (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      μ.probability (EncodedPaddingWitnessEvent (S main) d e main p B h s J supply)
  have hzero (main : List SignedStep) (hne : main ≠ e.decode.take d.1.1.val) : g main = 0 := by
    have hfalse : ∀ x, ¬EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x := by
      intro x hx
      exact hne hx.2.1.1.symm
    simp only [g, FiniteLaw.probability, FiniteLaw.average, hfalse, ite_false,
      mul_zero, sum_const_zero]
  change ∑ main ∈ F, g main ≤ _
  by_cases hm : e.decode.take d.1.1.val ∈ F
  · rw [sum_eq_single_of_mem (e.decode.take d.1.1.val) hm (fun main _ hne => hzero main hne)]
    exact encoded_padding_witness_probability_le (S _) d e _ p hinj B h s J supply hp hpB (hS _ hm) hcover
  · rw [sum_eq_zero (fun main hmain => hzero main (fun he => hm (he ▸ hmain)))]
    split_ifs
    · exact e.weight_nonneg
    · exact le_refl 0

theorem main_sum_padding_witness_union_probability_le {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (List SignedStep)) (S : List SignedStep → Finset ι) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (hS : ∀ main ∈ F, ∀ i ∈ S main, p i ∈ wordDivisorPrimeSupport main) :
    (∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => ∃ d : WitnessRecord n R, ∃ e : PrimeWordEncoding R T P Q,
          EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x)) ≤
      ∑ d : WitnessRecord n R, ∑ e : PrimeWordEncoding R T P Q,
        if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
          h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  calc
    _ ≤ ∑ main ∈ F, ∑ d : WitnessRecord n R, ∑ e : PrimeWordEncoding R T P Q,
        (∏ i ∈ S main, (p i : ℝ)⁻¹) *
          μ.probability (EncodedPaddingWitnessEvent (S main) d e main p B h s J supply) := by
      apply sum_le_sum
      intro main _
      simp only [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun _ _ => by positivity))
      apply (μ.probability_exists_le _).trans
      exact sum_le_sum (fun d _ => μ.probability_exists_le _)
    _ ≤ _ := by
      rw [sum_comm]
      apply sum_le_sum
      intro d _
      rw [sum_comm]
      apply sum_le_sum
      intro e _
      exact sum_main_encoded_padding_probability_le d e F S p hinj B h s J supply hp hpB
        (fun q hq => hcover q (e.divisor_support_subset hP hQ hq)) hS

end TwoPointCorrelations

end OAI

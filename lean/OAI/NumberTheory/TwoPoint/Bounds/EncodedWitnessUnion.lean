import OAI.NumberTheory.TwoPoint.Bounds.EncodedWitnessProbability
import OAI.NumberTheory.TwoPoint.Bounds.EncodedPrimeSupport

namespace OAI

/-! Sum over all main words without paying a second main-word catalog factor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem sum_main_encoded_witness_probability_le {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q)
    (F : Finset (List SignedStep)) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport e.decode, ∃ i, p i = q) :
    (∑ main ∈ F, (∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (EncodedWitnessHybridEvent d e main p B h s J supply)) ≤
      if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
        h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  let g (main : List SignedStep) :=
    (∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹) *
      μ.probability (EncodedWitnessHybridEvent d e main p B h s J supply)
  have hzero (main : List SignedStep) (hne : main ≠ e.decode.take d.1.1.val) : g main = 0 := by
    have hfalse : ∀ x, ¬EncodedWitnessHybridEvent d e main p B h s J supply x := by
      intro x hx
      exact hne hx.2.1.1.symm
    simp only [g, FiniteLaw.probability, FiniteLaw.average, hfalse, ite_false,
      mul_zero, sum_const_zero]
  change ∑ main ∈ F, g main ≤ _
  by_cases hm : e.decode.take d.1.1.val ∈ F
  · rw [sum_eq_single_of_mem (e.decode.take d.1.1.val) hm (fun main _ hne => hzero main hne)]
    exact encoded_witness_hybrid_probability_le d e _ p hinj B h s J supply hp hpB hcover
  · rw [sum_eq_zero (fun main hmain => hzero main (fun he => hm (he ▸ hmain)))]
    split_ifs
    · exact e.weight_nonneg
    · exact le_refl 0

theorem main_sum_witness_union_probability_le {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (List SignedStep)) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q) :
    (∑ main ∈ F, (∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => ∃ d : WitnessRecord n R, ∃ e : PrimeWordEncoding R T P Q,
          EncodedWitnessHybridEvent d e main p B h s J supply x)) ≤
      ∑ d : WitnessRecord n R, ∑ e : PrimeWordEncoding R T P Q,
        if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
          h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  calc
    _ ≤ ∑ main ∈ F, ∑ d : WitnessRecord n R, ∑ e : PrimeWordEncoding R T P Q,
        (∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹) *
          μ.probability (EncodedWitnessHybridEvent d e main p B h s J supply) := by
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
      exact sum_main_encoded_witness_probability_le d e F p hinj B h s J supply hp hpB
        (fun q hq => hcover q (e.divisor_support_subset hP hQ hq))

end TwoPointCorrelations

end OAI

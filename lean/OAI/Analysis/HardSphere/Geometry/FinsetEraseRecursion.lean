import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter

lemma finset_erase_recursion {S : Type*} [DecidableEq S] (a : Finset S → ℝ) (q : ℝ)
    (hq : 0 ≤ q) (h0 : a ∅ ≤ 1)
    (hr : ∀ A : Finset S, A.Nonempty → (A.card : ℝ)*a A ≤ q*∑ s∈A, a (A.erase s)) :
    ∀ A : Finset S, a A ≤ q^A.card := by
  intro A
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hA : A.Nonempty
    · have hc : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
      have hs : (∑ s∈A, a (A.erase s)) ≤ (A.card : ℝ)*q^(A.card-1) := by
        calc
          _ ≤ ∑ _s∈A, q^(A.card-1) := Finset.sum_le_sum fun s hs ↦ by
            have hh := ih (A.erase s) (Finset.erase_ssubset hs)
            rwa [Finset.card_erase_of_mem hs] at hh
          _ = _ := by simp
      have he : q*((A.card : ℝ)*q^(A.card-1))=(A.card : ℝ)*q^A.card := by
        rw [show q^A.card=q^(A.card-1)*q by
          conv_lhs => rw [← Nat.sub_add_cancel hA.card_pos]
          rw [pow_succ]]
        ring
      have ht := (hr A hA).trans ((mul_le_mul_of_nonneg_left hs hq).trans_eq he)
      exact (mul_le_mul_iff_right₀ hc).mp (by simpa only [mul_comm (A.card : ℝ)] using ht)
    · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simpa [he] using h0

end HardSphere

end

end OAI

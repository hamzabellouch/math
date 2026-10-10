import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLawConstructions

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

omit [Fintype Ξ] in
 theorem expect_mono_support (μ : FiniteLaw Ω) {f h : Ω → ℝ}
    (hfh : ∀ ω, 0 < μ.weight ω → f ω ≤ h ω) : μ.expect f ≤ μ.expect h := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : 0 < μ.weight ω
  · exact mul_le_mul_of_nonneg_left (hfh ω hp) (μ.nonneg ω)
  · rw [le_antisymm (le_of_not_gt hp) (μ.nonneg ω), zero_mul, zero_mul]

omit [Fintype Ξ] in
 theorem expect_congr_support (μ : FiniteLaw Ω) {f h : Ω → ℝ}
    (hfh : ∀ ω, 0 < μ.weight ω → f ω=h ω) : μ.expect f=μ.expect h := by
  exact le_antisymm (μ.expect_mono_support (fun ω hω => (hfh ω hω).le))
    (μ.expect_mono_support (fun ω hω => (hfh ω hω).ge))

omit [Fintype Ξ] in
 theorem prob_zero_support (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (h : μ.prob E=0) : ∀ ω, 0 < μ.weight ω → ¬E ω := by
  intro ω hω hE
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun ξ => μ.weight ξ*(if E ξ then (1:ℝ) else 0))
    (fun ξ _ => mul_nonneg (μ.nonneg ξ) (by split_ifs <;> norm_num)) (Finset.mem_univ ω)
  have hs' : μ.weight ω ≤ μ.prob E := by
    simpa only [FiniteLaw.prob, expect, ite_eq_left hE, mul_one] using hs
  rw [h] at hs'
  exact not_lt_of_ge hs' hω

omit [Fintype Ξ] in
 theorem prob_compl (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    μ.prob (fun ω => ¬E ω)=1-μ.prob E := by
  have hp : ∀ ω, (if ¬E ω then (1:ℝ) else 0)=1-(if E ω then 1 else 0) := by
    intro ω; split_ifs <;> simp_all
  simp only [prob, hp, expect_sub, expect_const]

omit [Fintype Ξ] in
 theorem prob_one_support (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (h : μ.prob E=1) : ∀ ω, 0 < μ.weight ω → E ω := by
  classical
  have hz : μ.prob (fun ω => ¬E ω)=0 := by rw [prob_compl, h, sub_self]
  intro ω hω
  exact Classical.not_not.mp (μ.prob_zero_support _ hz ω hω)

omit [Fintype Ξ] in
 theorem support_product {I : Type*} [Fintype I] [DecidableEq I]
    (μ : I → FiniteLaw Ω) (ω : I → Ω) (h : 0 < (product μ).weight ω) :
    ∀ i, 0 < (μ i).weight (ω i) := by
  intro i
  apply lt_of_le_of_ne ((μ i).nonneg (ω i))
  intro hz
  have he0 : (product μ).weight ω=0 := by
    unfold product
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz.symm
  rw [he0] at h
  exact (lt_irrefl _ h)

end MetricKMedian.FiniteLaw

end OAI

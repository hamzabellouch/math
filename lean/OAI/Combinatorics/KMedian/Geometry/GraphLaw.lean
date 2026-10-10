import Mathlib
import OAI.Combinatorics.KMedian.Rounding.MarginalRounding

namespace OAI

section
section
namespace MetricKMedian
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem expect_eq_zero_of_support (μ : FiniteLaw Ω) {f : Ω → ℝ}
    (hf : ∀ ω, 0 < μ.weight ω → f ω=0) : μ.expect f=0 := by
  apply Finset.sum_eq_zero
  intro ω _
  by_cases h : 0 < μ.weight ω
  · rw [hf ω h, mul_zero]
  · rw [le_antisymm (le_of_not_gt h) (μ.nonneg ω), zero_mul]

theorem property_of_prob_one (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (hE : μ.prob E=1) {ω : Ω} (hω : 0 < μ.weight ω) : E ω := by
  classical
  by_contra hn
  have hpoint : ∀ t, (if E t then (1:ℝ) else 0)+(if E t then 0 else 1)=1 :=
    fun t => by split_ifs <;> norm_num
  have hbad : μ.expect (fun t => if E t then 0 else 1)=0 := by
    have h := μ.expect_add (fun t => if E t then 1 else 0) (fun t => if E t then 0 else 1)
    simp_rw [hpoint] at h
    rw [μ.expect_const] at h
    change 1 = μ.prob E+_ at h
    linarith only [h, hE]
  have hsingle := Finset.single_le_sum (s := Finset.univ)
    (f := fun t => μ.weight t*(if E t then (0:ℝ) else 1))
    (fun t _ => mul_nonneg (μ.nonneg t) (by split_ifs <;> norm_num)) (Finset.mem_univ ω)
  change μ.weight ω*(if E ω then (0:ℝ) else 1) ≤ μ.expect (fun t => if E t then 0 else 1) at hsingle
  rw [ite_eq_right hn, mul_one, hbad] at hsingle
  exact (not_lt_of_ge hsingle) hω

theorem not_property_of_prob_zero (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (hE : μ.prob E=0) {ω : Ω} (hω : 0 < μ.weight ω) : ¬ E ω := by
  intro h
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun t => μ.weight t*(if E t then (1:ℝ) else 0))
    (fun t _ => mul_nonneg (μ.nonneg t) (by split_ifs <;> norm_num)) (Finset.mem_univ ω)
  change μ.weight ω*(if E ω then (1:ℝ) else 0) ≤ μ.prob E at hs
  rw [ite_eq_left h, mul_one, hE] at hs
  exact (not_lt_of_ge hs) hω

end FiniteLaw

namespace GraphLaw
variable {I H : Type*} [Fintype I] [Fintype H] [DecidableEq I] [DecidableEq H]

noncomputable def edge (G : I → Finset H) (h : H) (i : I) : ℝ := if h ∈ G i then 1 else 0

theorem exists_law (q : H → I → ℝ) (Δ : ℕ)
    (hq0 : ∀ h i, 0 ≤ q h i) (hq1 : ∀ h i, q h i ≤ 1)
    (hsum : ∀ i, ∑ h, q h i=Δ) :
    ∃ μ : FiniteLaw (I → Finset H),
      (∀ G, 0 < μ.weight G → ∀ i, (G i).card=Δ) ∧
      (∀ h i, μ.expect (fun G => edge G h i)=q h i) ∧
      (∀ h k i j, i ≠ j → μ.expect (fun G => edge G h i*edge G k j)=q h i*q k j) ∧
      (∀ G, 0 < μ.weight G → ∀ h i, q h i=1 → h ∈ G i) ∧
      (∀ G, 0 < μ.weight G → ∀ h i, q h i=0 → h ∉ G i) := by
  classical
  choose μ hcard hmarg using fun i => MarginalRounding.exists_law (fun h => q h i) Δ
    (fun h => hq0 h i) (fun h => hq1 h i) (hsum i)
  let ν := FiniteLaw.product μ
  have hfirst : ∀ h i, ν.expect (fun G => edge G h i)=q h i := by
    intro h i
    rw [show (fun G => edge G h i) = (fun G : I → Finset H => if h ∈ G i then 1 else 0) from rfl,
      FiniteLaw.product_marginal μ i (fun S => if h ∈ S then (1:ℝ) else 0)]
    exact hmarg i h
  refine ⟨ν, ?_, hfirst, ?_, ?_, ?_⟩
  · intro G hG i
    have hi : 0 < (μ i).weight (G i) := by
      by_contra hn
      have hz : (μ i).weight (G i)=0 := le_antisymm (le_of_not_gt hn) ((μ i).nonneg _)
      have hp : ν.weight G=0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
      rw [hp] at hG
      exact lt_irrefl _ hG
    exact hcard i (G i) hi
  · intro h k i j hij
    rw [show (fun G => edge G h i*edge G k j) =
        (fun G : I → Finset H => (if h ∈ G i then 1 else 0)*(if k ∈ G j then 1 else 0)) from rfl,
      FiniteLaw.product_pair μ hij (fun S => if h ∈ S then (1:ℝ) else 0)
        (fun S => if k ∈ S then (1:ℝ) else 0)]
    change (μ i).prob (fun S => h ∈ S)*(μ j).prob (fun S => k ∈ S)=_
    rw [hmarg, hmarg]
  · intro G hG h i hq
    exact ν.property_of_prob_one (fun G => h ∈ G i) ((hfirst h i).trans hq) hG
  · intro G hG h i hq
    exact ν.not_property_of_prob_zero (fun G => h ∈ G i) ((hfirst h i).trans hq) hG

end GraphLaw
end MetricKMedian
end
end

end OAI

import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteJoint
import OAI.Combinatorics.KMedian.Preparation.PreparationMoments
import OAI.Combinatorics.KMedian.Preparation.AssignmentRepair

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]

theorem conditional_shortfall (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
    (U B : Ω → ℝ) (P : Ω → Ξ → ℝ) {u b g v A : ℝ}
    (hab : u+b=1) (hU : ν.expect U=u) (hUv : ν.variance U ≤ g)
    (hPm : ∀ ω, (κ ω).expect (P ω)=B ω)
    (hPv : ∀ ω, (κ ω).variance (P ω) ≤ v)
    (hB : ν.expect (fun ω => |B ω-b|) ≤ A) :
    (ν.joint κ).expect (fun z => max (1-U z.1-P z.1 z.2) 0) ≤
      Real.sqrt g+Real.sqrt v+A := by
  have hpoint : ∀ z : Ω × Ξ, max (1-U z.1-P z.1 z.2) 0 ≤
      |U z.1-u|+|P z.1 z.2-B z.1|+|B z.1-b| := by
    intro z
    apply max_le
    · have he : 1-U z.1-P z.1 z.2= -(U z.1-u)-(P z.1 z.2-B z.1)-(B z.1-b) := by
        linarith only [hab]
      rw [he]
      have h1 := neg_le_abs (U z.1-u)
      have h2 := neg_le_abs (P z.1 z.2-B z.1)
      have h3 := neg_le_abs (B z.1-b)
      linarith only [h1,h2,h3]
    · positivity
  have hu : ν.expect (fun ω => |U ω-u|) ≤ Real.sqrt g := by
    rw [← hU]
    exact (ν.expect_abs_centered_le_sqrt U).trans (Real.sqrt_le_sqrt hUv)
  have hp : ∀ ω, (κ ω).expect (fun ξ => |P ω ξ-B ω|) ≤ Real.sqrt v := by
    intro ω
    rw [← hPm ω]
    exact ((κ ω).expect_abs_centered_le_sqrt (P ω)).trans (Real.sqrt_le_sqrt (hPv ω))
  have he := (ν.joint κ).expect_mono hpoint
  simp only [FiniteLaw.expect_joint,FiniteLaw.expect_add,FiniteLaw.expect_const] at he
  have hp' : ν.expect (fun ω => (κ ω).expect (fun ξ => |P ω ξ-B ω|)) ≤ Real.sqrt v :=
    (ν.expect_mono hp).trans_eq (ν.expect_const _)
  rw [FiniteLaw.expect_joint]
  exact he.trans (add_le_add (add_le_add hu hp') hB)

omit [Fintype Ξ] in

theorem expected_repaired_cost {I : Type} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw Ω) (ball : Finset I) (y a : Ω → I → ℝ) (d : I → ℝ)
    {Q V H C : ℝ} (hQ : 0 ≤ Q) (hV : 0 ≤ V)
    (ha : ∀ ω i, 0 ≤ a ω i) (hay : ∀ ω i, a ω i ≤ y ω i)
    (hd : ∀ i, 0 ≤ d i) (hdQ : ∀ i ∈ ball, d i ≤ Q*V)
    (hball : ∀ ω, 1 ≤ ∑ i ∈ ball, y ω i)
    (hcost : μ.expect (fun ω => ∑ i, a ω i*d i) ≤ C*V)
    (hshort : μ.expect (fun ω => max (1-∑ i, a ω i) 0) ≤ H) :
    ∃ r : Ω → I → ℝ,
      (∀ ω, (∀ i, 0 ≤ r ω i ∧ r ω i ≤ y ω i) ∧ (∑ i, r ω i)=1) ∧
      μ.expect (fun ω => ∑ i, r ω i*d i) ≤ (C+Q*H)*V := by
  classical
  choose r hr hm hc using fun ω => repair_assignment ball (y ω) (a ω) d (ha ω) (hay ω)
    hd (mul_nonneg hQ hV) hdQ (hball ω)
  refine ⟨r,fun ω => ⟨hr ω,hm ω⟩,?_⟩
  have he := μ.expect_mono hc
  rw [FiniteLaw.expect_add,FiniteLaw.expect_mul] at he
  have hs := mul_le_mul_of_nonneg_left hshort (mul_nonneg hQ hV)
  calc
    _ ≤ _ := he
    _ ≤ C*V+(Q*V)*H := add_le_add hcost hs
    _ = _ := by ring

end MetricKMedian.Preparation
end
end

end OAI

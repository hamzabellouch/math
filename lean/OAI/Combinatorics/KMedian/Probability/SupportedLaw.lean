import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteJoint

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

omit [Fintype Ξ] in
noncomputable def supported (μ : FiniteLaw Ω) : FiniteLaw {ω // 0 < μ.weight ω} where
  weight ω := μ.weight ω.1
  nonneg ω := μ.nonneg ω.1
  total := by
    classical
    rw [← Finset.sum_subtype (univ.filter (fun ω => 0 < μ.weight ω)) (by simp), sum_filter]
    calc
      _ = ∑ ω, μ.weight ω := by
        apply sum_congr rfl
        intro ω _
        by_cases h : 0 < μ.weight ω
        · simp only [h, ite_true]
        · simp only [h, ite_false]
          exact (le_antisymm (le_of_not_gt h) (μ.nonneg ω)).symm
      _ = 1 := μ.total

omit [Fintype Ξ] in
 theorem expect_supported (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.supported.expect (fun ω => f ω.1)=μ.expect f := by
  classical
  change (∑ ω : {ω // 0 < μ.weight ω}, μ.weight ω.1*f ω.1)=∑ ω, μ.weight ω*f ω
  rw [← Finset.sum_subtype (univ.filter (fun ω => 0 < μ.weight ω)) (by simp)
    (fun ω => μ.weight ω*f ω), sum_filter]
  apply sum_congr rfl
  intro ω _
  by_cases h : 0 < μ.weight ω
  · simp only [h, ite_true]
  · rw [ite_eq_right h, le_antisymm (le_of_not_gt h) (μ.nonneg ω), zero_mul]

noncomputable def independent (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) : FiniteLaw (Ω × Ξ) :=
  μ.joint (fun _ => ν)

 theorem expect_independent (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω × Ξ → ℝ) :
    (μ.independent ν).expect f=μ.expect (fun ω => ν.expect (fun ξ => f (ω,ξ))) :=
  expect_joint μ (fun _ => ν) f

 theorem independent_left (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω → ℝ) :
    (μ.independent ν).expect (fun z => f z.1)=μ.expect f := by
  rw [expect_independent]
  simp only [expect_const]

 theorem independent_right (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ξ → ℝ) :
    (μ.independent ν).expect (fun z => f z.2)=ν.expect f := by
  rw [expect_independent]
  simpa only using μ.expect_const (ν.expect f)

 theorem independent_pair (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω → ℝ) (g : Ξ → ℝ) :
    (μ.independent ν).expect (fun z => f z.1*g z.2)=μ.expect f*ν.expect g := by
  rw [expect_independent]
  simp only [expect_mul,expect_mul_right]

 theorem support_independent (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (z : Ω × Ξ)
    (h : 0 < (μ.independent ν).weight z) : 0 < μ.weight z.1 ∧ 0 < ν.weight z.2 :=
  support_joint μ (fun _ => ν) z h

end MetricKMedian.FiniteLaw
end
end

end OAI

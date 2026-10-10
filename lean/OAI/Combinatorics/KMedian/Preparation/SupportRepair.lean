import Mathlib
import OAI.Combinatorics.KMedian.Probability.ProbabilitySupport
import OAI.Combinatorics.KMedian.Preparation.AssignmentRepair

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem support_repaired_cost (μ : FiniteLaw Ω) (ball : Finset I)
    (y a : Ω → I → ℝ) (d : I → ℝ) {R H V : ℝ}
    (hR : 0 ≤ R) (ha : ∀ ω, 0 < μ.weight ω → ∀ i, 0 ≤ a ω i)
    (hay : ∀ ω, 0 < μ.weight ω → ∀ i, a ω i ≤ y ω i)
    (hd : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ ball, d i ≤ R)
    (hball : ∀ ω, 0 < μ.weight ω → 1 ≤ ∑ i ∈ ball, y ω i)
    (hcost : μ.expect (fun ω => ∑ i, a ω i*d i) ≤ V)
    (hshort : μ.expect (fun ω => max (1-∑ i, a ω i) 0) ≤ H) :
    ∃ r : Ω → I → ℝ,
      (∀ ω, 0 < μ.weight ω → (∀ i, 0 ≤ r ω i ∧ r ω i ≤ y ω i) ∧ (∑ i, r ω i)=1) ∧
      μ.expect (fun ω => ∑ i, r ω i*d i) ≤ V+R*H := by
  classical
  choose r hr using fun ω : {ω // 0 < μ.weight ω} => repair_assignment ball
    (y ω.1) (a ω.1) d (ha ω.1 ω.2) (hay ω.1 ω.2) hd hR hdR (hball ω.1 ω.2)
  let r' := fun ω => if h : 0 < μ.weight ω then r ⟨ω,h⟩ else fun _ => 0
  refine ⟨r',?_,?_⟩
  · intro ω hω
    simp only [r',dite_eq_left hω]
    exact ⟨(hr ⟨ω,hω⟩).1,(hr ⟨ω,hω⟩).2.1⟩
  · have he : μ.expect (fun ω => ∑ i, r' ω i*d i) ≤
        μ.expect (fun ω => (∑ i, a ω i*d i)+R*max (1-∑ i, a ω i) 0) :=
      μ.expect_mono_support (fun ω (hω : 0 < μ.weight ω) => by
        simpa only [r',dite_eq_left hω] using (hr ⟨ω,hω⟩).2.2)
    rw [FiniteLaw.expect_add,FiniteLaw.expect_mul] at he
    exact he.trans (add_le_add hcost (mul_le_mul_of_nonneg_left hshort hR))

end MetricKMedian.Preparation
end
end

end OAI

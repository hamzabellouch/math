import OAI.Probability.SpanningForest.BrownianFamilyPast
import OAI.Probability.SpanningForest.GaussianSum

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem336.BrownianFamilyPast

variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : I → ℝ≥0 → Ω → ℝ}

theorem weighted_increment_hasLaw
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) (u h : ℝ≥0) :
    HasLaw (fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω))
      (gaussianReal 0 (h * ∑ i ∈ S, ⟨(θ i)^2, sq_nonneg _⟩)) P := by
  classical
  have hQ (i : S) : HasLaw (fun ω => B i (u + h) ω - B i u ω)
      (gaussianReal 0 h) P := ((hB i).shift u).hasLaw_eval h
  have hJ : iIndepFun (fun (i : S) ω => B i (u + h) ω - B i u ω) P :=
    (hI.precomp Subtype.val_injective).comp
      (fun (_ : S) (f : ℝ≥0 → ℝ) => f (u + h) - f u) (fun _ => by fun_prop)
  have hsum := independent_weighted_gaussian_sum_hasLaw hQ hJ (fun i : S => θ i)
  have heq : (fun ω => ∑ i : S, θ i * (B i (u + h) ω - B i u ω)) =
      (fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω)) := by
    funext ω
    exact Finset.sum_coe_sort S (fun i => θ i * (B i (u + h) ω - B i u ω))
  have hv : (∑ i : S, NNReal.mk ((θ i)^2) (sq_nonneg _) * h) =
      h * ∑ i ∈ S, NNReal.mk ((θ i)^2) (sq_nonneg _) := by
    rw [Finset.sum_coe_sort S (fun i => NNReal.mk ((θ i)^2) (sq_nonneg _) * h)]
    rw [← Finset.sum_mul, mul_comm]
  rw [heq, hv] at hsum
  exact hsum

end Problem336.BrownianFamilyPast

end

end OAI

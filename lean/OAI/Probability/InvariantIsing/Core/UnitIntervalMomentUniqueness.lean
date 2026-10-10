import OAI.Probability.InvariantIsing.Spectral.ResolventMomentIdentification
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

namespace OAI

/-! Bounded polynomial moments determine a probability measure on the unit interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace InvariantIsing

theorem unitInterval_moments_unique (μ ν : Measure (Set.Icc (0 : ℝ) 1))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n : ℕ, (∫ x, (x : ℝ)^n ∂μ) = ∫ x, (x : ℝ)^n ∂ν) : μ = ν := by
  let g : Set.Icc (0 : ℝ) 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨Subtype.val,continuous_subtype_val⟩
  let ev : Polynomial ℝ →ₐ[ℝ] (Set.Icc (0 : ℝ) 1 →ᵇ ℝ) := Polynomial.aeval g
  let A : StarSubalgebra ℝ (Set.Icc (0 : ℝ) 1 →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    refine ⟨g,?_,?_⟩
    · refine ⟨g.toContinuousMap,?_,rfl⟩
      exact ⟨g,⟨Polynomial.X,by simp [ev]⟩,rfl⟩
    · exact fun he => hxy (Subtype.ext he)
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p,rfl⟩ := hf
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add,BoundedContinuousFunction.coe_add,Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial n c =>
    have he (x : Set.Icc (0 : ℝ) 1) : ev (Polynomial.monomial n c) x = c*(x : ℝ)^n := by
      simp [ev,Polynomial.aeval_monomial,g]
    change (∫ x, ev (Polynomial.monomial n c) x ∂μ) =
      ∫ x, ev (Polynomial.monomial n c) x ∂ν
    simp only [he,integral_const_mul]
    exact congrArg (c * ·) (h n)

end InvariantIsing

end

end OAI

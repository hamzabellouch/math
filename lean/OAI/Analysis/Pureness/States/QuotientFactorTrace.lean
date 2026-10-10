import OAI.Analysis.Pureness.Projections.QuotientProjectionComparison
import OAI.Analysis.Pureness.Projections.QuotientEquivalentSubprojections
import OAI.Analysis.Pureness.States.QuotientAWStar
import OAI.Analysis.Pureness.Projections.AWFactorCorners
import OAI.Analysis.Pureness.Projections.ProjectionDimensionQuasitrace
import OAI.Analysis.Pureness.Projections.QuotientProjectionDeterminesValue

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt in

theorem quotient_factor_projection_comparison
    (hcentral : ∀ p : T.CauchyQuotient hadd, IsStarProjection p →
      (∀ x, Commute p x) → p=0 ∨ p=1)
    (p q : T.CauchyQuotient hadd) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (∃ v, star v*v=p ∧ IsStarProjection (v*star v) ∧ v*star v ≤ q) ∨
    (∃ v, star v*v=q ∧ IsStarProjection (v*star v) ∧ v*star v ≤ p) := by
  apply T.quotient_projection_comparison hadd hsqrt _ p q hp hq
  intro a b ha hb ha0 hb0
  obtain ⟨x,hx⟩ := exists_nonzero_factor_corner
    (T.quotient_right_annihilator_projection hadd hsqrt) hcentral a b ha0 hb0
  apply T.quotient_equivalent_subprojections_of_nonzero_corner hadd hsqrt a b ha hb (a*x*b) hx
  · rw [← mul_assoc a,← mul_assoc a,ha.isIdempotentElem.eq]
  · rw [mul_assoc (a*x),hb.isIdempotentElem.eq]

theorem quotient_factor_trace_agrees
    (hcentral : ∀ p : T.CauchyQuotient hadd, IsStarProjection p →
      (∀ x, Commute p x) → p=0 ∨ p=1)
    (Q : ComplexQuasitrace (T.CauchyQuotient hadd)) (hQ : Q 1=1)
    (c : ℂ) (hval : ∀ x, Q x=c*T.quotientValue hadd hsqrt x)
    (τ : TracialState (T.CauchyQuotient hadd)) : ∀ x, τ.functional x=Q x := by
  intro x
  rw [hval x]
  apply T.scaled_quotientValue_eq_of_projections hadd hsqrt τ.functional c _ x
  intro p hp
  rw [← hval p]
  exact tracialState_eq_quasitrace_on_projections
    (T.quotient_factor_projection_comparison hadd hsqrt hcentral) τ Q hQ p hp
end CuntzPureness.PositiveQuasitrace

end

end OAI

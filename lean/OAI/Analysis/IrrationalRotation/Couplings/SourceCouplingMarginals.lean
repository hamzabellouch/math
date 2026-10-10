import OAI.Analysis.IrrationalRotation.Model.SourceCouplingMarginals
import OAI.Analysis.IrrationalRotation.Couplings.ProductCouplingCircleSource
import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalCrossing

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Invariant233.OrderedProductCoupling
open OneCoordinateCoupling

theorem source_coupling_marginals
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) :
    SourceMarginalProperties (sourceBlocks m a b hm ha ha' hb hb' e tag)
      (blockDensityBound sourceKappa) := by
  let P := sourceBlocks m a b hm ha ha' hb hb' e tag
  change SourceMarginalProperties P _
  refine {
    law_probability := law_isProbabilityMeasure P
    H_positive := blockDensityBound_pos sourceKappa
    probability := circlePairLaw_probability P
    ordered := circlePairLaw_ordered P
    representatives := ae_real_circle_endpoints P
    coordinate_densities := ?_
    coordinate_bound := ?_
    hybrid_densities := ?_
    hybrid_mass_bound := ?_
    right_kernel := right_condDistrib_eq_product P
    left_kernel := left_condDistrib_eq_product P
    right_independent := right_coordinates_conditionally_independent P
    left_independent := left_coordinates_conditionally_independent P
    right_crossing := right_condDistrib_crossing_real_lower P
    left_crossing := left_condDistrib_crossing_real_lower P }
  · intro side i
    cases side
    · exact coordinateLaw_map_left P i
    · exact coordinateLaw_map_right P i
  · intro side i x
    refine ⟨marginalDensity_nonneg P side i x, ?_⟩
    cases side
    · exact (leftMarginalDensity_bounds (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
        (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
        (P.t_nonneg i) (P.t_le i) x).2.2.le
    · exact (rightMarginalDensity_bounds (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
        (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
        (P.t_nonneg i) (P.t_le i) x).2.2.le
  · intro ε
    exact exists_source_circle_hybrid_density m a b hm ha ha' hb hb' e tag ε
  · intro ε A hA
    exact source_circle_hybrid_measureReal_le_sqrt m a b hm ha ha' hb hb' e tag ε A hA

end Invariant233.OrderedProductCoupling

end OAI

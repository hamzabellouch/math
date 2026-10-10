import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMetricRemainder
import OAI.Geometry.SurfaceImmersion.Geometry.ScalarFastRemainderBounds

namespace OAI

/-! Quantitative bounds for the actual finite pullback-metric tail. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion WeightedEstimates

/-- A single finite algebraic loss bounds the true metric remainder, at every
weighted derivative order. This applies to each of xx, xy, and yy by choosing
the two tangent coefficient sequences. -/
theorem compact_finite_metric_tail {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (X Y : ℕ → VectorExpression) (hXs : ∀ i, (X i).SmoothCoeffs O)
    (hYs : ∀ i, (Y i).SmoothCoeffs O) (L N : ℕ) (hN : 2 ≤ N)
    (hX : ∀ i ≤ L, ∀ a, (X i a).order ≤ N)
    (hY : ∀ i ≤ L, ∀ a, (Y i a).order ≤ N) (ℓ : Base →L[ℝ] ℝ) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + N) B (lowJet G) →
      ∀ (A B : ℕ → Family S R4),
        (∀ i, VectorExpression.Represents G (X i) (A i)) →
        (∀ i, VectorExpression.Represents G (Y i) (B i)) →
        WeightedBound S z m (D * z ^ L / s ^ d)
          (fun p => ∑ r ∈ Finset.Ico L (2 * L + 1),
            z ^ r * (metricCoefficientFamily L r A B).fastValue ℓ z p) := by
  let R := fun r => finiteMetric L r X Y
  let d := (Finset.Ico L (2 * L + 1)).sup (fun r => (R r).loss)
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hb⟩ := Expression.compact_tail_bound (S := S) hO hK hKO R
    (fun r => smooth_finiteMetric hXs hYs L r) L (2 * L + 1) N d
    (fun r _ => order_finiteMetric hN hX hY r)
    (fun r hr => Finset.le_sup (f := fun r => (R r).loss) hr) ℓ m B hB
  refine ⟨D, hD, ?_⟩
  intro G s z hz hzs hs1 hG hGK hGb A B hA hB
  exact hb G s z hz hzs hs1 hG hGK hGb (fun r => metricCoefficientFamily L r A B)
    (fun r _ => represents_finiteMetric hA hB L r)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI

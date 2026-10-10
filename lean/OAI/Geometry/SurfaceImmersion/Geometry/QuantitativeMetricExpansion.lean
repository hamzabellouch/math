import OAI.Geometry.SurfaceImmersion.Atlas.TangentMetricBounds
import OAI.Geometry.SurfaceImmersion.Geometry.LocalMetricExpansionWitness

namespace OAI

/-! The actual pullback metric, after subtracting its finite mean expansion,
has the fast-scale remainder bound used by the correction iteration. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector

namespace MetricPolynomial

def metricDirection (dx dy : Base) (b : Bool) : Base := if b then dx else dy

def meanMetric {S : TopologicalSpace.Opens Base} {dy : Base}
    (g : Geometry (E := R4) S dy) (dx : Base) (U : ℕ → Family S R4)
    (n : ℕ) (b c : Bool) (z : ℝ) (p : Base) : ℝ :=
  if b && c then
    inner ℝ (g.X₀ p) (g.X₀ p) + g.q p +
      ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xxCoefficient dx U r).val p) * z ^ r
  else if b || c then
    inner ℝ (g.X₀ p) (g.Y p) +
      ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xyCoefficient dx U r).val p) * z ^ r
  else
    inner ℝ (g.Y p) (g.Y p) +
      ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.yyCoefficient U r).val p) * z ^ r

/-- In each metric component, the error of the actual finite oscillatory map
relative to its mean expansion is `O_z(z^(n+1) / s^d)`. The fixed loss is
chosen before the slow map, both scales, or the derivative order. -/
theorem compact_metric_error {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (X Y : VectorExpression) (R : ℕ → VectorExpression)
    (hXs : X.SmoothCoeffs O) (hYs : Y.SmoothCoeffs O) (hRs : ∀ i, (R i).SmoothCoeffs O)
    (n : ℕ) (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
    (hR : ∀ j < n + 1, ∀ a, (R j a).order ≤ 2 * j + 2)
    (dx dy : Fin 2) (b c : Bool) (ℓ : Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector dx) = 1) (hℓy : ℓ (coordinateVector dy) = 0) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + (2 * (n + 1) + 1)) B (lowJet G) →
      ∀ (g : Geometry (E := R4) S (coordinateVector dy)) (U : ℕ → Family S R4)
        (F : Base → R4),
        VectorExpression.Represents G X g.longitudinal →
        VectorExpression.Represents G Y g.transverse →
        (∀ i, VectorExpression.Represents G (R i) (U i)) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) →
        ContDiffOn ℝ ∞ F S →
        (∀ p ∈ S, fderiv ℝ F p (coordinateVector dx) = g.X₀ p + average (g.V.val p)) →
        (∀ p ∈ S, fderiv ℝ F p (coordinateVector dy) = g.Y p) →
        WeightedBound S z m (D * z ^ (n + 1) / s ^ d)
          (fun p => inner ℝ
            (fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p
              (metricDirection (coordinateVector dx) (coordinateVector dy) b))
            (fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p
              (metricDirection (coordinateVector dx) (coordinateVector dy) c)) -
            meanMetric g (coordinateVector dx) U n b c z p) := by
  obtain ⟨d, hd⟩ := compact_tangent_metric_tail hO hK hKO X Y R hXs hYs hRs
    (n + 1) (by omega) hX hY hR dx dy (b || c) (b && c) ℓ
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hb⟩ := hd m B hB
  refine ⟨D, hD, ?_⟩
  intro G s z hz hzs hs1 hG hGK hGb g U F hXg hYg hrep hinit hy hc hF hDX hDY
  have htail := hb G s z hz hzs hs1 hG hGK hGb g U hXg hYg hrep
  apply htail.congr
  intro p hp
  obtain ⟨hxx, hxy, hyy⟩ := g.finite_expansion_of_cancellation hF U hinit n
    (coordinateVector dx) hy hc ℓ hℓx hℓy hDX hDY z hz.ne' hp
  cases b <;> cases c
  · simp only [metricDirection, meanMetric, tangentFamily, Family.fastValue,
      Bool.and, Bool.or, Bool.false_eq_true, ↓reduceIte]
    change _ - _ = ∑ r ∈ _, z ^ r * (g.yyRemainder U (n + 1) r).val p _
    rw [hyy]
    simp only [add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  · simp only [metricDirection, meanMetric, tangentFamily, Family.fastValue,
      Bool.and, Bool.or, Bool.false_eq_true, ↓reduceIte]
    rw [real_inner_comm]
    change _ - _ = ∑ r ∈ _, z ^ r * (g.xyRemainder (coordinateVector dx) U (n + 1) r).val p _
    rw [hxy]
    simp only [add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  · simp only [metricDirection, meanMetric, tangentFamily, Family.fastValue,
      Bool.and, Bool.or, Bool.false_eq_true, ↓reduceIte]
    change _ - _ = ∑ r ∈ _, z ^ r * (g.xyRemainder (coordinateVector dx) U (n + 1) r).val p _
    rw [hxy]
    simp only [add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  · simp only [metricDirection, meanMetric, tangentFamily, Family.fastValue,
      Bool.and, Bool.or, ↓reduceIte]
    change _ - _ = ∑ r ∈ _, z ^ r * (g.xxRemainder (coordinateVector dx) U (n + 1) r).val p _
    rw [hxx]
    simp only [add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end MetricPolynomial
end ClosedSurfaceR4.JetPolynomial

end

end OAI

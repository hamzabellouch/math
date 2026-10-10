import OAI.Geometry.SurfaceImmersion.Correction.BoundedSurfaceCorrection
import OAI.Geometry.SurfaceImmersion.Geometry.QuantitativeMetricExpansion

namespace OAI

/-! The finite metric expansion of the actual surface map, with its leading
primitive tensor identified and its fast remainder uniformly bounded. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector WeightedEstimates
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

def meanCorrection {S : TopologicalSpace.Opens JetPolynomial.Base}
    (g : Geometry (E := Euclidean) S (coordinateVector 1))
    (U : ℕ → Family S Euclidean) (n : ℕ) (b c : Bool) (z : ℝ)
    (p : JetPolynomial.Base) : ℝ :=
  if b && c then
    ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xxCoefficient (coordinateVector 0) U r).val p) * z ^ r
  else if b || c then
    ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xyCoefficient (coordinateVector 0) U r).val p) * z ^ r
  else
    ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.yyCoefficient U r).val p) * z ^ r

lemma meanMetric_eq {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (U : ℕ → Family S Euclidean)
    (n : ℕ) (b c : Bool) (z : ℝ) {p : JetPolynomial.Base} (hp : p ∈ S) :
    let g := l.geometry G hG hGO
    MetricPolynomial.meanMetric g (coordinateVector 0) U n b c z p =
      inner ℝ
        (fderiv ℝ (fun q => ι (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ (fun q => ι (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) +
      (if b && c then l.amplitude (lowJet G p) ^ 2 else 0) + meanCorrection g U n b c z p := by
  dsimp only
  cases b <;> cases c <;>
    simp only [MetricPolynomial.meanMetric, meanCorrection, MetricPolynomial.metricDirection,
      Bool.and, Bool.or, Bool.false_eq_true, ↓reduceIte,
      euclidean_first_derivative hG, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [add_zero]; rfl
  · change inner ℝ (ι (tangent (lowJet G p))) (ι (slot 2 (lowJet G p))) + _ = _
    rw [l.leading_xy (hGO hp), real_inner_comm (ι (slot 1 (lowJet G p))) (ι (slot 2 (lowJet G p)))]
    simp only [add_zero]
  · change inner ℝ (ι (tangent (lowJet G p))) (ι (slot 2 (lowJet G p))) + _ = _
    rw [l.leading_xy (hGO hp)]
    simp only [add_zero]
  · change (inner ℝ (ι (tangent (lowJet G p))) (ι (tangent (lowJet G p))) +
      l.q (lowJet G p)) + _ = _
    rw [l.leading_xx (hGO hp)]

/-- No derivative or leading-metric identities are additional assumptions:
they follow from the actual coordinate jet and the geometric loop. -/
theorem compact_surface_metric_error {S : TopologicalSpace.Opens JetPolynomial.Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (b c : Bool) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGK : MapsTo (lowJet G) S K) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s (m + (2 * (n + 1) + 1)) B (lowJet G) →
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) →
        WeightedBound S z m (D * z ^ (n + 1) / s ^ d)
          (fun p => inner ℝ
            (fderiv ℝ (finiteAnsatz (fun q => ι (G q)) U ℓ (n + 1) z) p
              (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
            (fderiv ℝ (finiteAnsatz (fun q => ι (G q)) U ℓ (n + 1) z) p
              (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) -
            MetricPolynomial.meanMetric g (coordinateVector 0) U n b c z p) := by
  have hd : ∀ J ∈ O, PeriodicCorrector.gramDet (yData J) (cData J) ≠ 0 := by
    intro J hJ
    rw [yData, cData, gram_toEuclidean]
    exact l.gram_ne J hJ
  have hRs := MetricPolynomial.coefficients_smooth O.isOpen yData_smooth cData_smooth
    (xData_smooth l) l.euclideanVelocity_smooth hd l.smoothQ (fun _ hJ => l.q_pos hJ)
    (fun _ hJ => l.euclideanVelocity_length hJ) 0 1 n
  obtain ⟨d, hb⟩ := MetricPolynomial.compact_metric_error (S := S) O.isOpen hK hKO
    (MetricPolynomial.longitudinal xData l.euclideanVelocity) (MetricPolynomial.transverse yData)
    (l.coefficientExpressions n)
    (MetricPolynomial.smooth_longitudinal (xData_smooth l) l.euclideanVelocity_smooth)
    (MetricPolynomial.smooth_transverse yData_smooth) hRs n (fun _ => le_rfl) (fun _ => le_rfl)
    (fun j _ a => MetricPolynomial.coefficients_order _ _ _ _ _ 0 1 n j a)
    0 1 b c ℓ hℓx hℓy
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hbound⟩ := hb m B hB
  refine ⟨D, hD, ?_⟩
  intro G hG hGK s z hz hzs hs1 hGs g U hrep hinit hy hc
  exact hbound G s z hz hzs hs1 hG hGK hGs g U (fun q => ι (G q))
    (MetricPolynomial.represents_longitudinal g xData l.euclideanVelocity (fun _ _ => rfl)
      (fun _ hp => l.geometry_velocity hG (fun _ hp => hKO (hGK hp)) hp))
    (MetricPolynomial.represents_transverse g yData (fun _ _ => rfl))
    hrep hinit hy hc (JetVelocityCoordinates.toEuclidean.contDiff.comp hG).contDiffOn
    (fun _ hp => l.geometry_dx hG (fun _ hp => hKO (hGK hp)) hp)
    (fun p _ => l.geometry_dy hG (fun _ hp => hKO (hGK hp)) p)

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI

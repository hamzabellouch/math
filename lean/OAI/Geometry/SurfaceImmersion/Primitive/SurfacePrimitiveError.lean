import OAI.Geometry.SurfaceImmersion.Primitive.SpatialLoopAmplitude

namespace OAI

/-! The finite primitive's actual metric error is the sum of its solved mean
error and the fast finite tail. The prescribed amplitude is fixed in position. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def meanOperator (n : ℕ) (b c : Bool) (z : ℝ) (G : JetPolynomial.Base → JetPolynomial.Space) (p : Base) : ℝ :=
  inner ℝ
    (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
      (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
    (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
      (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) +
  Perturbation.eval (l.meanPolynomial n b c) z G (p,0)

lemma meanOperator_smooth {S : TopologicalSpace.Opens Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G) (hGO : MapsTo (lowJet G) S O)
    (n : ℕ) (b c : Bool) (z : ℝ) : ContDiffOn ℝ ∞ (l.meanOperator n b c z G) S := by
  have hF := JetVelocityCoordinates.toEuclidean.contDiff.comp hG
  have hd := hF.fderiv_right (m := ∞) (by simp)
  apply ((hd.clm_apply contDiff_const).inner ℝ (hd.clm_apply contDiff_const)).contDiffOn.add
  have he := Perturbation.eval_smooth (fun r => l.meanPolynomial_smooth n b c r) z hG hGO
  exact he.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun p hp => ⟨hp,mem_univ _⟩)

lemma meanMetric_eq_meanOperator {a : Base → ℝ} (ha : l.HasSpatialAmplitude a)
    {S : TopologicalSpace.Opens Base} {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool) (z : ℝ)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    {p : Base} (hp : p ∈ S) :
    MetricPolynomial.meanMetric (l.geometry G hG hGO) (coordinateVector 0) U n b c z p =
      l.meanOperator n b c z G p+(if b && c then a p^2 else 0) := by
  rw [l.meanMetric_eq_spatial_polynomial ha hG hGO n b c U hU z hp]
  unfold meanOperator
  ring

/-- A solved mean equation controls the actual primitive metric at every
finite weighted order. The tail loss is chosen before the order or slow map. -/
theorem compact_primitive_error {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hamp : l.HasSpatialAmplitude a) {S : TopologicalSpace.Opens Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (b c : Bool) (ℓ : Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G) (hGK : MapsTo (lowJet G) S K)
        (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s (m+(2*(n+1)+1)) B (lowJet G) →
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r+1)).fluct = 0) →
      ∀ (H : Base → ℝ), ContDiffOn ℝ ∞ H S → ∀ E : ℝ,
      WeightedBound S s m E (l.meanOperator n b c z G-H) →
      WeightedBound S z m (D*z^(n+1)/s^d+E)
        (fun p => inner ℝ
          (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p
            (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
          (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p
            (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) -
          (H p+(if b && c then a p^2 else 0))) := by
  obtain ⟨d,hd⟩ := l.compact_surface_metric_error (S := S) hK hKO n b c ℓ hℓx hℓy
  refine ⟨d,?_⟩
  intro m B hB
  obtain ⟨D,hD,hbound⟩ := hd m B hB
  refine ⟨D,hD,?_⟩
  intro G hG hGK s z hz hzs hs1 hGb g U hU hinit hy hc H hH E hErr
  have hGO : MapsTo (lowJet G) S O := fun _ hp => hKO (hGK hp)
  have htail := hbound G hG hGK s z hz hzs hs1 hGb U hU hinit hy hc
  have hbase : ContDiffOn ℝ ∞ (fun q => JetVelocityCoordinates.toEuclidean (G q)) S :=
    (JetVelocityCoordinates.toEuclidean.contDiff.comp hG).contDiffOn
  have hfinite := finiteAnsatz_smooth hbase U ℓ (n+1) z
  have hfd := hfinite.fderiv_of_isOpen S.isOpen (m := ∞) (by simp)
  have hmetric : ContDiffOn ℝ ∞ (fun p => inner ℝ
      (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
        U ℓ (n+1) z) p
        (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
      (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
        U ℓ (n+1) z) p
        (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c))) S :=
    (hfd.clm_apply contDiffOn_const).inner ℝ (hfd.clm_apply contDiffOn_const)
  have hmean := l.meanOperator_smooth hG hGO n b c z
  have hAmp : ContDiffOn ℝ ∞ (fun p => if b && c then a p^2 else 0) S := by
    split_ifs
    · exact (ha.pow 2).contDiffOn
    · exact contDiffOn_const
  have hMeanMetric : ContDiffOn ℝ ∞
      (MetricPolynomial.meanMetric g (coordinateVector 0) U n b c z) S := by
    apply (hmean.add hAmp).congr
    intro p hp
    exact l.meanMetric_eq_meanOperator hamp hG hGO n b c z U hU hp
  have hsErr := hErr.shrink_scale hz.le hzs
  have hb := htail.add S.isOpen.uniqueDiffOn hz.le (hmetric.sub hMeanMetric)
    (hmean.sub hH) hsErr
  apply hb.congr
  intro p hp
  dsimp only [g]
  rw [l.meanMetric_eq_meanOperator hamp hG hGO n b c z U hU hp]
  ring

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI

import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveTensorRemainder

namespace OAI

/-! The finite recursion supplies the same supported coefficients for the
actual primitive and its full tensor remainder. Both losses are fixed before
the differentiation order and before the slow map. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem supported_primitive_expansion {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hamp : l.HasSpatialAmplitude a) {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (_hG : ContDiff ℝ ∞ G)
        (_hGQ : MapsTo (lowJet G) S Q),
      ∀ K : Set JetPolynomial.Base, IsClosed K → K ⊆ S →
        (∀ p ∈ S, p ∉ K → ∀ t, l.velocity (lowJet G p,t) = normal (lowJet G p)) →
      ∃ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) ∧
        (∀ i p, p ∉ K → (U i).val p = 0) ∧
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) ∧
        U 0 = (l.geometry G _hG (fun _ hp => hQO (_hGQ hp))).initial ∧
        ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
          WeightedBound S s (m+(2*(n+1)+1)) B (lowJet G) →
          WeightedBound S z m (C*z/s^loss)
            (fun p => finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
              U ℓ (n+1) z p-JetVelocityCoordinates.toEuclidean (G p)) ∧
          WeightedBound S z m (D*z^(n+1)/s^loss)
            (fun p => RealModes.realMetricTensor
              (spaceCoordinates ∘ finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
                U ℓ (n+1) z ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry p)-
              l.meanTensorOperator n z G (planeCoordinateIsometry p)-![a p^2,0,0]) := by
  obtain ⟨dc,hc⟩ := l.bounded_surface_correction (S := S) hQ hQO n ℓ
  obtain ⟨de,he⟩ := l.uniform_primitive_metric_remainder (S := S) ha hamp hQ hQO n ℓ hℓx hℓy
  refine ⟨max dc de,?_⟩
  intro m B hB
  obtain ⟨C,hC,hcb⟩ := hc m B hB
  obtain ⟨D,hD,heb⟩ := he m B hB
  refine ⟨C,D,hC,hD,?_⟩
  intro G hG hGQ K hK hKS hv
  obtain ⟨U,hinit,_,hU,hzero,hy,hcoeff,hrep,hbound⟩ := hcb G hG hGQ K hK hKS hv
  refine ⟨U,hU,hzero,hrep,hinit,?_⟩
  intro s z hz hzs hs1 hb
  have hs : 0 < s := hz.trans_le hzs
  have hden (d : ℕ) (hd : d ≤ max dc de) : s^(max dc de) ≤ s^d :=
    pow_le_pow_of_le_one hs.le hs1 hd
  constructor
  · exact (hbound s z hz hzs hs1 (hb.mono_order (by omega))).mono_const
      (div_le_div_of_nonneg_left (mul_nonneg hC hz.le)
        (pow_pos hs _) (hden dc (le_max_left _ _)))
  · exact (heb G hG hGQ s z hz hzs hs1 hb U hrep hU hinit hy hcoeff).mono_const
      (div_le_div_of_nonneg_left (mul_nonneg hD (pow_nonneg hz.le _))
        (pow_pos hs _) (hden de (le_max_right _ _)))

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI

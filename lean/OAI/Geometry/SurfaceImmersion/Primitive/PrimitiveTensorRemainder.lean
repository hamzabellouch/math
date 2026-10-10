import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveRemainder
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicMetricCoordinates
import OAI.Geometry.SurfaceImmersion.Primitive.LocalAnsatzProfiles

namespace OAI

/-! The three scalar remainder estimates control the actual full metric
tensor of the same finite periodic ansatz. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_primitive_metric_remainder {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hamp : l.HasSpatialAmplitude a) {S : TopologicalSpace.Opens JetPolynomial.Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGK : MapsTo (lowJet G) S K) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s (m+(2*(n+1)+1)) B (lowJet G) →
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r+1)).fluct = 0) →
      WeightedBound S z m (D*z^(n+1)/s^loss)
        (fun p => RealModes.realMetricTensor
          (spaceCoordinates ∘ finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q)) U ℓ (n+1) z ∘
            planeCoordinateIsometry.symm) (planeCoordinateIsometry p)-
          l.meanTensorOperator n z G (planeCoordinateIsometry p)-![a p^2,0,0]) := by
  obtain ⟨loss,hb⟩ := l.uniform_primitive_remainder ha hamp hK hKO n ℓ hℓx hℓy
  refine ⟨loss,?_⟩
  intro m B hB
  obtain ⟨D,hD,hd⟩ := hb m B hB
  refine ⟨D,hD,?_⟩
  intro G hG hGK s z hz hzs hs1 hGb g U hrep hU hinit hy hcoeff
  have hs : 0 < s := hz.trans_le hzs
  have hGO : MapsTo (lowJet G) S O := fun _ hp => hKO (hGK hp)
  let f := finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q)) U ℓ (n+1) z
  have hf : ContDiff ℝ ∞ f := by
    exact PeriodicExpansion.finiteAnsatz_smooth (JetVelocityCoordinates.toEuclidean.contDiff.comp hG)
      (globalCoefficients U hU) ℓ (n+1) z
  let E : Bool → Bool → JetPolynomial.Base → ℝ := fun b c p =>
    inner ℝ
      (fderiv ℝ f p (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
      (fderiv ℝ f p (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c))-
      (l.meanOperator n b c z G p+(if b && c then a p^2 else 0))
  have hEs (b c : Bool) : ContDiffOn ℝ ∞ (E b c) S := by
    have hdf := hf.fderiv_right (m := ∞) (by simp)
    apply ((hdf.clm_apply contDiff_const).inner ℝ (hdf.clm_apply contDiff_const)).contDiffOn.sub
    apply (l.meanOperator_smooth hG hGO n b c z).add
    split_ifs
    · exact (ha.pow 2).contDiffOn
    · exact contDiffOn_const
  have hEb (b c : Bool) : WeightedBound S z m (D*z^(n+1)/s^loss) (E b c) :=
    hd G hG hGK s z hz hzs hs1 hGb U hrep hinit hy hcoeff b c
  let bf : Fin 3 → Bool := ![true,true,false]
  let cf : Fin 3 → Bool := ![true,false,false]
  have hbvec := WeightedBound.pi S.isOpen.uniqueDiffOn hz
    (div_nonneg (mul_nonneg hD (pow_nonneg hz.le _)) (pow_nonneg hs.le _))
    (fun k : Fin 3 => hEs (bf k) (cf k)) (fun k => hEb (bf k) (cf k))
  have heq : (fun p => RealModes.realMetricTensor
      (spaceCoordinates ∘ f ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry p)-
      l.meanTensorOperator n z G (planeCoordinateIsometry p)-![a p^2,0,0]) =
        (fun p k => E (bf k) (cf k) p) := by
    funext p k
    rw [metric_coordinate_tensor hf p]
    fin_cases k <;>
      simp [E,bf,cf,meanTensorOperator,MetricPolynomial.metricDirection]
    ring
  rw [heq]
  exact hbvec

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI

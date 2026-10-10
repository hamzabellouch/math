import OAI.Geometry.SurfaceImmersion.Primitive.SurfacePrimitiveError

namespace OAI

/-! One finite loss and one coefficient profile control all metric components
of the actual periodic primitive, before the slow map is selected. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_primitive_remainder {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a)
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
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r+1)).fluct = 0) →
      ∀ b c : Bool, WeightedBound S z m (D*z^(n+1)/s^loss)
        (fun p => inner ℝ
          (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p
            (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
          (fderiv ℝ (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p
            (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c))-
          (l.meanOperator n b c z G p+(if b && c then a p^2 else 0))) := by
  classical
  choose d hd using fun bc : Bool × Bool => l.compact_primitive_error ha hamp hK hKO n bc.1 bc.2 ℓ hℓx hℓy
  let loss := Finset.univ.sup d
  refine ⟨loss,?_⟩
  intro m B hB
  choose C hC hc using fun bc : Bool × Bool => hd bc m B hB
  let D := ∑ bc : Bool × Bool, C bc
  have hD : 0 ≤ D := Finset.sum_nonneg (fun bc _ => hC bc)
  have hCD (bc : Bool × Bool) : C bc ≤ D :=
    Finset.single_le_sum (fun bc _ => hC bc) (Finset.mem_univ _)
  refine ⟨D,hD,?_⟩
  intro G hG hGK s z hz hzs hs1 hGb g U hU hinit hy hcoeff b c
  have hs : 0 < s := hz.trans_le hzs
  have hmean := l.meanOperator_smooth hG (fun _ hp => hKO (hGK hp)) n b c z
  have hzero : WeightedBound S s m 0
      (l.meanOperator n b c z G-l.meanOperator n b c z G) := by
    have he : l.meanOperator n b c z G-l.meanOperator n b c z G = (fun _ => (0 : ℝ)) := by
      funext p
      exact sub_self _
    rw [he]
    exact weightedBound_zero (S : Set JetPolynomial.Base) s m (F := ℝ)
  have hb := hc (b,c) G hG hGK s z hz hzs hs1 hGb U hU hinit hy hcoeff
    (l.meanOperator n b c z G) hmean 0 hzero
  simp only [add_zero] at hb
  apply hb.mono_const
  have hdl : d (b,c) ≤ loss := Finset.le_sup (Finset.mem_univ _)
  have hp : s^loss ≤ s^d (b,c) := pow_le_pow_of_le_one hs.le hs1 hdl
  calc
    C (b,c)*z^(n+1)/s^d (b,c) ≤ D*z^(n+1)/s^d (b,c) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hCD (b,c)) (pow_nonneg hz.le _)) (pow_nonneg hs.le _)
    _ ≤ D*z^(n+1)/s^loss := div_le_div_of_nonneg_left
      (mul_nonneg hD (pow_nonneg hz.le _)) (pow_pos hs _) hp

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI

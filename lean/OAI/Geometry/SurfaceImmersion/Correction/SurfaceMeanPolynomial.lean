import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceMetricExpansion
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerturbationCalculus
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialCoefficientExtension

namespace OAI

/-! The finite mean correction is an actual higher-jet polynomial, so the
perturbed small-increment solver applies to the same metric expansion. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

def meanTangentExpression (n : ℕ) (b : Bool) : ℕ → VectorExpression :=
  MetricPolynomial.tangentExpression (MetricPolynomial.longitudinal xData l.euclideanVelocity)
    (MetricPolynomial.transverse yData) (l.coefficientExpressions n) 0 1 (n+1) b

def meanPolynomial (n : ℕ) (b c : Bool) : Fin n → Expression := fun r =>
  (MetricPolynomial.finiteMetric (n+1) (r.val+1)
    (l.meanTangentExpression n (b || c)) (l.meanTangentExpression n (b && c))).mean

lemma coefficientExpressions_smooth (n i : ℕ) :
    (l.coefficientExpressions n i).SmoothCoeffs O :=
  MetricPolynomial.coefficients_smooth O.isOpen yData_smooth cData_smooth
    (xData_smooth l) l.euclideanVelocity_smooth
    (fun J hJ => by rw [yData,cData,gram_toEuclidean]; exact l.gram_ne J hJ)
    l.smoothQ (fun _ hJ => l.q_pos hJ) (fun _ hJ => l.euclideanVelocity_length hJ) 0 1 n i

lemma meanPolynomial_smooth (n : ℕ) (b c : Bool) (r : Fin n) :
    (l.meanPolynomial n b c r).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_mean O.isOpen
  apply MetricPolynomial.smooth_finiteMetric
  all_goals
    intro i
    exact MetricPolynomial.smooth_tangentExpression O.isOpen
      (MetricPolynomial.smooth_longitudinal (xData_smooth l) l.euclideanVelocity_smooth)
      (MetricPolynomial.smooth_transverse yData_smooth) (l.coefficientExpressions_smooth n)
      0 1 (n+1) _ i

lemma meanPolynomial_order (n : ℕ) (b c : Bool) (r : Fin n) :
    (l.meanPolynomial n b c r).order ≤ 2*(n+1)+1 := by
  unfold meanPolynomial
  rw [Expression.order_mean]
  apply MetricPolynomial.order_finiteMetric (by omega)
  all_goals
    intro i hi a
    exact MetricPolynomial.order_tangentExpression (by omega)
      (fun _ => le_rfl) (fun _ => le_rfl)
      (fun j _ a => MetricPolynomial.coefficients_order _ _ _ _ _ 0 1 n j a)
      0 1 _ hi a

def meanCoefficientValue {S : TopologicalSpace.Opens JetPolynomial.Base}
    (g : Geometry (E := Euclidean) S (coordinateVector 1))
    (U : ℕ → Family S Euclidean) (b c : Bool) (r : ℕ) (p : JetPolynomial.Base) : ℝ :=
  if b && c then average ((g.xxCoefficient (coordinateVector 0) U r).val p)
  else if b || c then average ((g.xyCoefficient (coordinateVector 0) U r).val p)
  else average ((g.yyCoefficient U r).val p)

/-- Each coefficient used by the slow correction is the mean of the same
coefficient in the actual periodic pullback metric. -/
lemma meanPolynomial_eval {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool) (r : Fin n)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    (l.meanPolynomial n b c r).eval G (p,t) =
      meanCoefficientValue (l.geometry G hG hGO) U b c (r.val+1) p := by
  let g := l.geometry G hG hGO
  have hX : VectorExpression.Represents G
      (MetricPolynomial.longitudinal xData l.euclideanVelocity) g.longitudinal :=
    MetricPolynomial.represents_longitudinal g xData l.euclideanVelocity (fun _ _ => rfl)
      (fun _ hp => l.geometry_velocity hG hGO hp)
  have hY : VectorExpression.Represents G (MetricPolynomial.transverse yData) g.transverse :=
    MetricPolynomial.represents_transverse g yData (fun _ _ => rfl)
  have hT (b : Bool) (i : ℕ) := MetricPolynomial.represents_tangentExpression
    O.isOpen hG hGO 0 1 g hX hY (l.coefficientExpressions_smooth n) hU (n+1) b i
  have hrep := MetricPolynomial.represents_finiteMetric (hT (b || c)) (hT (b && c))
    (n+1) (r.val+1)
  have hs := MetricPolynomial.smooth_finiteMetric
    (fun i => MetricPolynomial.smooth_tangentExpression O.isOpen
      (MetricPolynomial.smooth_longitudinal (xData_smooth l) l.euclideanVelocity_smooth)
      (MetricPolynomial.smooth_transverse yData_smooth) (l.coefficientExpressions_smooth n)
      0 1 (n+1) (b || c) i)
    (fun i => MetricPolynomial.smooth_tangentExpression O.isOpen
      (MetricPolynomial.smooth_longitudinal (xData_smooth l) l.euclideanVelocity_smooth)
      (MetricPolynomial.smooth_transverse yData_smooth) (l.coefficientExpressions_smooth n)
      0 1 (n+1) (b && c) i) (n+1) (r.val+1)
  unfold meanPolynomial meanTangentExpression
  rw [Expression.eval_mean O.isOpen hs G (hGO hp)]
  have hr : 0 < r.val+1 := by omega
  have hrn : r.val+1 < n+1 := by omega
  cases b <;> cases c
  all_goals
    simp only [Bool.and,Bool.or,meanCoefficientValue,Bool.false_eq_true,↓reduceIte]
    simp only [Bool.and,Bool.or] at hrep
    simp_rw [hrep p hp,metricCoefficientFamily_apply]
  · change (∫ s in (0 : ℝ)..1, (g.yyPolynomial U (n+1) p (s : Period)).coeff (r.val+1)) =
      average ((g.yyCoefficient U (r.val+1)).val p)
    simp_rw [g.yyPolynomial_coeff U hr hrn.le]
    exact PeriodicPrimitive.integral_lift_eq_haar _
  · change (∫ s in (0 : ℝ)..1, (g.xyPolynomial (coordinateVector 0) U (n+1) p
      (s : Period)).coeff (r.val+1)) = average ((g.xyCoefficient (coordinateVector 0) U
        (r.val+1)).val p)
    simp_rw [g.xyPolynomial_coeff (coordinateVector 0) U hr hrn]
    exact PeriodicPrimitive.integral_lift_eq_haar _
  · change (∫ s in (0 : ℝ)..1, (g.xyPolynomial (coordinateVector 0) U (n+1) p
      (s : Period)).coeff (r.val+1)) = average ((g.xyCoefficient (coordinateVector 0) U
        (r.val+1)).val p)
    simp_rw [g.xyPolynomial_coeff (coordinateVector 0) U hr hrn]
    exact PeriodicPrimitive.integral_lift_eq_haar _
  · change (∫ s in (0 : ℝ)..1, (g.xxPolynomial (coordinateVector 0) U (n+1) p
      (s : Period)).coeff (r.val+1)) = average ((g.xxCoefficient (coordinateVector 0) U
        (r.val+1)).val p)
    simp_rw [g.xxPolynomial_coeff (coordinateVector 0) U hr hrn]
    exact PeriodicPrimitive.integral_lift_eq_haar _

/-- The full mean correction is precisely the polynomial perturbation
evaluated by the finite-parametrix machinery. -/
lemma meanPolynomial_eval_sum {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    (z : ℝ) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    Perturbation.eval (l.meanPolynomial n b c) z G (p,t) =
      meanCorrection (l.geometry G hG hGO) U n b c z p := by
  unfold Perturbation.eval
  simp_rw [l.meanPolynomial_eval hG hGO n b c _ U hU hp t]
  change (∑ r : Fin n, (fun j : ℕ => z^(j+1)*
    meanCoefficientValue (l.geometry G hG hGO) U b c (j+1) p) r.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => z^(j+1)*
    meanCoefficientValue (l.geometry G hG hGO) U b c (j+1) p)]
  have he := Finset.sum_Ico_add'
    (fun r => z^r*meanCoefficientValue (l.geometry G hG hGO) U b c r p) 0 n 1
  simp only [zero_add,Nat.Ico_zero_eq_range] at he
  rw [he]
  cases b <;> cases c <;>
    simp only [meanCoefficientValue,meanCorrection,Bool.and,Bool.or,Bool.false_eq_true,↓reduceIte]
  all_goals exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The mean pullback metric is the original metric plus the primitive
rank-one term and this explicitly constructed polynomial operator. -/
theorem meanMetric_eq_polynomial {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    (z : ℝ) {p : JetPolynomial.Base} (hp : p ∈ S) :
    MetricPolynomial.meanMetric (l.geometry G hG hGO) (coordinateVector 0) U n b c z p =
      inner ℝ
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) +
      (if b && c then l.amplitude (lowJet G p)^2 else 0) +
        Perturbation.eval (l.meanPolynomial n b c) z G (p,0) := by
  rw [l.meanPolynomial_eval_sum hG hGO n b c U hU z hp 0]
  exact l.meanMetric_eq hG hGO U n b c z hp

/-- Global smooth coefficients for Taylor estimates, retaining exactly the
same operator and loss on the compact set of low jets used by the primitive. -/
theorem meanPolynomial_global_extension {Q : Set LowJet} (hQ : IsCompact Q)
    (hQO : Q ⊆ O) (n : ℕ) (b c : Bool) :
    ∃ P : Fin n → Expression,
      (∀ r, (P r).SmoothCoeffs univ) ∧
      (∀ r, (P r).order = (l.meanPolynomial n b c r).order) ∧
      (∀ r, (P r).loss = (l.meanPolynomial n b c r).loss) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (z : ℝ)
        (p : JetPolynomial.Base) (t : ℝ), lowJet G p ∈ Q →
        Perturbation.eval P z G (p,t) =
          Perturbation.eval (l.meanPolynomial n b c) z G (p,t) := by
  choose P hs ho hl he using fun r : Fin n =>
    Expression.exists_global_extension O.isOpen (l.meanPolynomial_smooth n b c r) hQ hQO
  refine ⟨P,hs,ho,hl,?_⟩
  intro G z p t hp
  unfold Perturbation.eval
  apply Finset.sum_congr rfl
  intro r _
  rw [he r G (p,t) hp]

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI

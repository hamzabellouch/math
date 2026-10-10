import OAI.Geometry.SurfaceImmersion.Correction.PolynomialGeometry
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialCancellation

namespace OAI

/-! The polynomial right-hand sides coincide with those in the actual
triangular metric-cancellation recursion. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion

lemma represents_mixedForcing {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : ℕ → VectorExpression} {U : ℕ → Family S R4}
    (hRs : ∀ i, (R i).SmoothCoeffs O) (hR : ∀ i, VectorExpression.Represents G (R i) (U i))
    {X Y : VectorExpression} {Xf Yf : Family S R4}
    (hX : VectorExpression.Represents G X Xf) (hY : VectorExpression.Represents G Y Yf)
    (dx dy : Fin 2) (r : ℕ) :
    Expression.Represents G (mixedForcing X Y dx dy R r)
      (Xf.inner (LocalPeriodicExpansion.yCoefficient (coordinateVector dy) U r) +
        Yf.inner ((U (r - 1)).slow (coordinateVector dx)) +
        LocalPeriodicExpansion.xyQuadratic (coordinateVector dx) (coordinateVector dy) U r) :=
  Expression.represents_add (Expression.represents_add
    (Expression.represents_dot hX (represents_yCoefficient hO hG hQ hRs hR dy r))
    (Expression.represents_dot hY (VectorExpression.represents_slow hO hG hQ (hRs _) (hR _) dx)))
    (represents_xyQuadratic hO hG hQ hRs hR dx dy r)

lemma represents_longitudinalForcing {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : ℕ → VectorExpression} {U : ℕ → Family S R4}
    (hRs : ∀ i, (R i).SmoothCoeffs O) (hR : ∀ i, VectorExpression.Represents G (R i) (U i))
    {X : VectorExpression} {Xf : Family S R4}
    (hX : VectorExpression.Represents G X Xf) (dx : Fin 2) (r : ℕ) :
    Expression.Represents G (longitudinalForcing X dx R r)
      (Xf.inner ((U (r - 1)).slow (coordinateVector dx)) +
        (1 / 2 : ℝ) • LocalPeriodicExpansion.xxQuadratic (coordinateVector dx) U r) :=
  Expression.represents_add
    (Expression.represents_dot hX (VectorExpression.represents_slow hO hG hQ (hRs _) (hR _) dx))
    (Expression.represents_scale (represents_xxQuadratic hO hG hQ hRs hR dx r) (1 / 2))

lemma represents_transverseForcing {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : ℕ → VectorExpression} {U : ℕ → Family S R4}
    (hRs : ∀ i, (R i).SmoothCoeffs O) (hR : ∀ i, VectorExpression.Represents G (R i) (U i))
    (dy : Fin 2) (r : ℕ) :
    Expression.Represents G (transverseForcing dy R r)
      (LocalPeriodicExpansion.yyQuadratic (coordinateVector dy) U (r + 1)) :=
  represents_yyQuadratic hO hG hQ hRs hR dy (r + 1)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI

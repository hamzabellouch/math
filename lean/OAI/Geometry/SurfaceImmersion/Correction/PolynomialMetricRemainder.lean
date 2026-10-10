import OAI.Geometry.SurfaceImmersion.Correction.PolynomialGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicMetricRemainder

namespace OAI

/-! Actual jet-polynomial representations of every coefficient of the finite
pullback-metric remainder. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion

def finiteMetric (L r : ℕ) (X Y : ℕ → VectorExpression) : Expression :=
  Expression.sumFinset (Finset.range (L + 1)) (fun i =>
    Expression.sumFinset (Finset.range (L + 1)) (fun j =>
      if i + j = r then (X i).dot (Y j) else .coeff (fun _ => 0)))

lemma smooth_finiteMetric {O : Set LowJet} {X Y : ℕ → VectorExpression}
    (hX : ∀ i, (X i).SmoothCoeffs O) (hY : ∀ i, (Y i).SmoothCoeffs O) (L r : ℕ) :
    (finiteMetric L r X Y).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  apply Expression.smoothCoeffs_sumFinset
  intro j _
  split_ifs
  · exact VectorExpression.smoothCoeffs_dot (hX i) (hY j)
  · exact contDiffOn_const

lemma order_finiteMetric {X Y : ℕ → VectorExpression} {L N : ℕ} (hN : 2 ≤ N)
    (hX : ∀ i ≤ L, ∀ a, (X i a).order ≤ N)
    (hY : ∀ i ≤ L, ∀ a, (Y i a).order ≤ N) (r : ℕ) :
    (finiteMetric L r X Y).order ≤ N := by
  apply Expression.order_sumFinset_le _ _ _ hN
  intro i hi
  apply Expression.order_sumFinset_le _ _ _ hN
  intro j hj
  split_ifs
  · exact VectorExpression.order_dot_le hN
      (hX i (by simpa using Finset.mem_range.mp hi))
      (hY j (by simpa using Finset.mem_range.mp hj))
  · exact hN

lemma represents_finiteMetric {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {X Y : ℕ → VectorExpression} {A B : ℕ → Family S R4}
    (hX : ∀ i, VectorExpression.Represents G (X i) (A i))
    (hY : ∀ i, VectorExpression.Represents G (Y i) (B i)) (L r : ℕ) :
    Expression.Represents G (finiteMetric L r X Y) (metricCoefficientFamily L r A B) := by
  apply Expression.represents_sumFinset
  intro i _
  apply Expression.represents_sumFinset
  intro j _
  split_ifs
  · exact Expression.represents_dot (hX i) (hY j)
  · intro p _ t
    rfl

def xTangent (X : VectorExpression) (dx : Fin 2) (U : ℕ → VectorExpression) (L i : ℕ) :
    VectorExpression :=
  if i = 0 then X else if i = L then (U (i - 1)).slow dx else xCoefficient dx U i

def yTangent (Y : VectorExpression) (dy : Fin 2) (U : ℕ → VectorExpression) (i : ℕ) :
    VectorExpression := if i = 0 then Y else yCoefficient dy U i

lemma smooth_xTangent {O : Set LowJet} (hO : IsOpen O) {X : VectorExpression}
    {U : ℕ → VectorExpression} (hX : X.SmoothCoeffs O) (hU : ∀ i, (U i).SmoothCoeffs O)
    (dx : Fin 2) (L i : ℕ) : (xTangent X dx U L i).SmoothCoeffs O := by
  unfold xTangent
  split_ifs
  · exact hX
  · intro a
    exact Expression.smoothCoeffs_slow hO dx (hU _ a)
  · exact smooth_xCoefficient hO hU dx i

lemma smooth_yTangent {O : Set LowJet} (hO : IsOpen O) {Y : VectorExpression}
    {U : ℕ → VectorExpression} (hY : Y.SmoothCoeffs O) (hU : ∀ i, (U i).SmoothCoeffs O)
    (dy : Fin 2) (i : ℕ) : (yTangent Y dy U i).SmoothCoeffs O := by
  unfold yTangent
  split_ifs
  · exact hY
  · exact smooth_yCoefficient hO hU dy i

lemma represents_xTangent {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) S O) {dy : Base} (g : Geometry (E := R4) S dy)
    {X : VectorExpression} {U : ℕ → VectorExpression} {W : ℕ → Family S R4}
    (hX : VectorExpression.Represents G X g.longitudinal)
    (hUs : ∀ i, (U i).SmoothCoeffs O) (hU : ∀ i, VectorExpression.Represents G (U i) (W i))
    (dx : Fin 2) (L i : ℕ) :
    VectorExpression.Represents G (xTangent X dx U L i) (g.xTangent (coordinateVector dx) W L i) := by
  unfold xTangent Geometry.xTangent
  split_ifs
  · exact hX
  · exact VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dx
  · exact represents_xCoefficient hO hG hQ hUs hU dx i

lemma represents_yTangent {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) S O) (dy : Fin 2) (g : Geometry (E := R4) S (coordinateVector dy))
    {Y : VectorExpression} {U : ℕ → VectorExpression} {W : ℕ → Family S R4}
    (hY : VectorExpression.Represents G Y g.transverse)
    (hUs : ∀ i, (U i).SmoothCoeffs O) (hU : ∀ i, VectorExpression.Represents G (U i) (W i)) (i : ℕ) :
    VectorExpression.Represents G (yTangent Y dy U i) (g.yTangent W i) := by
  unfold yTangent Geometry.yTangent
  split_ifs
  · exact hY
  · exact represents_yCoefficient hO hG hQ hUs hU dy i

lemma order_xTangent {X : VectorExpression} {U : ℕ → VectorExpression} {L : ℕ}
    (hL : 1 ≤ L) (hX : ∀ a, (X a).order ≤ 2)
    (hU : ∀ j < L, ∀ a, (U j a).order ≤ 2 * j + 2) (dx : Fin 2) {i : ℕ} (hi : i ≤ L) (a : Fin 4) :
    (xTangent X dx U L i a).order ≤ 2 * L + 1 := by
  unfold xTangent
  split_ifs with hi0 hiL
  · exact (hX a).trans (by omega)
  · have hprev := hU (i - 1) (by omega) a
    have hh := Expression.order_slow_le dx (U (i - 1) a)
    change ((U (i - 1) a).slow dx).order ≤ _
    omega
  · exact (order_xCoefficient (by omega) (by omega) hU dx a).trans (by omega)

lemma order_yTangent {Y : VectorExpression} {U : ℕ → VectorExpression} {L : ℕ}
    (hL : 1 ≤ L) (hY : ∀ a, (Y a).order ≤ 2)
    (hU : ∀ j < L, ∀ a, (U j a).order ≤ 2 * j + 2) (dy : Fin 2) {i : ℕ} (hi : i ≤ L) (a : Fin 4) :
    (yTangent Y dy U i a).order ≤ 2 * L + 1 := by
  unfold yTangent
  split_ifs with hi0
  · exact (hY a).trans (by omega)
  · exact (order_yCoefficient (by omega) hi hU dy a).trans (by omega)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI

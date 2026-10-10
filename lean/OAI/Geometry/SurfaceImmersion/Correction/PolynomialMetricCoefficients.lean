import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialScalar
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicMetricCoefficients

namespace OAI

/-! Actual coordinate polynomial expressions for the metric coefficients in
the finite oscillatory recursion. Index zero denotes the first correction. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

def xCoefficient (dx : Fin 2) (U : ℕ → VectorExpression) (i : ℕ) : VectorExpression :=
  ((U (i - 1)).slow dx).add (U i).angle

def yCoefficient (dy : Fin 2) (U : ℕ → VectorExpression) (i : ℕ) : VectorExpression :=
  (U (i - 1)).slow dy

def xxQuadratic (dx : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : Expression :=
  Expression.sumFinset (Finset.Ico 1 r) (fun i =>
    (xCoefficient dx U i).dot (xCoefficient dx U (r - i)))

def xyQuadratic (dx dy : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : Expression :=
  Expression.sumFinset (Finset.Ico 1 r) (fun i =>
    (xCoefficient dx U i).dot (yCoefficient dy U (r - i)))

def yyQuadratic (dy : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : Expression :=
  Expression.sumFinset (Finset.Ico 1 r) (fun i =>
    (yCoefficient dy U i).dot (yCoefficient dy U (r - i)))

lemma order_xCoefficient {U : ℕ → VectorExpression} {r i : ℕ}
    (hi : 1 ≤ i) (hir : i < r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dx : Fin 2) (a : Fin 4) :
    (xCoefficient dx U i a).order ≤ 2 * i + 2 := by
  have hp := Expression.order_slow_le dx (U (i - 1) a)
  have hprev := hU (i - 1) (by omega) a
  have hcur := hU i hir a
  change max ((U (i - 1) a).slow dx).order ((U i a).angle).order ≤ _
  rw [Expression.order_angle]
  omega

lemma order_yCoefficient {U : ℕ → VectorExpression} {r i : ℕ}
    (hi : 1 ≤ i) (hir : i ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dy : Fin 2) (a : Fin 4) :
    (yCoefficient dy U i a).order ≤ 2 * i + 1 := by
  have hp := Expression.order_slow_le dy (U (i - 1) a)
  have hprev := hU (i - 1) (by omega) a
  exact hp.trans (by omega)

lemma order_xxQuadratic {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dx : Fin 2) :
    (xxQuadratic dx U r).order ≤ 2 * r := by
  apply Expression.order_sumFinset_le _ _ _ (by omega)
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  apply VectorExpression.order_dot_le (by omega)
  · intro a
    exact (order_xCoefficient hi hir hU dx a).trans (by omega)
  · intro a
    exact (order_xCoefficient (by omega) (by omega) hU dx a).trans (by omega)

lemma order_xyQuadratic {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dx dy : Fin 2) :
    (xyQuadratic dx dy U r).order ≤ 2 * r := by
  apply Expression.order_sumFinset_le _ _ _ (by omega)
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  apply VectorExpression.order_dot_le (by omega)
  · intro a
    exact (order_xCoefficient hi hir hU dx a).trans (by omega)
  · intro a
    exact (order_yCoefficient (by omega) (by omega) hU dy a).trans (by omega)

lemma order_yyQuadratic {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2) (dy : Fin 2) :
    (yyQuadratic dy U (r + 1)).order ≤ 2 * r + 1 := by
  apply Expression.order_sumFinset_le _ _ _ (by omega)
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  apply VectorExpression.order_dot_le (by omega)
  · intro a
    exact (order_yCoefficient hi (by omega) hU dy a).trans (by omega)
  · intro a
    exact (order_yCoefficient (by omega) (by omega) hU dy a).trans (by omega)

lemma represents_xCoefficient {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dx : Fin 2) (i : ℕ) :
    VectorExpression.Represents G (xCoefficient dx U i)
      (LocalPeriodicExpansion.xCoefficient (coordinateVector dx) W i) :=
  VectorExpression.represents_add
    (VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dx)
    (VectorExpression.represents_angle hO hQ (hUs _) (hU _))

lemma represents_yCoefficient {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dy : Fin 2) (i : ℕ) :
    VectorExpression.Represents G (yCoefficient dy U i)
      (LocalPeriodicExpansion.yCoefficient (coordinateVector dy) W i) :=
  VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dy

lemma represents_xxQuadratic {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dx : Fin 2) (r : ℕ) :
    Expression.Represents G (xxQuadratic dx U r)
      (LocalPeriodicExpansion.xxQuadratic (coordinateVector dx) W r) := by
  apply Expression.represents_sumFinset
  intro i _
  exact Expression.represents_dot (represents_xCoefficient hO hG hQ hUs hU dx i)
    (represents_xCoefficient hO hG hQ hUs hU dx (r - i))

lemma represents_xyQuadratic {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dx dy : Fin 2) (r : ℕ) :
    Expression.Represents G (xyQuadratic dx dy U r)
      (LocalPeriodicExpansion.xyQuadratic (coordinateVector dx) (coordinateVector dy) W r) := by
  apply Expression.represents_sumFinset
  intro i _
  exact Expression.represents_dot (represents_xCoefficient hO hG hQ hUs hU dx i)
    (represents_yCoefficient hO hG hQ hUs hU dy (r - i))

lemma represents_yyQuadratic {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dy : Fin 2) (r : ℕ) :
    Expression.Represents G (yyQuadratic dy U r)
      (LocalPeriodicExpansion.yyQuadratic (coordinateVector dy) W r) := by
  apply Expression.represents_sumFinset
  intro i _
  exact Expression.represents_dot (represents_yCoefficient hO hG hQ hUs hU dy i)
    (represents_yCoefficient hO hG hQ hUs hU dy (r - i))

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI

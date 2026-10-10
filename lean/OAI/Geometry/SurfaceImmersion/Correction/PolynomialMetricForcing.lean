import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMetricCoefficients

namespace OAI

/-! The right-hand sides of the finite triangular correction step are actual
higher-jet polynomials. Their maximal jet order is the preceding order plus one. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

def mixedForcing (X Y : VectorExpression) (dx dy : Fin 2) (U : ℕ → VectorExpression)
    (r : ℕ) : Expression :=
  .add (.add (X.dot (yCoefficient dy U r)) (Y.dot ((U (r - 1)).slow dx)))
    (xyQuadratic dx dy U r)

def longitudinalForcing (X : VectorExpression) (dx : Fin 2) (U : ℕ → VectorExpression)
    (r : ℕ) : Expression :=
  .add (X.dot ((U (r - 1)).slow dx)) ((xxQuadratic dx U r).scale (1 / 2))

def transverseForcing (dy : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : Expression :=
  yyQuadratic dy U (r + 1)

lemma smooth_xCoefficient {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dx : Fin 2) (i : ℕ) :
    (xCoefficient dx U i).SmoothCoeffs O := by
  intro a
  exact ⟨Expression.smoothCoeffs_slow hO dx (hU _ _),
    Expression.smoothCoeffs_angle hO (hU _ _)⟩

lemma smooth_yCoefficient {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dy : Fin 2) (i : ℕ) :
    (yCoefficient dy U i).SmoothCoeffs O := by
  intro a
  exact Expression.smoothCoeffs_slow hO dy (hU _ _)

lemma smooth_xxQuadratic {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dx : Fin 2) (r : ℕ) :
    (xxQuadratic dx U r).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  exact VectorExpression.smoothCoeffs_dot (smooth_xCoefficient hO hU dx i)
    (smooth_xCoefficient hO hU dx (r - i))

lemma smooth_xyQuadratic {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dx dy : Fin 2) (r : ℕ) :
    (xyQuadratic dx dy U r).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  exact VectorExpression.smoothCoeffs_dot (smooth_xCoefficient hO hU dx i)
    (smooth_yCoefficient hO hU dy (r - i))

lemma smooth_yyQuadratic {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dy : Fin 2) (r : ℕ) :
    (yyQuadratic dy U r).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  exact VectorExpression.smoothCoeffs_dot (smooth_yCoefficient hO hU dy i)
    (smooth_yCoefficient hO hU dy (r - i))

lemma smooth_mixedForcing {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) {X Y : VectorExpression}
    (hX : X.SmoothCoeffs O) (hY : Y.SmoothCoeffs O) (dx dy : Fin 2) (r : ℕ) :
    (mixedForcing X Y dx dy U r).SmoothCoeffs O :=
  ⟨⟨VectorExpression.smoothCoeffs_dot hX (smooth_yCoefficient hO hU dy r),
    VectorExpression.smoothCoeffs_dot hY (fun a => Expression.smoothCoeffs_slow hO dx (hU _ a))⟩,
    smooth_xyQuadratic hO hU dx dy r⟩

lemma smooth_longitudinalForcing {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) {X : VectorExpression}
    (hX : X.SmoothCoeffs O) (dx : Fin 2) (r : ℕ) :
    (longitudinalForcing X dx U r).SmoothCoeffs O :=
  ⟨VectorExpression.smoothCoeffs_dot hX (fun a => Expression.smoothCoeffs_slow hO dx (hU _ a)),
    Expression.smoothCoeffs_scale _ (smooth_xxQuadratic hO hU dx r)⟩

lemma forcing_orders {U : ℕ → VectorExpression} {r : ℕ} (hr : 1 ≤ r)
    (hU : ∀ j < r, ∀ a, (U j a).order ≤ 2 * j + 2)
    {X Y : VectorExpression} (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
    (dx dy : Fin 2) :
    (mixedForcing X Y dx dy U r).order ≤ 2 * r + 1 ∧
      (longitudinalForcing X dx U r).order ≤ 2 * r + 1 ∧
      (transverseForcing dy U r).order ≤ 2 * r + 1 := by
  have hprev : ∀ a, ((U (r - 1)).slow dx a).order ≤ 2 * r + 1 := by
    intro a
    have hd := Expression.order_slow_le dx (U (r - 1) a)
    have hp := hU (r - 1) (by omega) a
    exact hd.trans (by omega)
  have hXslow := VectorExpression.order_dot_le (by omega : 2 ≤ 2 * r + 1)
    (fun a => (hX a).trans (by omega)) hprev
  have hYslow := VectorExpression.order_dot_le (by omega : 2 ≤ 2 * r + 1)
    (fun a => (hY a).trans (by omega)) hprev
  have hXy := VectorExpression.order_dot_le (by omega : 2 ≤ 2 * r + 1)
    (fun a => (hX a).trans (by omega)) (order_yCoefficient hr (le_refl r) hU dy)
  have hxy := order_xyQuadratic hr hU dx dy
  have hxx := order_xxQuadratic hr hU dx
  have hyy := order_yyQuadratic hr hU dy
  refine ⟨?_, ?_, hyy⟩
  · change max (max _ _) _ ≤ _
    exact max_le (max_le hXy hYslow) (hxy.trans (by omega))
  · change max _ ((xxQuadratic dx U r).scale (1 / 2)).order ≤ _
    rw [Expression.order_scale]
    exact max_le hXslow (hxx.trans (by omega))

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI

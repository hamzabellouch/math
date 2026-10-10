import OAI.Geometry.EinsteinFour.CurvatureFirstBianchi
import OAI.Geometry.EinsteinFour.CurvatureMetricSkew

namespace OAI

/-! The finite algebra relating the linearized coordinate geodesic
equation to the curvature convention used by the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

abbrev JacobiCoordinateVector := Fin 4 → ℝ

def jacobiConnection (Γ : Fin 4 → Mat4) (v : JacobiCoordinateVector) : Mat4 :=
  ∑ i, v i • Γ i

def jacobiConnectionDerivative (D : Fin 4 → Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) : Mat4 := ∑ i, ∑ j, (v i * w j) • D i j

def jacobiCurvature (Γ : Fin 4 → Mat4) (D : Fin 4 → Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) : Mat4 :=
  ∑ i, ∑ j, (v i * w j) • (D i j - D j i + Γ i * Γ j - Γ j * Γ i)

private theorem weighted_matrix_swap (D : Fin 4 → Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) :
    (∑ i, ∑ j, (v i * w j) • D j i) = ∑ i, ∑ j, (w i * v j) • D i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

private theorem jacobiConnection_mul (Γ : Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) :
    jacobiConnection Γ v * jacobiConnection Γ w =
      ∑ i, ∑ j, (v i * w j) • (Γ i * Γ j) := by
  simp only [jacobiConnection, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem jacobiCurvature_eq (Γ : Fin 4 → Mat4) (D : Fin 4 → Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) :
    jacobiCurvature Γ D v w =
      jacobiConnectionDerivative D v w - jacobiConnectionDerivative D w v +
        jacobiConnection Γ v * jacobiConnection Γ w -
          jacobiConnection Γ w * jacobiConnection Γ v := by
  simp only [jacobiCurvature, smul_sub, smul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  rw [weighted_matrix_swap D v w, weighted_matrix_swap (fun i j => Γ i * Γ j) v w,
    ← jacobiConnection_mul Γ v w, ← jacobiConnection_mul Γ w v]
  rfl

theorem jacobiConnection_mulVec_comm (Γ : Fin 4 → Mat4)
    (hΓ : ∀ a i j, Γ i a j = Γ j a i) (v w : JacobiCoordinateVector) :
    jacobiConnection Γ v *ᵥ w = jacobiConnection Γ w *ᵥ v := by
  ext a
  simp only [jacobiConnection, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hΓ a i j]
  ring

theorem jacobiConnectionDerivative_mulVec_comm (D : Fin 4 → Fin 4 → Mat4)
    (hD : ∀ r a i j, D r i a j = D r j a i)
    (v w u : JacobiCoordinateVector) :
    jacobiConnectionDerivative D v w *ᵥ u =
      jacobiConnectionDerivative D v u *ᵥ w := by
  have hm (w : JacobiCoordinateVector) : jacobiConnectionDerivative D v w =
      ∑ i, v i • jacobiConnection (D i) w := by
    simp only [jacobiConnectionDerivative, jacobiConnection, Finset.smul_sum, smul_smul]
  calc
    _ = ∑ i, v i • (jacobiConnection (D i) w *ᵥ u) := by
      rw [hm w, Matrix.sum_mulVec]
      simp only [Matrix.smul_mulVec]
    _ = ∑ i, v i • (jacobiConnection (D i) u *ᵥ w) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [jacobiConnection_mulVec_comm (D i) (hD i)]
    _ = _ := by
      rw [hm u, Matrix.sum_mulVec]
      simp only [Matrix.smul_mulVec]

/-- The coordinate variation equation implies the covariant Jacobi
equation. Only torsion freedom and its differentiated identity enter. -/
theorem linearized_geodesic_curvature_identity
    (Γ : Fin 4 → Mat4) (D : Fin 4 → Fin 4 → Mat4)
    (hΓ : ∀ a i j, Γ i a j = Γ j a i)
    (hD : ∀ r a i j, D r i a j = D r j a i)
    (v a y w b : JacobiCoordinateVector)
    (ha : a = -(jacobiConnection Γ v *ᵥ v))
    (hb : b = -(jacobiConnectionDerivative D y v *ᵥ v) -
      jacobiConnection Γ w *ᵥ v - jacobiConnection Γ v *ᵥ w) :
    b + jacobiConnectionDerivative D v v *ᵥ y + jacobiConnection Γ a *ᵥ y +
      (2 : ℝ) • (jacobiConnection Γ v *ᵥ w) +
      jacobiConnection Γ v *ᵥ (jacobiConnection Γ v *ᵥ y) +
      jacobiCurvature Γ D y v *ᵥ v = 0 := by
  have ha' : jacobiConnection Γ a *ᵥ y =
      -(jacobiConnection Γ y *ᵥ (jacobiConnection Γ v *ᵥ v)) := by
    rw [jacobiConnection_mulVec_comm Γ hΓ a y, ha, Matrix.mulVec_neg]
  rw [hb, ha', jacobiConnectionDerivative_mulVec_comm D hD v v y,
    jacobiConnection_mulVec_comm Γ hΓ w v, jacobiCurvature_eq,
    Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    jacobiConnection_mulVec_comm Γ hΓ v y]
  module

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem actual_jacobiConnection_comm (g : SmoothMetric M) (c : M) (z : FourSpace)
    (v w : JacobiCoordinateVector) :
    jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ w =
      jacobiConnection (fun i => connectionMatrix g c i z) w *ᵥ v :=
  jacobiConnection_mulVec_comm _ (fun a i j => christoffel_comm g c z a i j) v w

theorem actual_jacobiCurvature_eq (g : SmoothMetric M) (c : M) (z : FourSpace)
    (v w : JacobiCoordinateVector) :
    jacobiCurvature (fun i => connectionMatrix g c i z)
        (fun i j => matrixPartial (connectionMatrix g c j) i z) v w =
      ∑ i, ∑ j, (v i * w j) • coordinateCurvatureMatrix g c i j z := rfl

theorem actual_linearized_geodesic_curvature_identity
    (g : SmoothMetric M) (c : M) (z : FourSpace)
    (v a y w b : JacobiCoordinateVector)
    (ha : a = -(jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ v))
    (hb : b = -(jacobiConnectionDerivative
        (fun i j => matrixPartial (connectionMatrix g c j) i z) y v *ᵥ v) -
      jacobiConnection (fun i => connectionMatrix g c i z) w *ᵥ v -
      jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ w) :
    b + jacobiConnectionDerivative
        (fun i j => matrixPartial (connectionMatrix g c j) i z) v v *ᵥ y +
      jacobiConnection (fun i => connectionMatrix g c i z) a *ᵥ y +
      (2 : ℝ) • (jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ w) +
      jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ
        (jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ y) +
      (∑ i, ∑ j, (y i * v j) • coordinateCurvatureMatrix g c i j z) *ᵥ v = 0 := by
  have hD (r a i j : Fin 4) :
      matrixPartial (connectionMatrix g c i) r z a j =
        matrixPartial (connectionMatrix g c j) r z a i := by
    change partialDeriv (fun p => christoffel g c p a i j) r z =
      partialDeriv (fun p => christoffel g c p a j i) r z
    exact congrArg (fun f : FourSpace → ℝ => partialDeriv f r z)
      (funext fun p => christoffel_comm g c p a i j)
  exact linearized_geodesic_curvature_identity _ _
    (fun a i j => christoffel_comm g c z a i j) hD v a y w b ha hb

end
end PositiveEinsteinFour.Geometry

end OAI

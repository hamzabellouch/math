import OAI.Geometry.EinsteinFour.WeylGeometry

namespace OAI

/-! Coordinate covariant derivatives of the actual curvature tensor. The
scalar-curvature contribution is subtracted in the Ricci=3g normalization.
The definitions retain all tensor slots until after differentiation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev CovariantCoordinates (n : ℕ) := (Fin n → Fin 4) → ℝ

/-- Coordinate components of `<R(e_a,e_b)e_c,e_d>`. -/
def curvatureCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 4 := fun a =>
  ∑ l, metricInChart g c z l (a 3) *
    curvatureComponent g c z l (a 0) (a 1) (a 2)

/-- The curvature-one algebraic tensor in arbitrary coordinates. -/
def unitCurvatureCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 4 := fun a =>
  metricInChart g c z (a 1) (a 2) * metricInChart g c z (a 0) (a 3) -
    metricInChart g c z (a 0) (a 2) * metricInChart g c z (a 1) (a 3)

/-- For Ricci=3g this is exactly the Weyl four-tensor. Defining its coordinate
field first ensures that derivatives are taken before choosing eigenframes. -/
def normalizedWeylCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 4 := curvatureCoordinates g c z - unitCurvatureCoordinates g c z

/-- The induced Levi-Civita derivative on covariant coordinate tensors. The
leading slot records the direction of differentiation. -/
def covariantDerivative {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace) :
    CovariantCoordinates (n + 1) := fun a =>
  partialDeriv (fun w => T w (fun i => a i.succ)) (a 0) z -
    ∑ i : Fin n, ∑ b : Fin 4,
      christoffel g c z b (a 0) (a i.succ) *
        T z (Function.update (fun i => a i.succ) i b)

/-- Pull back every covariant slot by a single actual orthonormal frame. -/
def frameTensor {n : ℕ} (A : Mat4) (T : CovariantCoordinates n) :
    CovariantCoordinates n := fun a =>
  ∑ b : Fin n → Fin 4, (∏ i, A (b i) (a i)) * T b

/-- The two-form contraction for a tensor with no derivative slots. -/
def blockCoordinates (T : CovariantCoordinates 4) (Q : Fin 3 → Mat4) : Mat3 :=
  curvatureBlock (fun p q => T ![p.1, p.2, q.2, q.1]) Q

/-- A fixed derivative direction in the covariant derivative of curvature. -/
def gradientBlock (T : CovariantCoordinates 5) (Q : Fin 3 → Mat4)
    (i : Fin 4) : Mat3 :=
  blockCoordinates (fun a => T (Fin.cons i a)) Q

/-- Both derivative directions in the covariant Hessian of curvature. -/
def hessianBlock (T : CovariantCoordinates 6) (Q : Fin 3 → Mat4)
    (i j : Fin 4) : Mat3 :=
  blockCoordinates (fun a => T (Fin.cons i (Fin.cons j a))) Q

/-- The actual plus-block covariant gradient in an orthonormal frame. -/
def plusWeylGradient (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i : Fin 4) : Mat3 :=
  gradientBlock (frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c)))
    TraceHessian.quaternionMatrix i

/-- The actual plus-block covariant Hessian, before any trace decomposition. -/
def plusWeylHessian (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i j : Fin 4) : Mat3 :=
  hessianBlock (frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))) TraceHessian.quaternionMatrix i j

/-- The opposite block is differentiated in the same actual coordinate
connection, before the orthonormal frame and Hodge basis are applied. -/
def minusWeylGradient (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i : Fin 4) : Mat3 :=
  gradientBlock (frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c)))
    oppositeQuaternion i

def minusWeylHessian (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i j : Fin 4) : Mat3 :=
  hessianBlock (frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))) oppositeQuaternion i j

end

end PositiveEinsteinFour.Geometry

end OAI

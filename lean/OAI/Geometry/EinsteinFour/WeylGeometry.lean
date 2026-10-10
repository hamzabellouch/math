import OAI.Geometry.EinsteinFour.Statement
import OAI.Geometry.EinsteinFour.TraceHessian
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace OAI

/-! Concrete orthonormal frames and curvature blocks of the metric in the
classification statement, defined from its chart curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def chartMetric (g : SmoothMetric M) (c : M) : Mat4 :=
  metricInChart g c (chartAt FourSpace c c)

def chartRicci (g : SmoothMetric M) (c : M) : Mat4 :=
  ricciInChart g c (chartAt FourSpace c c)

/-- Columns are the coordinates of an orthonormal tangent frame in the same
chart as the concrete metric and curvature used by `ClassificationOn`. -/
structure OrthonormalFrame (g : SmoothMetric M) (c : M) where
  matrix : Mat4
  orthonormal : matrixᵀ * chartMetric g c * matrix = 1

namespace OrthonormalFrame

variable {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c)

theorem det_ne_zero : e.matrix.det ≠ 0 := by
  have h := congrArg Matrix.det e.orthonormal
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  intro hz
  simp [hz] at h

/-- The actual linear change from frame coordinates to chart coordinates. -/
def map : FourSpace →ₗ[ℝ] FourSpace :=
  (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.toLinearMap ∘ₗ
    (Matrix.mulVecLin e.matrix) ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).toLinearMap

theorem map_apply (u : FourSpace) (i : Fin 4) :
    e.map u i = ∑ j, e.matrix i j * u j := rfl

theorem map_injective : Function.Injective e.map := by
  intro u v h
  apply (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).injective
  apply Matrix.mulVec_injective_of_det_ne_zero e.det_ne_zero
  exact congrArg WithLp.ofLp h

def vector (i : Fin 4) : FourSpace := WithLp.toLp 2 (fun a => e.matrix a i)

@[simp] theorem vector_apply (i a : Fin 4) : e.vector i a = e.matrix a i := rfl

/-- Pullback of the actual chart Ricci tensor. -/
def ricci : Mat4 := e.matrixᵀ * chartRicci g c * e.matrix

/-- Normalization of Ricci transfers to every orthonormal frame. -/
theorem ricci_eq_three_one
    (hRic : chartRicci g c = (3 : ℝ) • chartMetric g c) :
    e.ricci = (3 : ℝ) • (1 : Mat4) := by
  unfold ricci
  rw [hRic, mul_smul_comm, smul_mul_assoc, e.orthonormal]

/-- Positivity in chart coordinates is preserved by the actual invertible
frame change. This uses the sectional-curvature predicate in the target. -/
theorem sectional_pos (hsec : HasPositiveSectionalCurvature g)
    (u v : FourSpace) (huv : LinearIndependent ℝ ![u, v]) :
    0 < sectionalNumerator g c (chartAt FourSpace c c) (e.map u) (e.map v) := by
  apply hsec
  have h := huv.map' e.map (LinearMap.ker_eq_bot.mpr e.map_injective)
  have heq : e.map ∘ ![u, v] = ![e.map u, e.map v] := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at h

end OrthonormalFrame

/-- The Riemann tensor evaluated on an actual orthonormal frame. Its slots
are `<R(e_i,e_j)e_k,e_l>`, matching `sectionalNumerator`. -/
def frameCurvature (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i j k l : Fin 4) : ℝ :=
  ∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
    chartMetric g c a b * curvatureComponent g c (chartAt FourSpace c c) a p q r *
      e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b l

theorem frameCurvature_sectional (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i j : Fin 4) :
    frameCurvature g c e i j j i =
      sectionalNumerator g c (chartAt FourSpace c c) (e.vector i) (e.vector j) := rfl

/-- The second quaternion triple is obtained by reversing the first frame
axis. This exchanges the two Hodge-star eigenspaces. -/
def oppositeQuaternion (s : Fin 3) (i j : Fin 4) : ℝ :=
  (if i = 0 then (-1 : ℝ) else 1) *
    (if j = 0 then (-1 : ℝ) else 1) * TraceHessian.quaternionMatrix s i j

/-- Curvature as a bilinear form on two-form coordinates. -/
def curvaturePairing (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (p q : Fin 4 × Fin 4) : ℝ := frameCurvature g c e p.1 p.2 q.2 q.1

/-- The factor 1/8 accounts for antisymmetric coordinate pairs and the
`1/sqrt(2)` normalization of the quaternionic two-form basis. -/
def curvatureBlock (R : (Fin 4 × Fin 4) → (Fin 4 × Fin 4) → ℝ)
    (Q : Fin 3 → Mat4) : Mat3 := fun s t =>
  (1 / 8 : ℝ) * ∑ p, ∑ q, R p q * Q s p.1 p.2 * Q t q.1 q.2

/-- The self-dual Weyl block in the normalized Ricci=3g convention. -/
def plusWeyl (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) : Mat3 :=
  curvatureBlock (curvaturePairing g c e) TraceHessian.quaternionMatrix - 1

/-- The anti-self-dual Weyl block in the same concrete frame. -/
def minusWeyl (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) : Mat3 :=
  curvatureBlock (curvaturePairing g c e) oppositeQuaternion - 1

/-- The normalized Weyl norm, written without a choice of eigenvectors. -/
def normalizedBlockNorm (T : Mat3) : ℝ :=
  Real.sqrt ((∑ i, ∑ j, T i j ^ 2) / 6)

theorem normalizedBlockNorm_nonneg (T : Mat3) : 0 ≤ normalizedBlockNorm T :=
  Real.sqrt_nonneg _

theorem normalizedBlockNorm_sq (T : Mat3) :
    normalizedBlockNorm T ^ 2 = (∑ i, ∑ j, T i j ^ 2) / 6 := by
  apply Real.sq_sqrt
  positivity

/-- Vanishing of the normalized norm is exactly vanishing of the concrete
curvature block. -/
theorem normalizedBlockNorm_eq_zero_iff (T : Mat3) :
    normalizedBlockNorm T = 0 ↔ T = 0 := by
  constructor
  · intro hz
    have hsum : (∑ i, ∑ j, T i j ^ 2) = 0 := by
      have hs := normalizedBlockNorm_sq T
      rw [hz] at hs
      linarith
    ext i j
    have hj : T i j ^ 2 ≤ ∑ k, T i k ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have hi : (∑ k, T i k ^ 2) ≤ ∑ a, ∑ k, T a k ^ 2 :=
      Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hsq : T i j ^ 2 = 0 := le_antisymm (hsum ▸ hj.trans hi) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hsq
  · rintro rfl
    simp [normalizedBlockNorm]

/-- Pair symmetry of curvature implies symmetry of its actual block. -/
theorem curvatureBlock_symmetric
    {R : (Fin 4 × Fin 4) → (Fin 4 × Fin 4) → ℝ}
    (hR : ∀ p q, R p q = R q p) (Q : Fin 3 → Mat4) :
    (curvatureBlock R Q)ᵀ = curvatureBlock R Q := by
  ext s t
  change (1 / 8 : ℝ) * (∑ p, ∑ q, R p q * Q t p.1 p.2 * Q s q.1 q.2) =
    (1 / 8 : ℝ) * (∑ p, ∑ q, R p q * Q s p.1 p.2 * Q t q.1 q.2)
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hR]
  ring

end

end PositiveEinsteinFour.Geometry

end OAI

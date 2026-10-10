import OAI.Analysis.HyperbolicCones.Pencil
import OAI.Analysis.HyperbolicCones.TangentObstruction
import OAI.Analysis.HyperbolicCones.Deformation
import OAI.Analysis.HyperbolicCones.LinePolynomial
import OAI.Analysis.HyperbolicCones.ConeZero
import OAI.Analysis.HyperbolicCones.Coordinates

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem cone_not_spectrahedral (N : ℕ) (hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N) :
    cone ≠ {x | (L x : Mat N ℝ).PosSemidef} := by
  intro hL
  obtain ⟨P⟩ := pencil_normalization N hN L hL
  exact P.impossible

/-- An explicit degree-20 hyperbolic polynomial in a 23-dimensional real space
whose closed hyperbolicity cone is not spectrahedral. -/
theorem main_result :
    Module.finrank ℝ Ambient = 23 ∧
    polynomial.IsHomogeneous 20 ∧
    polynomial.totalDegree = 20 ∧
    MvPolynomial.eval (coordinates basePoint) polynomial = 1 ∧
    (∀ (x : Ambient) (z : ℂ), (linePolynomial x).aeval z = 0 → z.im = 0) ∧
    ∀ (N : ℕ) (_hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N),
      cone ≠ {x | (L x : Mat N ℝ).PosSemidef} := by
  exact ⟨ambient_finrank, polynomial_homogeneous, polynomial_totalDegree,
    polynomial_basePoint, linePolynomial_complex_roots_real, cone_not_spectrahedral⟩

end Paper256

end

end OAI

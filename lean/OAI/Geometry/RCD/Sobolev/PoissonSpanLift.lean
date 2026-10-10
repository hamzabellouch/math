import OAI.Geometry.RCD.Coordinates.PoissonSpanCoordinates

namespace OAI

/-! # Isometric inclusion of all coordinate covectors in the Poisson span -/

open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

def poissonCoordinateLift {n : ℕ} (b : Euclidean n) : Euclidean (n + 2) :=
  WithLp.toLp 2 (Fin.append (fun i => b i) (fun _ : Fin 2 => (0 : ℝ)))

theorem poissonCoordinateLift_norm {n : ℕ} (b : Euclidean n) :
    ‖poissonCoordinateLift b‖ = ‖b‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, poissonCoordinateLift, Fin.sum_univ_add]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : MeasureTheory.Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem poissonSpanMap_lift {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (f : Fin 2 → SobolevSpace μ hQ) (b : Euclidean n) :
    sobolevColumnMap μ hQ (poissonSpan μ hQ u f) (poissonCoordinateLift b) =
      sobolevColumnMap μ hQ u b := by
  simp [sobolevColumnMap_apply, poissonCoordinateLift, poissonSpan, Fin.sum_univ_add]

omit [MetricSpace X] [MeasurableSpace X] in
theorem poissonSpanLaplacian_lift {n : ℕ} (c : ℝ) (b : Euclidean n) :
    poissonSpanLaplacian n c (poissonCoordinateLift b) = 0 := by
  simp [poissonSpanLaplacian, poissonCoordinateLift, Fin.sum_univ_add,
    EuclideanSpace.projₗ, PiLp.projₗ_apply]

end RegularPointCoordinates

end

end OAI

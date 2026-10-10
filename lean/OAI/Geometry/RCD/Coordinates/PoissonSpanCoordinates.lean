import OAI.Geometry.RCD.Sobolev.PoissonSpan

namespace OAI

/-! # The actual coordinate directions in the finite Poisson span -/

open Set Metric MeasureTheory
open scoped BigOperators NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem poissonSpanMap_right {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (f : Fin 2 → SobolevSpace μ hQ) (j : Fin 2) :
    sobolevColumnMap μ hQ (poissonSpan μ hQ u f)
      (EuclideanSpace.single (Fin.natAdd n j) 1) = f j := by
  rw [sobolevColumnMap_single]
  exact Fin.append_right u f j

theorem poissonSpanMap_left {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (f : Fin 2 → SobolevSpace μ hQ) (j : Fin n) :
    sobolevColumnMap μ hQ (poissonSpan μ hQ u f)
      (EuclideanSpace.single (Fin.castAdd 2 j) 1) = u j := by
  rw [sobolevColumnMap_single]
  exact Fin.append_left u f j

omit [MetricSpace X] [MeasurableSpace X] in
theorem poissonSpanLaplacian_single {n : ℕ} (c : ℝ) (j : Fin (n + 2)) :
    poissonSpanLaplacian n c (EuclideanSpace.single j 1) =
      Fin.append (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin 2 => c) j := by
  simp [poissonSpanLaplacian, EuclideanSpace.projₗ, PiLp.projₗ_apply, PiLp.single_apply]

omit [MetricSpace X] [MeasurableSpace X] in
theorem poissonSpanLaplacian_right {n : ℕ} (c : ℝ) (j : Fin 2) :
    poissonSpanLaplacian n c (EuclideanSpace.single (Fin.natAdd n j) 1) = c := by
  rw [poissonSpanLaplacian_single]
  exact Fin.append_right _ _ _

omit [MetricSpace X] [MeasurableSpace X] in
theorem poissonSpanLaplacian_left {n : ℕ} (c : ℝ) (j : Fin n) :
    poissonSpanLaplacian n c (EuclideanSpace.single (Fin.castAdd 2 j) 1) = 0 := by
  rw [poissonSpanLaplacian_single]
  exact Fin.append_left _ _ _

end RegularPointCoordinates

end

end OAI

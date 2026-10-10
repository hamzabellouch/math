import OAI.Geometry.RCD.Sobolev.PoissonSpanLift

namespace OAI

/-! # The coordinate inclusion as a continuous linear map -/

open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

def poissonCoordinateLiftLinear (n : ℕ) : Euclidean n →L[ℝ] Euclidean (n + 2) :=
  LinearMap.mkContinuous
    { toFun := poissonCoordinateLift
      map_add' := by
        intro b c
        ext j
        refine Fin.addCases ?_ ?_ j
        · intro k
          simp [poissonCoordinateLift]
        · intro k
          simp [poissonCoordinateLift]
      map_smul' := by
        intro c b
        ext j
        refine Fin.addCases ?_ ?_ j
        · intro k
          simp [poissonCoordinateLift]
        · intro k
          simp [poissonCoordinateLift] }
    1 (by
      intro b
      change ‖poissonCoordinateLift b‖ ≤ 1 * ‖b‖
      simpa only [one_mul] using (poissonCoordinateLift_norm b).le)

@[simp] theorem poissonCoordinateLiftLinear_apply {n : ℕ} (b : Euclidean n) :
    poissonCoordinateLiftLinear n b = poissonCoordinateLift b := rfl

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The coordinate block of the actual joint span is exactly the original map. -/
theorem poissonSpanMap_comp_lift (μ : MeasureTheory.Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (f : Fin 2 → SobolevSpace μ hQ) :
    (sobolevColumnMap μ hQ (poissonSpan μ hQ u f)).comp (poissonCoordinateLiftLinear n) =
      sobolevColumnMap μ hQ u := by
  apply ContinuousLinearMap.ext
  intro b
  exact poissonSpanMap_lift μ hQ u f b

end RegularPointCoordinates

end

end OAI

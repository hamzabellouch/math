import OAI.Geometry.SurfaceImmersion.Primitive.CrossingCoordinateMap

namespace OAI

/-! The two standard coordinate planes used for a regular double point. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def leftCrossingPlane (u : Base) : Base × ℝ := (![u 0,0],u 1)
def rightCrossingPlane (u : Base) : Base × ℝ := (![0,u 0],u 1)

lemma leftCrossingPlane_smooth : ContDiff ℝ ∞ leftCrossingPlane := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [leftCrossingPlane] <;> fun_prop
  · change ContDiff ℝ ∞ (fun u : Base => u 1)
    fun_prop

lemma rightCrossingPlane_smooth : ContDiff ℝ ∞ rightCrossingPlane := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [rightCrossingPlane] <;> fun_prop
  · change ContDiff ℝ ∞ (fun u : Base => u 1)
    fun_prop

lemma leftCrossingPlane_axis (t : ℝ) : leftCrossingPlane ![0,t] = (0,t) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · rfl

lemma rightCrossingPlane_axis (t : ℝ) : rightCrossingPlane ![0,t] = (0,t) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · rfl

lemma crossingCoordinateMap_leftPlane {F G : Base → ProjectionTarget 3} (u : Base)
    (he : F ![0,u 1] = G ![0,u 1]) :
    crossingCoordinateMap F G (leftCrossingPlane u) = F u := by
  have hu : (![u 0,u 1] : Base) = u := by ext i; fin_cases i <;> rfl
  have h := crossingCoordinateMap_left he (u 0)
  change crossingCoordinateMap F G (leftCrossingPlane u) = F ![u 0,u 1] at h
  rwa [hu] at h

lemma crossingCoordinateMap_rightPlane (F G : Base → ProjectionTarget 3) (u : Base) :
    crossingCoordinateMap F G (rightCrossingPlane u) = G u := by
  have hu : (![u 0,u 1] : Base) = u := by ext i; fin_cases i <;> rfl
  have h := crossingCoordinateMap_right F G (u 0) (u 1)
  change crossingCoordinateMap F G (rightCrossingPlane u) = G ![u 0,u 1] at h
  rwa [hu] at h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

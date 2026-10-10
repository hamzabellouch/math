import OAI.Geometry.IsometricImmersion.Calculus.ExtremumHessian
import OAI.Geometry.IsometricImmersion.Darboux.HeightEquation
import OAI.Geometry.IsometricImmersion.Energy.HeightEnergy
import Mathlib.Analysis.Matrix.PosDef

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

theorem heightEnergy_at_critical (g : MetricField) (z : Coord → ℝ) (p : Coord)
    (hcrit : fderiv ℝ z p = 0) : heightEnergy g z p = (g p).det := by
  simp [heightEnergy, covectorNormSq, coordPartial, hcrit]

theorem no_localExtr_at_negative_curvature
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (hK : gaussianCurvature g p < 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    ¬IsLocalExtr z p := by
  intro he
  have hc := covHessian_at_localExtr hg hz hU hp he
  have hE : 0 < heightEnergy g z p := by
    rw [heightEnergy_at_critical g z p hc.1]
    exact (hg.2 p hp).det_pos
  have hneg : (covHessian g z p).det < 0 := by
    rw [hD]
    exact mul_neg_of_neg_of_pos hK hE
  exact (not_lt_of_ge hc.2.2) hneg

theorem immersion_height_no_localExtr
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (e : Ambient) (he : inner ℝ e e = 1) (hp : p ∈ U)
    (hK : gaussianCurvature g p < 0) : ¬IsLocalExtr (height F e) p := by
  apply no_localExtr_at_negative_curvature hg (height_smooth hF.1 e) hU hp hK
  simpa only [heightEnergy, mul_assoc] using geometric_height_equation hg hF hU e he hp

end SmoothLocal.Geometry

end

end OAI

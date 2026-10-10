import OAI.Geometry.SurfaceImmersion.Atlas.ConvexQuadraticPhase
import OAI.Geometry.SurfaceImmersion.Geometry.RealMetricDerivatives

namespace OAI

/-! The negative tangential acceleration required by the velocity plane is
the actual Christoffel coefficient of the induced metric. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame PhaseGeometry

def inducedCoordinateMetric (F : RField 4) (p : Base) : PhaseMean.Tensor :=
  ![realMetric F dx dx p,realMetric F dx dy p,realMetric F dy dy p]

lemma inducedCoordinateMetric_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (inducedCoordinateMetric F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact real_dot_smooth (contDiff_real_coordDeriv hF dx) (contDiff_real_coordDeriv hF dx)
  · exact real_dot_smooth (contDiff_real_coordDeriv hF dx) (contDiff_real_coordDeriv hF dy)
  · exact real_dot_smooth (contDiff_real_coordDeriv hF dy) (contDiff_real_coordDeriv hF dy)

lemma inducedCoordinateMetric_derivative {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v : Base) (i : Fin 3) :
    fderiv ℝ (inducedCoordinateMetric F) p v i =
      coordDeriv v (fun q => inducedCoordinateMetric F q i) p := by
  have he := congrArg (fun L : Base →L[ℝ] ℝ => L v)
    (fderiv_apply ((inducedCoordinateMetric_smooth hF).differentiable (by simp) p) i)
  exact he.symm

lemma induced_connection_yy {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base) :
    metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) 2 =
      (((coordDeriv dy F p ⬝ᵥ coordDeriv dy F p) *
          (coordDeriv dx F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p) -
        (coordDeriv dx F p ⬝ᵥ coordDeriv dy F p) *
          (coordDeriv dy F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p)) /
          gramDet (coordDeriv dx F p) (coordDeriv dy F p),
       ((coordDeriv dx F p ⬝ᵥ coordDeriv dx F p) *
          (coordDeriv dy F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p) -
        (coordDeriv dx F p ⬝ᵥ coordDeriv dy F p) *
          (coordDeriv dx F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p)) /
          gramDet (coordDeriv dx F p) (coordDeriv dy F p)) := by
  have ha : coordDeriv dy (realMetric F dx dy) p - coordDeriv dx (realMetric F dy dy) p/2 =
      coordDeriv dx F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p := by
    simp only [realMetric_partial hF,real_second_coordDeriv_comm hF p dy dx]
    rw [dotProduct_comm (coordDeriv dy F p) (coordDeriv dx (coordDeriv dy F) p)]
    ring
  have hb : coordDeriv dy (realMetric F dy dy) p/2 =
      coordDeriv dy F p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p := by
    rw [realMetric_partial hF,dotProduct_comm (coordDeriv dy (coordDeriv dy F) p)]
    ring
  simp only [metricConnectionAt,Matrix.cons_val_two,inducedCoordinateMetric_derivative hF]
  change ((realMetric F dy dy p *
      (coordDeriv dy (realMetric F dx dy) p - coordDeriv dx (realMetric F dy dy) p/2) -
      realMetric F dx dy p * (coordDeriv dy (realMetric F dy dy) p/2)) / _,
    (realMetric F dx dx p * (coordDeriv dy (realMetric F dy dy) p/2) -
      realMetric F dx dy p *
      (coordDeriv dy (realMetric F dx dy) p - coordDeriv dx (realMetric F dy dy) p/2)) / _) = _
  rw [ha,hb]
  rfl

lemma acceleration_connection_decomposition {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base) :
    let Gamma := metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) 2
    coordDeriv dy (coordDeriv dy F) p = Gamma.1 • coordDeriv dx F p +
      Gamma.2 • coordDeriv dy F p + realSecondForm F dy dy p := by
  dsimp only
  rw [induced_connection_yy hF p]
  unfold realSecondForm realNormalPart
  abel

lemma negative_acceleration_of_positive_hessian {F : RField 4}
    (hF : ContDiff ℝ ∞ F) (p : Base)
    (hpos : 0 < coordinateMetricHessian (inducedCoordinateMetric F) (Prod.fst : Base → ℝ) p dy dy) :
    ∃ μ ν : ℝ, μ < 0 ∧ coordDeriv dy (coordDeriv dy F) p =
      μ • coordDeriv dx F p + ν • coordDeriv dy F p + realSecondForm F dy dy p := by
  let Gamma := metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) 2
  refine ⟨Gamma.1,Gamma.2,?_,acceleration_connection_decomposition hF p⟩
  rw [coordinateMetricHessian_fst_dy] at hpos
  exact neg_pos.mp hpos

end ClosedSurfaceR4.RealModes

end

end OAI

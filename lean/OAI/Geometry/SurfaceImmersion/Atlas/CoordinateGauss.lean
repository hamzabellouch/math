import OAI.Geometry.SurfaceImmersion.Geometry.RealMetricDerivatives

namespace OAI

/-! The coordinate Gauss identity, proved from Euclidean derivatives and the
explicit normal projection.  Its right side depends only on the metric. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame

/-- Pairing of tangent covectors by the inverse first fundamental form. -/
def inverseMetricPair (E F G a b c d : ℝ) : ℝ :=
  (G*a*c-F*(a*d+b*c)+E*b*d)/(E*G-F^2)

lemma normalPart_dot_normalPart (X Y U V : RVec 4) (hD : gramDet X Y ≠ 0) :
    realNormalPart X Y U ⬝ᵥ realNormalPart X Y V = U ⬝ᵥ V-
      inverseMetricPair (X ⬝ᵥ X) (X ⬝ᵥ Y) (Y ⬝ᵥ Y)
        (X ⬝ᵥ U) (Y ⬝ᵥ U) (X ⬝ᵥ V) (Y ⬝ᵥ V) := by
  have hperp := realNormalPart_perp X Y U hD
  have hX : realNormalPart X Y U ⬝ᵥ X = 0 := (dotProduct_comm _ _).trans hperp.1
  have hY : realNormalPart X Y U ⬝ᵥ Y = 0 := (dotProduct_comm _ _).trans hperp.2
  have hcut : realNormalPart X Y U ⬝ᵥ realNormalPart X Y V =
      realNormalPart X Y U ⬝ᵥ V := by
    conv_lhs => arg 2; unfold realNormalPart
    simp only [dotProduct_sub,dotProduct_smul,hX,hY,smul_eq_mul,mul_zero,sub_zero]
  rw [hcut]
  simp only [realNormalPart,inverseMetricPair,NormalFrame.gramDet,sub_dotProduct,smul_dotProduct,
    smul_eq_mul]
  ring

/-- Gaussian curvature times the coordinate metric determinant. -/
def coordinateGauss (E F G : Base → ℝ) (p : Base) : ℝ :=
  (2*coordDeriv dx (coordDeriv dy F) p-
    coordDeriv dy (coordDeriv dy E) p-coordDeriv dx (coordDeriv dx G) p)/2-
  inverseMetricPair (E p) (F p) (G p)
    (coordDeriv dx E p/2) (coordDeriv dx F p-coordDeriv dy E p/2)
    (coordDeriv dy F p-coordDeriv dx G p/2) (coordDeriv dy G p/2)+
  inverseMetricPair (E p) (F p) (G p)
    (coordDeriv dy E p/2) (coordDeriv dx G p/2)
    (coordDeriv dy E p/2) (coordDeriv dx G p/2)

theorem gauss_metric_identity {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    realSecondForm F dx dx p ⬝ᵥ realSecondForm F dy dy p-
      realSecondForm F dx dy p ⬝ᵥ realSecondForm F dx dy p =
    coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p := by
  have hcomm : coordDeriv dy (coordDeriv dx F) = coordDeriv dx (coordDeriv dy F) :=
    funext fun q => real_second_coordDeriv_comm hF q dy dx
  unfold realSecondForm
  rw [normalPart_dot_normalPart _ _ _ _ hD,normalPart_dot_normalPart _ _ _ _ hD]
  unfold coordinateGauss
  rw [← raw_gauss_metric_identity hF p]
  simp only [realMetric_partial hF,hcomm,realMetric,inverseMetricPair,dotProduct_comm]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI

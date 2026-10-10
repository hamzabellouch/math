import Mathlib
import OAI.Geometry.PrescribedRicci.ChernLuGradient
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy
import OAI.Geometry.PrescribedRicci.ChernLuConnection
import OAI.Geometry.PrescribedRicci.GlobalKahlerEnergy
import OAI.Geometry.PrescribedRicci.KaehlerLogTrace

namespace OAI

/-! Chern Lu Differential. -/

section

 

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

def connectionEnergy (h g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : ℝ :=
  (∑ a, ∑ b, (h.matrix q z)⁻¹ a b *
    ((h.matrix q z)⁻¹*(h.connectionDifference g q z b)ᴴ*(g.matrix q z)⁻¹*h.connectionDifference g q z a).trace).re

def targetCurvatureTerm (h g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : ℝ :=
  (∑ a, ∑ b, (h.matrix q z)⁻¹ a b *
    ((h.matrix q z)⁻¹*g.curvatureMatrix q z b a).trace).re

def sourceRicciTerm (h g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : ℝ :=
  ((h.matrix q z)⁻¹*h.curvatureRicci q z*(h.matrix q z)⁻¹*g.matrix q z).trace.re

lemma laplacian_traceMetric (h g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    (h.laplacian (h.traceMetric g)).localExpression q z =
      -h.targetCurvatureTerm g q z + h.connectionEnergy g q z + h.sourceRicciTerm g q z := by
  have hl := h.laplacianValue_local (h.traceMetric g) q ((A.chart q).mapsTo_symm hz)
  change (h.laplacian (h.traceMetric g)).localExpression q z = _ at hl
  rw [(A.chart q).right_inv hz] at hl
  rw [hl]
  simp only [linearizedMongeAmpere,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  simp only [h.hessian_traceMetric g q hz,trace_neg,mul_add,mul_neg,
    Finset.sum_add_distrib,Finset.sum_neg_distrib,Complex.add_re,Complex.neg_re]
  change -h.targetCurvatureTerm g q z+h.connectionEnergy g q z+_ = _
  congr 1
  exact congrArg Complex.re (h.curvature_trace_contraction q hz (g.matrix q z))

lemma trace_gradient_bound (h g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    (h.energy (h.traceMetric g) (h.traceMetric g)).localExpression q z ≤
      (h.traceMetric g).localExpression q z * h.connectionEnergy g q z := by
  rw [h.energy_local (h.traceMetric g) (h.traceMetric g) q hz,h.traceMetric_local g q hz]
  unfold gradientPair connectionEnergy
  simp only [h.holRealDeriv_traceMetric g q hz]
  exact MongeAmpere.chernLu_gradient_bound _ _ (h.positive q z hz).inv.posSemidef
    (g.positive q z hz) (h.connectionDifference g q z)

lemma chernLu_pointwise (h g : KaehlerMetric A) (hd : 0 < d) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ((h.traceMetric g).localExpression q z)⁻¹ *
      (-h.targetCurvatureTerm g q z+h.sourceRicciTerm g q z) ≤
        (h.laplacian (h.logTrace g hd)).localExpression q z := by
  have hs : 0 < (h.traceMetric g).localExpression q z :=
    h.traceMetric_pos g hd ((A.chart q).symm z)
  have hg := h.trace_gradient_bound g q hz
  rw [h.laplacian_logTrace g hd q hz,h.laplacian_traceMetric g q hz]
  have hc := mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr (sq_nonneg ((h.traceMetric g).localExpression q z)))
  have he : (((h.traceMetric g).localExpression q z)^2)⁻¹ *
      ((h.traceMetric g).localExpression q z*h.connectionEnergy g q z) =
      ((h.traceMetric g).localExpression q z)⁻¹ * h.connectionEnergy g q z := by
    field_simp
  rw [he] at hc
  linarith

lemma chernLu_of_component_bounds (h g : KaehlerMetric A) (hd : 0 < d) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) {C R : ℝ}
    (hC : h.targetCurvatureTerm g q z ≤ C*((h.traceMetric g).localExpression q z)^2)
    (hR : -R*((h.traceMetric g).localExpression q z)^2 ≤ h.sourceRicciTerm g q z) :
    -(C+R)*(h.traceMetric g).localExpression q z ≤
      (h.laplacian (h.logTrace g hd)).localExpression q z := by
  have hs : 0 < (h.traceMetric g).localExpression q z :=
    h.traceMetric_pos g hd ((A.chart q).symm z)
  apply le_trans _ (h.chernLu_pointwise g hd q hz)
  have hh : -(C+R)*((h.traceMetric g).localExpression q z)^2 ≤
      -h.targetCurvatureTerm g q z+h.sourceRicciTerm g q z := by linarith
  have hm := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hs).le
  have he : ((h.traceMetric g).localExpression q z)⁻¹ *
      (-(C+R)*((h.traceMetric g).localExpression q z)^2) =
      -(C+R)*(h.traceMetric g).localExpression q z := by field_simp
  rwa [he] at hm

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI

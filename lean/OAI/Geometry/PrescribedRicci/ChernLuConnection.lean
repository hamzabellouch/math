import Mathlib
import OAI.Geometry.PrescribedRicci.CurvatureRicci
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy
import OAI.Geometry.PrescribedRicci.KaehlerTrace
import OAI.Geometry.PrescribedRicci.MatrixWirtingerExtra

namespace OAI

/-! Chern Lu Connection. -/

section

 

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_lu_W_identity (B G Pg Qg Ph Qh Rg Rh : Matrix n n ℂ)
    (hG : IsUnit G.det) :
    (-(B*Qh*B)*(Pg-G*B*Ph)+
      B*(Rg-(Qg*B*Ph-G*B*Qh*B*Ph+G*B*Rh))).trace =
    (-(B*(-Rg+Qg*G⁻¹*Pg))).trace +
      (B*(Qg-Qh*B*G)*G⁻¹*(Pg-G*B*Ph)).trace +
      (B*(-Rh+Qh*B*Ph)*B*G).trace := by
  have he : B*(Qg-Qh*B*G)*G⁻¹*(Pg-G*B*Ph) =
      B*Qg*G⁻¹*Pg-B*Qg*B*Ph-B*Qh*B*Pg+B*Qh*B*G*B*Ph := by
    simp only [mul_sub,sub_mul]
    simp only [mul_assoc,Matrix.mul_nonsing_inv_cancel_left G _ hG,
      Matrix.nonsing_inv_mul_cancel_left G _ hG]
    noncomm_ring
  rw [he]
  simp only [mul_add,add_mul,mul_sub,mul_neg,neg_mul,trace_add,trace_sub,trace_neg]
  have h1 : (B*G*B*Qh*B*Ph).trace = (B*Qh*B*Ph*B*G).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (B*G) (B*Qh*B*Ph)
  have h2 : (B*G*B*Rh).trace = (B*Rh*B*G).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (B*G) (B*Rh)
  simp only [mul_assoc] at h1 h2 ⊢
  linear_combination h1-h2

end MongeAmpere
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

def connectionDifference (h g : KaehlerMetric A) (q : Fin A.count)
    (z : Coordinates d) (a : Fin d) : Mat :=
  holDerivative (g.matrix q) z a - g.matrix q z*(h.matrix q z)⁻¹*holDerivative (h.matrix q) z a

lemma connectionDifference_smooth (h g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    ContDiffAt ℝ ∞ (fun y => h.connectionDifference g q y a) z := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hh := (h.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (h.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (h.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hh
  exact (contDiffAt_holDerivative hg a).sub
    (matrix_mul_contDiffAt (matrix_mul_contDiffAt hg hi) (contDiffAt_holDerivative hh a))

lemma connectionDifference_adjoint (h g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    (h.connectionDifference g q z a)ᴴ =
      barDerivative (g.matrix q) z a - barDerivative (h.matrix q) z a*(h.matrix q z)⁻¹*g.matrix q z := by
  unfold connectionDifference
  rw [conjTranspose_sub,conjTranspose_mul,conjTranspose_mul,
    g.holDerivative_adjoint q hz,h.holDerivative_adjoint q hz,
    (h.positive q z hz).inv.isHermitian.eq,(g.positive q z hz).isHermitian.eq]
  simp only [mul_assoc]

lemma holRealDeriv_traceMetric (h g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    holRealDeriv ((h.traceMetric g).localExpression q) z a =
      ((h.matrix q z)⁻¹*h.connectionDifference g q z a).trace := by
  have hs : ContDiffAt ℝ ∞ ((h.traceMetric g).localExpression q) z :=
    ((h.traceMetric g).smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hh := (h.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (h.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (h.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hh
  have he : (fun y => (((h.traceMetric g).localExpression q y):ℂ)) =ᶠ[nhds z]
      (fun y => ((h.matrix q y)⁻¹*g.matrix q y).trace) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    rw [h.traceMetric_local g q hy]
    exact MongeAmpere.trace_mul_real (h.positive q y hy).inv.isHermitian (g.positive q y hy).isHermitian
  rw [← holDeriv_ofReal (hs.differentiableAt (by simp)),holDeriv_congr he,
    holDeriv_trace (matrix_mul_differentiableAt (hi.differentiableAt (by simp)) (hg.differentiableAt (by simp))),
    holDerivative_mul (hi.differentiableAt (by simp)) (hg.differentiableAt (by simp)),
    holDerivative_inv (hh.differentiableAt (by simp)) (isUnit_iff_ne_zero.mpr (h.positive q z hz).det_pos.ne')]
  simp only [connectionDifference,neg_mul,mul_sub,trace_add,trace_sub,trace_neg]
  have hc : ((h.matrix q z)⁻¹*holDerivative (h.matrix q) z a*(h.matrix q z)⁻¹*g.matrix q z).trace =
      ((h.matrix q z)⁻¹*g.matrix q z*(h.matrix q z)⁻¹*holDerivative (h.matrix q) z a).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm
      ((h.matrix q z)⁻¹*holDerivative (h.matrix q) z a) ((h.matrix q z)⁻¹*g.matrix q z)
  simp only [mul_assoc] at hc ⊢
  linear_combination -hc

lemma barDerivative_connectionDifference (h g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (b a : Fin d) :
    barDerivative (fun y => h.connectionDifference g q y a) z b =
      barDerivative (fun y => holDerivative (g.matrix q) y a) z b -
        (barDerivative (g.matrix q) z b*(h.matrix q z)⁻¹*holDerivative (h.matrix q) z a -
          g.matrix q z*(h.matrix q z)⁻¹*barDerivative (h.matrix q) z b*(h.matrix q z)⁻¹*holDerivative (h.matrix q) z a +
          g.matrix q z*(h.matrix q z)⁻¹*barDerivative (fun y => holDerivative (h.matrix q) y a) z b) := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hh := (h.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (h.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (h.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hh
  have pd := (contDiffAt_holDerivative hh a).differentiableAt (by simp)
  have gd := hg.differentiableAt (by simp)
  have id := hi.differentiableAt (by simp)
  unfold connectionDifference
  rw [barDerivative_sub ((contDiffAt_holDerivative hg a).differentiableAt (by simp))
      (matrix_mul_differentiableAt (matrix_mul_differentiableAt gd id) pd),
    barDerivative_mul (matrix_mul_differentiableAt gd id) pd,
    barDerivative_mul gd id,
    barDerivative_inv (hh.differentiableAt (by simp)) (isUnit_iff_ne_zero.mpr (h.positive q z hz).det_pos.ne')]
  simp only [mul_neg,neg_mul,add_mul,mul_assoc,sub_eq_add_neg]

lemma hessian_traceMetric (h g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (b a : Fin d) :
    (h.traceMetric g).hessian q z b a =
      (-((h.matrix q z)⁻¹*g.curvatureMatrix q z b a)).trace +
        ((h.matrix q z)⁻¹*(h.connectionDifference g q z b)ᴴ*(g.matrix q z)⁻¹*h.connectionDifference g q z a).trace +
        ((h.matrix q z)⁻¹*h.curvatureMatrix q z b a*(h.matrix q z)⁻¹*g.matrix q z).trace := by
  have hh := (h.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (h.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (h.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hh
  have hw := (h.connectionDifference_smooth g q hz a).differentiableAt (by simp)
  have he : (fun y => holRealDeriv ((h.traceMetric g).localExpression q) y a) =ᶠ[nhds z]
      (fun y => ((h.matrix q y)⁻¹*h.connectionDifference g q y a).trace) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact h.holRealDeriv_traceMetric g q hy a
  have hs : ContDiffAt ℝ ∞ ((h.traceMetric g).localExpression q) z :=
    ((h.traceMetric g).smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  change PotentialKaehler.potentialMatrix ((h.traceMetric g).localExpression q) z b a = _
  rw [← barDeriv_holRealDeriv hs,
    barDeriv_congr he,barDeriv_trace (matrix_mul_differentiableAt (hi.differentiableAt (by simp)) hw),
    barDerivative_mul (hi.differentiableAt (by simp)) hw,
    barDerivative_inv (hh.differentiableAt (by simp)) (isUnit_iff_ne_zero.mpr (h.positive q z hz).det_pos.ne'),
    h.barDerivative_connectionDifference g q hz,h.connectionDifference_adjoint g q hz]
  exact MongeAmpere.trace_lu_W_identity _ _ _ _ _ _ _ _
    (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne')

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI

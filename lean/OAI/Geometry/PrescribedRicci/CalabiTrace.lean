import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiTensorAlgebra
import OAI.Geometry.PrescribedRicci.CalabiTensorMetric
import OAI.Geometry.PrescribedRicci.ChernConnection
import OAI.Geometry.PrescribedRicci.HermitianTensorEnergy
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy

namespace OAI

/-! Calabi Trace. -/

noncomputable section
open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff MatrixOrder Kronecker Matrix.Norms.Elementwise
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma hermPair_kronecker_one_trace (H U V : Matrix n n ℂ) :
    hermPair (H ⊗ₖ (1 : Matrix n n ℂ)) (fun p => U p.1 p.2) (fun p => V p.1 p.2) =
      (Uᴴ*H*V).trace := by
  classical
  simp only [hermPair_expand,Fintype.sum_prod_type,Matrix.kronecker_apply,Matrix.one_apply,
    mul_ite,ite_mul,mul_one,mul_zero,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

omit [DecidableEq n] in
lemma trace_real {H : Matrix n n ℂ} (hH : H.IsHermitian) : (H.trace.re : ℂ) = H.trace := by
  have he : star H.trace = H.trace := by rw [← trace_conjTranspose,hH.eq]
  have hi := congrArg Complex.im he
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    simp only [Complex.star_def,Complex.conj_im] at hi
    linarith
end MongeAmpere
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "TI" => TensorIndex (Fin d)

def flatTrace (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : ℝ :=
  (g.matrix q z).trace.re

lemma flatTrace_smooth (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) : ContDiffAt ℝ ∞ (g.flatTrace q) z := by
  have hs := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  exact Complex.reCLM.contDiff.contDiffAt.comp z (ContDiffAt.sum (fun i _ =>
    contDiffAt_pi.mp (contDiffAt_pi.mp hs i) i))

lemma flatTrace_hol (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    holRealDeriv (g.flatTrace q) z a = (holDerivative (g.matrix q) z a).trace := by
  rw [← holDeriv_ofReal ((g.flatTrace_smooth q hz).differentiableAt (by simp))]
  have he : (fun y => (g.flatTrace q y : ℂ)) =ᶠ[nhds z] fun y => (g.matrix q y).trace := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact trace_real (g.positive q y hy).isHermitian
  rw [holDeriv_congr he,holDeriv_trace
    (((g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)).differentiableAt (by simp))]

lemma flatTrace_hessian (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (b a : Fin d) :
    PotentialKaehler.potentialMatrix (g.flatTrace q) z b a =
      ((g.chernConnection q z b)ᴴ*g.matrix q z*g.chernConnection q z a).trace-
        (g.curvatureMatrix q z b a).trace := by
  rw [← barDeriv_holRealDeriv (g.flatTrace_smooth q hz)]
  have he : (fun y => holRealDeriv (g.flatTrace q) y a) =ᶠ[nhds z]
      fun y => (holDerivative (g.matrix q) y a).trace := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact g.flatTrace_hol q hy a
  rw [barDeriv_congr he,barDeriv_trace ((contDiffAt_holDerivative
    ((g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)) a).differentiableAt (by simp))]
  have hp : (g.chernConnection q z b)ᴴ*g.matrix q z*g.chernConnection q z a =
      barDerivative (g.matrix q) z b*(g.matrix q z)⁻¹*holDerivative (g.matrix q) z a := by
    simp only [chernConnection,Matrix.conjTranspose_mul,g.holDerivative_adjoint q hz,
      (g.positive q z hz).inv.isHermitian.eq]
    rw [mul_assoc,Matrix.mul_nonsing_inv_cancel_left _ _
      (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne')]
  rw [hp]
  simp only [curvatureMatrix,trace_add,trace_neg]
  abel

lemma flatTrace_laplacian (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ((g.matrix q z)⁻¹*PotentialKaehler.potentialMatrix (g.flatTrace q) z).trace.re =
      (hermPair (tensor3 (g.matrix q z)⁻¹.transpose (g.matrix q z) 1)
        (g.calabiTensor q z) (g.calabiTensor q z)).re-(g.curvatureRicci q z).trace.re := by
  have he : ((g.matrix q z)⁻¹*PotentialKaehler.potentialMatrix (g.flatTrace q) z).trace =
      hermPair (tensor3 (g.matrix q z)⁻¹.transpose (g.matrix q z) 1)
        (g.calabiTensor q z) (g.calabiTensor q z)-(g.curvatureRicci q z).trace := by
    change (∑ u, ∑ b, (g.matrix q z)⁻¹ u b*PotentialKaehler.potentialMatrix (g.flatTrace q) z b u) = _
    simp_rw [g.flatTrace_hessian q hz]
    simp only [mul_sub,Finset.sum_sub_distrib]
    congr 1
    · have ht := tensorEnergy_eq (g.matrix q z)⁻¹.transpose
        ((g.matrix q z) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))
        (fun a (p : Fin d × Fin d) => g.chernConnection q z a p.1 p.2)
      change _ = hermPair (tensor3 (g.matrix q z)⁻¹.transpose (g.matrix q z) 1)
        (g.calabiTensor q z) (g.calabiTensor q z) at ht
      rw [← ht,← tensorEnergy_flip]
      simp only [hermPair_kronecker_one_trace]
    · have hh := congrArg Matrix.trace (g.curvature_contraction q hz)
      simp only [trace_sum,trace_smul,smul_eq_mul] at hh
      exact hh
  exact congrArg Complex.re he

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI

import Mathlib
import OAI.Geometry.PrescribedRicci.ChernConnection

namespace OAI

/-! Chern Bianchi. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

lemma holDerivative_neg (f : Coordinates d → Mat) (z : Coordinates d) (a : Fin d) :
    holDerivative (fun y => -f y) z a = -holDerivative f z a := by
  unfold holDerivative
  have he : fderiv ℝ (fun y => -f y) z = -fderiv ℝ f z := by
    exact fderiv_fun_neg
  rw [he]
  ext i j
  simp only [_root_.neg_apply,Matrix.smul_apply,Matrix.sub_apply,Matrix.neg_apply,smul_eq_mul]
  ring

variable {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma chernCurvature_smooth (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (b a : Fin d) :
    ContDiffAt ℝ ∞ (fun y => g.chernCurvature q y b a) z := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (g.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hg
  unfold chernCurvature curvatureMatrix
  exact matrix_mul_contDiffAt hi
    ((contDiffAt_barDerivative (contDiffAt_holDerivative hg a) b).neg.add
      (matrix_mul_contDiffAt (matrix_mul_contDiffAt (contDiffAt_barDerivative hg b) hi)
        (contDiffAt_holDerivative hg a)))

lemma chernConnection_hol_bar (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (b a u : Fin d) :
    holDerivative (fun y => barDerivative (fun w => g.chernConnection q w a) y b) z u =
      -holDerivative (fun y => g.chernCurvature q y b a) z u := by
  have he : (fun y => barDerivative (fun w => g.chernConnection q w a) y b) =ᶠ[nhds z]
      (fun y => -g.chernCurvature q y b a) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact g.chernConnection_bar q hy a b
  rw [holDerivative_congr he,holDerivative_neg]

lemma chern_bianchi (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (b a u : Fin d) :
    holDerivative (fun y => g.chernCurvature q y b a) z u +
      g.chernConnection q z u*g.chernCurvature q z b a -
      g.chernCurvature q z b a*g.chernConnection q z u =
    holDerivative (fun y => g.chernCurvature q y b u) z a +
      g.chernConnection q z a*g.chernCurvature q z b u -
      g.chernCurvature q z b u*g.chernConnection q z a := by
  have hc (v : Fin d) := g.chernConnection_smooth q hz v
  have he : (fun y => holDerivative (fun w => g.chernConnection q w a) y u-
      holDerivative (fun w => g.chernConnection q w u) y a) =ᶠ[nhds z]
      (fun y => g.chernConnection q y a*g.chernConnection q y u-
        g.chernConnection q y u*g.chernConnection q y a) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact g.chernConnection_maurerCartan q hy a u
  have hb := barDerivative_congr he b
  rw [barDerivative_sub ((contDiffAt_holDerivative (hc a) u).differentiableAt (by simp))
      ((contDiffAt_holDerivative (hc u) a).differentiableAt (by simp)),
    bar_hol_comm (hc a),bar_hol_comm (hc u),g.chernConnection_hol_bar q hz,
    g.chernConnection_hol_bar q hz] at hb
  rw [barDerivative_sub (matrix_mul_differentiableAt ((hc a).differentiableAt (by simp))
      ((hc u).differentiableAt (by simp)))
      (matrix_mul_differentiableAt ((hc u).differentiableAt (by simp))
      ((hc a).differentiableAt (by simp))),
    barDerivative_mul ((hc a).differentiableAt (by simp)) ((hc u).differentiableAt (by simp)),
    barDerivative_mul ((hc u).differentiableAt (by simp)) ((hc a).differentiableAt (by simp)),
    g.chernConnection_bar q hz,g.chernConnection_bar q hz] at hb
  simp only [neg_mul,mul_neg] at hb
  have hh := congrArg (fun M : Mat => M+
    (holDerivative (fun y => g.chernCurvature q y b a) z u+
      g.chernConnection q z a*g.chernCurvature q z b u-
      g.chernCurvature q z b u*g.chernConnection q z a)) hb
  convert hh.symm using 1 <;> abel

lemma chernCurvature_contraction (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ∑ u, ∑ b, ((g.matrix q z)⁻¹ u b) • g.chernCurvature q z b u =
      (g.matrix q z)⁻¹*g.curvatureRicci q z := by
  rw [← g.curvature_contraction q hz]
  simp only [chernCurvature,Matrix.mul_sum,Matrix.mul_smul]

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI

import Mathlib
import OAI.Geometry.PrescribedRicci.ArrayWirtinger
import OAI.Geometry.PrescribedRicci.ChernConnection

namespace OAI

/-! Calabi Tensor Metric. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Kronecker Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ
local notation "TI" => TensorIndex (Fin d)

def calabiTensor (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : TI → ℂ :=
  fun v => g.chernConnection q z v.1 v.2.1 v.2.2

def calabiMetric (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : Matrix TI TI ℂ :=
  tensorMetric (g.matrix q z)

def calabiConnection (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d)
    (a : Fin d) : Matrix TI TI ℂ := tensorConnection (g.chernConnection q z a)

def calabiNorm (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : ℝ :=
  (hermPair (g.calabiMetric q z) (g.calabiTensor q z) (g.calabiTensor q z)).re

lemma calabiTensor_smooth (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (i : TI) :
    ContDiffAt ℝ ∞ (fun y => g.calabiTensor q y i) z :=
  contDiffAt_pi.mp (contDiffAt_pi.mp (g.chernConnection_smooth q hz i.1) i.2.1) i.2.2

lemma calabiMetric_posDef (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) : (g.calabiMetric q z).PosDef :=
  tensorMetric_posDef (g.positive q z hz)

lemma calabiNorm_nonneg (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) : 0 ≤ g.calabiNorm q z :=
  hermPair_nonneg (g.calabiMetric_posDef q hz).posSemidef _

lemma calabiMetric_smooth (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (i j : TI) :
    ContDiffAt ℝ ∞ (fun y => g.calabiMetric q y i j) z := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (g.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hg
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hi j.1) i.1).mul
    ((contDiffAt_pi.mp (contDiffAt_pi.mp hg i.2.1) j.2.1).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hi j.2.2) i.2.2))

lemma calabiConnection_smooth (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) (i j : TI) :
    ContDiffAt ℝ ∞ (fun y => g.calabiConnection q y a i j) z := by
  have hc (u v : Fin d) : ContDiffAt ℝ ∞ (fun y => g.chernConnection q y a u v) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (g.chernConnection_smooth q hz a) u) v
  exact (((hc j.1 i.1).neg.mul (contDiffAt_const.mul contDiffAt_const)).add
    (contDiffAt_const.mul ((hc i.2.1 j.2.1).mul contDiffAt_const))).add
    (contDiffAt_const.mul (contDiffAt_const.mul (hc j.2.2 i.2.2).neg))

lemma calabiNorm_smooth (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ContDiffAt ℝ ∞ (g.calabiNorm q) z :=
  Complex.reCLM.contDiff.contDiffAt.comp z
    (hermPair_smooth (g.calabiMetric_smooth q hz) (g.calabiTensor_smooth q hz) (g.calabiTensor_smooth q hz))

lemma metric_hol_connection (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    holArray (g.matrix q) z a = g.matrix q z*g.chernConnection q z a := by
  rw [holArray_eq_holDerivative
    (((g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)).differentiableAt (by simp))]
  rw [chernConnection,← mul_assoc,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne'),one_mul]

lemma inverse_metric_hol_connection (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    holArray (fun y => (g.matrix q y)⁻¹.transpose) z a =
      (g.matrix q z)⁻¹.transpose*(-(g.chernConnection q z a).transpose) := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (g.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hg
  rw [holArray_transpose,holArray_eq_holDerivative (hi.differentiableAt (by simp)),
    holDerivative_inv (hg.differentiableAt (by simp))
      (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne')]
  simp only [chernConnection,Matrix.transpose_neg,Matrix.transpose_mul,mul_neg,mul_assoc]

lemma calabiMetric_hol (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    holArray (g.calabiMetric q) z a = g.calabiMetric q z*g.calabiConnection q z a := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (g.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hg
  have hg' (i j : Fin d) : DifferentiableAt ℝ (fun y => g.matrix q y i j) z :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j).differentiableAt (by simp)
  have hi' (i j : Fin d) : DifferentiableAt ℝ (fun y => (g.matrix q y)⁻¹.transpose i j) z :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hi j) i).differentiableAt (by simp)
  change holArray (fun y => tensor3 (g.matrix q y)⁻¹.transpose (g.matrix q y)
    (g.matrix q y)⁻¹.transpose) z a = _
  rw [holArray_tensor3 hi' hg' hi',g.metric_hol_connection q hz,
    g.inverse_metric_hol_connection q hz]
  exact (tensorMetric_mul_connection _ _).symm

lemma calabiMetric_bar (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    barArray (g.calabiMetric q) z a = (g.calabiConnection q z a)ᴴ*g.calabiMetric q z := by
  have hh : ∀ᶠ y in nhds z, (g.calabiMetric q y).IsHermitian := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact (g.calabiMetric_posDef q hy).isHermitian
  rw [barArray_eq_adjoint_hol hh,g.calabiMetric_hol q hz,Matrix.conjTranspose_mul,
    (g.calabiMetric_posDef q hz).isHermitian.eq]

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI

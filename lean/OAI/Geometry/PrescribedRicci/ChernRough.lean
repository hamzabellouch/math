import Mathlib
import OAI.Geometry.PrescribedRicci.ChernConnection
import OAI.Geometry.PrescribedRicci.ChernBianchi
import OAI.Geometry.PrescribedRicci.CurvatureCompactBounds
import OAI.Geometry.PrescribedRicci.WirtingerScalar

namespace OAI

/-! Chern Rough. -/

section

 
noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

lemma holDerivative_sum_smul {ι : Type*} [Fintype ι]
    {f : ι → Coordinates d → ℂ} {M : ι → Coordinates d → Mat} {z : Coordinates d}
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) (hM : ∀ i, DifferentiableAt ℝ (M i) z)
    (a : Fin d) :
    holDerivative (fun y => ∑ i, f i y • M i y) z a =
      ∑ i, (holDeriv (f i) z a • M i z + f i z • holDerivative (M i) z a) := by
  have hm (i : ι) (k j : Fin d) := (differentiableAt_pi.mp (differentiableAt_pi.mp (hM i) k) j)
  have ht (i : ι) : DifferentiableAt ℝ (fun y => f i y • M i y) z := (hf i).smul (hM i)
  have hs : DifferentiableAt ℝ (fun y => ∑ i, f i y • M i y) z :=
    DifferentiableAt.fun_sum (u:=Finset.univ) (fun i _ => ht i)
  ext k j
  rw [← holDeriv_entry hs]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rw [holDeriv_sum (fun i => (hf i).fun_mul (hm i k j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [holDeriv_mul (hf i) (hm i k j),holDeriv_entry (hM i)]
  rfl

variable {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma inverse_derivative_curvature_correction (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    ∑ u, ∑ b, holDerivative (fun y => (g.matrix q y)⁻¹) z a u b • g.chernCurvature q z b u =
      -(∑ u, ∑ b, ((g.matrix q z)⁻¹ u b) •
          (∑ v, (g.chernConnection q z u v a) • g.chernCurvature q z b v)) := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  rw [holDerivative_inv (hg.differentiableAt (by simp))
    (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne')]
  change ∑ u, ∑ b, (-(g.chernConnection q z a*(g.matrix q z)⁻¹)) u b •
    g.chernCurvature q z b u = _
  simp only [Matrix.neg_apply,Matrix.mul_apply,neg_smul,Finset.sum_neg_distrib,
    Finset.sum_smul,Finset.smul_sum,smul_smul]
  congr 1
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext b
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro v _
  rw [g.chernConnection_torsion q hz a v u]
  congr 1
  ring

lemma chernCurvature_rough (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    ∑ u, ∑ b, ((g.matrix q z)⁻¹ u b) •
      (holDerivative (fun y => g.chernCurvature q y b a) z u +
        g.chernConnection q z u*g.chernCurvature q z b a-
        g.chernCurvature q z b a*g.chernConnection q z u-
        ∑ v, g.chernConnection q z u v a • g.chernCurvature q z b v) =
      (g.matrix q z)⁻¹*holDerivative (g.curvatureRicci q) z a-
        ((g.matrix q z)⁻¹*g.curvatureRicci q z)*g.chernConnection q z a := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (g.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hg
  have hI (u b : Fin d) : DifferentiableAt ℝ (fun y => (g.matrix q y)⁻¹ u b) z :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hi u) b).differentiableAt (by simp)
  have hR (b u : Fin d) := (g.chernCurvature_smooth q hz b u).differentiableAt (by simp)
  have hr := (g.curvatureRicci_smooth q hz).differentiableAt (by simp)
  have he : (fun y => ∑ ub : Fin d × Fin d,
      (g.matrix q y)⁻¹ ub.1 ub.2 • g.chernCurvature q y ub.2 ub.1) =ᶠ[nhds z]
        (fun y => (g.matrix q y)⁻¹*g.curvatureRicci q y) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    simpa only [Fintype.sum_prod_type] using g.chernCurvature_contraction q hy
  have hd := holDerivative_congr he a
  have hdL := holDerivative_sum_smul
    (f:=fun ub : Fin d × Fin d => fun y => (g.matrix q y)⁻¹ ub.1 ub.2)
    (M:=fun ub : Fin d × Fin d => fun y => g.chernCurvature q y ub.2 ub.1)
    (fun ub => hI ub.1 ub.2) (fun ub => hR ub.2 ub.1) a
  rw [hdL] at hd
  have hdR := holDerivative_mul (f:=fun y => (g.matrix q y)⁻¹)
    (g:=g.curvatureRicci q) (hi.differentiableAt (by simp)) hr a
  rw [hdR] at hd
  have hdi := holDerivative_inv (hg.differentiableAt (by simp))
    (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne') a
  rw [hdi] at hd
  simp only [Fintype.sum_prod_type,Finset.sum_add_distrib] at hd
  simp_rw [holDeriv_entry (hi.differentiableAt (by simp))] at hd
  rw [g.inverse_derivative_curvature_correction q hz] at hd
  simp only [neg_mul,mul_assoc] at hd
  rw [← mul_assoc (g.matrix q z)⁻¹ (holDerivative (g.matrix q) z a)
    ((g.matrix q z)⁻¹*g.curvatureRicci q z)] at hd
  change -(∑ u, ∑ b, ((g.matrix q z)⁻¹ u b) •
      (∑ v, g.chernConnection q z u v a • g.chernCurvature q z b v)) +
      (∑ u, ∑ b, ((g.matrix q z)⁻¹ u b) •
        holDerivative (fun y => g.chernCurvature q y b u) z a) =
      -(g.chernConnection q z a*((g.matrix q z)⁻¹*g.curvatureRicci q z))+
        (g.matrix q z)⁻¹*holDerivative (g.curvatureRicci q) z a at hd
  conv_lhs =>
    arg 2
    ext u
    arg 2
    ext b
    rw [g.chern_bianchi q hz]
  have hleft : (∑ u, ∑ b, ((g.matrix q z)⁻¹ u b) •
      (g.chernConnection q z a*g.chernCurvature q z b u)) =
        g.chernConnection q z a*((g.matrix q z)⁻¹*g.curvatureRicci q z) := by
    rw [← g.chernCurvature_contraction q hz]
    simp only [Matrix.mul_sum,Matrix.mul_smul]
  have hright : (∑ u, ∑ b, ((g.matrix q z)⁻¹ u b) •
      (g.chernCurvature q z b u*g.chernConnection q z a)) =
        ((g.matrix q z)⁻¹*g.curvatureRicci q z)*g.chernConnection q z a := by
    rw [← g.chernCurvature_contraction q hz]
    simp only [Matrix.sum_mul,Matrix.smul_mul]
  simp only [smul_sub,smul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,hleft,hright]
  have hh := congrArg (fun M : Mat => M+
    g.chernConnection q z a*((g.matrix q z)⁻¹*g.curvatureRicci q z)-
      ((g.matrix q z)⁻¹*g.curvatureRicci q z)*g.chernConnection q z a) hd
  convert hh using 1 <;> abel

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI

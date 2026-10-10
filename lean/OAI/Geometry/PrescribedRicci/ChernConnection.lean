import Mathlib
import OAI.Geometry.PrescribedRicci.ChernLuAlgebra
import OAI.Geometry.PrescribedRicci.MatrixWirtingerExtra
import OAI.Geometry.PrescribedRicci.MatrixWirtingerSecond

namespace OAI

/-! Chern Connection. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

lemma holDerivative_congr {f g : Coordinates d → Mat} {z : Coordinates d}
    (he : f =ᶠ[nhds z] g) (a : Fin d) : holDerivative f z a = holDerivative g z a := by
  unfold holDerivative
  rw [he.fderiv_eq]

lemma holDerivative_sub {f g : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : Fin d) :
    holDerivative (fun y => f y-g y) z a = holDerivative f z a-holDerivative g z a := by
  unfold holDerivative
  have he : fderiv ℝ (fun y => f y-g y) z = fderiv ℝ f z-fderiv ℝ g z := by
    convert! (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv using 1
  rw [he]
  simp only [_root_.sub_apply,smul_sub]
  abel

lemma hol_hol_comm {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a b : Fin d) :
    holDerivative (fun y => holDerivative f y a) z b =
      holDerivative (fun y => holDerivative f y b) z a := by
  change (2:ℂ)⁻¹ • (fderiv ℝ (fun y => holDerivative f y a) z (coordinateVector b) -
    Complex.I • fderiv ℝ (fun y => holDerivative f y a) z (Complex.I • coordinateVector b)) =
    (2:ℂ)⁻¹ • (fderiv ℝ (fun y => holDerivative f y b) z (coordinateVector a) -
    Complex.I • fderiv ℝ (fun y => holDerivative f y b) z (Complex.I • coordinateVector a))
  rw [fderiv_holDerivative hf,fderiv_holDerivative hf,
    fderiv_holDerivative hf,fderiv_holDerivative hf]
  have hs (u v : Coordinates d) : fderiv ℝ (fderiv ℝ f) z u v = fderiv ℝ (fderiv ℝ f) z v u := by
    exact hf.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      change ((2:ℕ∞):WithTop ℕ∞) ≤ ((⊤:ℕ∞):WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top) u v
  rw [hs (coordinateVector a) (coordinateVector b),
    hs (coordinateVector a) (Complex.I • coordinateVector b),
    hs (Complex.I • coordinateVector a) (coordinateVector b),
    hs (Complex.I • coordinateVector a) (Complex.I • coordinateVector b)]
  ext i j
  simp only [Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

variable {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

def chernConnection (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) (a : Fin d) : Mat :=
  (g.matrix q z)⁻¹*holDerivative (g.matrix q) z a

def chernCurvature (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d)
    (b a : Fin d) : Mat := (g.matrix q z)⁻¹*g.curvatureMatrix q z b a

lemma chernConnection_smooth (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    ContDiffAt ℝ ∞ (fun y => g.chernConnection q y a) z := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  exact matrix_mul_contDiffAt
    (((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hg)
    (contDiffAt_holDerivative hg a)

lemma chernConnection_torsion (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a k j : Fin d) :
    g.chernConnection q z a k j = g.chernConnection q z j k a := by
  simp only [chernConnection,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro u _
  rw [g.holDerivative_symm q hz a u j]

lemma chernConnection_bar (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a b : Fin d) :
    barDerivative (fun y => g.chernConnection q y a) z b = -g.chernCurvature q z b a := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (g.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hg
  unfold chernConnection
  rw [barDerivative_mul (hi.differentiableAt (by simp))
    ((contDiffAt_holDerivative hg a).differentiableAt (by simp)),
    barDerivative_inv (hg.differentiableAt (by simp)) (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne')]
  simp only [chernCurvature,curvatureMatrix,mul_add,neg_mul,mul_neg,mul_assoc]
  abel

lemma chernConnection_hol (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a u : Fin d) :
    holDerivative (fun y => g.chernConnection q y a) z u =
      -(g.chernConnection q z u*g.chernConnection q z a)+
        (g.matrix q z)⁻¹*holDerivative (fun y => holDerivative (g.matrix q) y a) z u := by
  have hg := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (g.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hg
  unfold chernConnection
  rw [holDerivative_mul (hi.differentiableAt (by simp))
    ((contDiffAt_holDerivative hg a).differentiableAt (by simp)),
    holDerivative_inv (hg.differentiableAt (by simp)) (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne')]
  simp only [neg_mul,mul_assoc]

lemma chernConnection_maurerCartan (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a u : Fin d) :
    holDerivative (fun y => g.chernConnection q y a) z u -
      holDerivative (fun y => g.chernConnection q y u) z a =
      g.chernConnection q z a*g.chernConnection q z u-
        g.chernConnection q z u*g.chernConnection q z a := by
  rw [g.chernConnection_hol q hz,g.chernConnection_hol q hz,
    hol_hol_comm ((g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)) a u]
  abel

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI

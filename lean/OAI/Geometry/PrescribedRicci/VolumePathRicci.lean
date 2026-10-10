import Mathlib
import OAI.Geometry.PrescribedRicci.CurvatureRicci
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Volume Path Ricci. -/

section

 
noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace PotentialKaehler
variable {d : ℕ}

lemma potentialMatrix_add_const (f : V d → ℝ) (z : V d) (c : ℝ) :
    potentialMatrix (fun y => f y+c) z = potentialMatrix f z := by
  unfold potentialMatrix
  have he : fderiv ℝ (fun y => f y+c) = fderiv ℝ f := by
    funext y
    exact fderiv_add_const c
  rw [he]

lemma potentialMatrix_affine {f g : V d → ℝ} {z : V d}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (t c : ℝ) :
    potentialMatrix (fun y => f y+t*g y+c) z =
      potentialMatrix f z + (t:ℂ) • potentialMatrix g z := by
  rw [potentialMatrix_add_const]
  change hermitianPartMatrix (fderiv ℝ (fderiv ℝ (f+t • g)) z) = _
  have ht : ContDiffAt ℝ ∞ (t • g) z := hg.const_smul t
  rw [EllipticKernel.hessian_add hf ht,
    fderiv_const_smul_field (𝕜:=ℝ) (f:=g) t,
    fderiv_const_smul_field (𝕜:=ℝ) (f:=fderiv ℝ g) t,
    EllipticKernel.hermitianPartMatrix_add]
  congr 1
  ext a b
  simp only [hermitianPartMatrix_apply,Matrix.smul_apply]
  apply Complex.ext <;>
    simp [potentialMatrix,hermitianPartMatrix_apply,hermitianPart,Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im] <;> ring

end PotentialKaehler
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma ricciPotential_contDiffAt (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ContDiffAt ℝ ∞ (g.ricciPotential q) z :=
  (((g.volumeCoefficient_smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)).log
    (g.volumeCoefficient_pos q hz).ne').neg

lemma volumePath_ricci (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (hp : g.PositivePotential φ)
    (heq : ∀ x, (g.logRatio (g.deform φ hp)).value x =
      t*(prescribedForcing g line).value x+b)
    (q : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    (g.deform φ hp).curvatureRicci q z =
      g.curvatureRicci q z - (t:ℂ) • (prescribedForcing g line).hessian q z := by
  have he : (g.deform φ hp).ricciPotential q =ᶠ[nhds z]
      (fun y => g.ricciPotential q y+(-t)*(prescribedForcing g line).localExpression q y+(-b)) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    have hh := heq ((A.chart q).symm y)
    change (g.logRatio (g.deform φ hp)).localExpression q y =
      t*(prescribedForcing g line).localExpression q y+b at hh
    rw [g.logRatio_local _ q hy] at hh
    unfold ricciPotential
    linarith
  rw [(g.deform φ hp).curvatureRicci_eq q hz,
    PotentialKaehler.potentialMatrix_congr he,
    PotentialKaehler.potentialMatrix_affine (g.ricciPotential_contDiffAt q hz)
      (show ContDiffAt ℝ ∞ ((prescribedForcing g line).localExpression q) z from
        ((prescribedForcing g line).smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)),
    g.curvatureRicci_eq q hz]
  simp only [Complex.ofReal_neg,neg_smul,sub_eq_add_neg]
  rfl

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI

import Mathlib
import OAI.Geometry.PrescribedRicci.LocalKahlerEnergy

namespace OAI

/-! Matrix Wirtinger Extra. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

lemma matrix_mul_differentiableAt {f g : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    DifferentiableAt ℝ (fun y => f y*g y) z :=
  (MongeAmpere.matrixMulCLM.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).differentiableAt

lemma matrix_mul_contDiffAt {f g : Coordinates d → Mat} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) :
    ContDiffAt ℝ ∞ (fun y => f y*g y) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiffAt.sum
  intro k _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hf i) k).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hg k) j)

lemma barDerivative_congr {f g : Coordinates d → Mat} {z : Coordinates d}
    (he : f =ᶠ[nhds z] g) (a : Fin d) : barDerivative f z a = barDerivative g z a := by
  unfold barDerivative
  rw [he.fderiv_eq]

lemma barDerivative_sub {f g : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : Fin d) :
    barDerivative (fun y => f y-g y) z a = barDerivative f z a - barDerivative g z a := by
  unfold barDerivative
  have he : fderiv ℝ (fun y => f y-g y) z = fderiv ℝ f z - fderiv ℝ g z := by
    convert! (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv using 1
  rw [he]
  simp only [_root_.sub_apply,smul_sub,smul_add]
  abel

lemma holDeriv_congr {f g : Coordinates d → ℂ} {z : Coordinates d}
    (he : f =ᶠ[nhds z] g) (a : Fin d) : holDeriv f z a = holDeriv g z a := by
  unfold holDeriv
  rw [he.fderiv_eq]

lemma holDeriv_ofReal {φ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : DifferentiableAt ℝ φ z) (a : Fin d) :
    holDeriv (fun y => (φ y:ℂ)) z a = holRealDeriv φ z a := by
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp z hφ.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (φ y:ℂ)) z = _ at hd
  unfold holDeriv holRealDeriv holRealForm
  rw [hd]
  rfl

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI

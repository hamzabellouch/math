import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives

namespace OAI

/-! Quadratic Contact. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped InnerProductSpace ContDiff
namespace PotentialABP
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_sub_sq_hessian (c x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => ‖y-c‖^2)) x v w = 2 * inner ℝ v w := by
  have he : fderiv ℝ (fun y : E => ‖y-c‖^2) = fun y => (2:ℝ) • innerSL ℝ (y-c) := by
    funext y
    simpa [two_smul] using (((hasFDerivAt_id y).sub_const c).norm_sq).fderiv
  rw [he]
  have hd := ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const c)).const_smul (2:ℝ)
  change HasFDerivAt (fun y => (2:ℝ) • innerSL ℝ (y-c)) _ x at hd
  rw [hd.fderiv]
  simp
  rfl

lemma quadratic_add_hessian {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (δ : ℝ)
    (c x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y + δ*‖y-c‖^2)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w + 2*δ*inner ℝ v w := by
  have hn : ContDiff ℝ ∞ (fun y : E => ‖y-c‖^2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have he := EllipticKernel.hessian_add_smul_sub_const (z := x) hf.contDiffAt hn.contDiffAt δ 0
  simp only [sub_zero] at he
  rw [he]
  simp only [_root_.add_apply, _root_.smul_apply,
    smul_eq_mul, norm_sub_sq_hessian]
  ring

end PotentialABP

namespace PotentialABP
variable {d : ℕ}
local notation "E" => EuclideanSpace ℂ (Fin d)
local instance (d : ℕ) : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin d)) :=
  InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin d))
local notation "e" => EuclideanSpace.equiv (Fin d) ℂ

lemma hessian_coord_comp {f : (Fin d → ℂ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ e)) x v w =
      fderiv ℝ (fderiv ℝ f) (e x) (e v) (e w) := by
  let er := (EuclideanSpace.equiv (Fin d) ℂ).toContinuousLinearMap.restrictScalars ℝ
  have her : ContDiff ℝ ∞ e := er.contDiff
  have hd : fderiv ℝ e = fun _ => (er : E →L[ℝ] (Fin d → ℂ)) := by
    funext y
    exact er.hasFDerivAt.fderiv
  rw [PotentialKaehler.second_derivative_comp her.contDiffAt hf.contDiffAt v w, hd]
  simp
  rfl

lemma levi_coord_pair {f : (Fin d → ℂ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ e)) x v v +
      fderiv ℝ (fderiv ℝ (f ∘ e)) x (Complex.I • v) (Complex.I • v) =
        4 * inner ℝ ((PotentialKaehler.potentialMatrix f (e x)).toEuclideanLin v) v := by
  rw [hessian_coord_comp hf, hessian_coord_comp hf]
  rw [real_inner_comm, real_inner_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  change _ = 4 * (star (e v) ⬝ᵥ ((PotentialKaehler.potentialMatrix f (e x)) *ᵥ (e v))).re
  rw [PotentialKaehler.potentialMatrix, PotentialKaehler.hermitianPartMatrix_pair]
  simp only [map_smul, PotentialKaehler.hermitianPart]
  ring

end PotentialABP

end
end

end OAI

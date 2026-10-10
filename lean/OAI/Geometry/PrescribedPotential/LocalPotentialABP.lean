import Mathlib
import OAI.Geometry.PrescribedPotential.ComplexContactDeterminant
import OAI.Geometry.PrescribedPotential.ContactSetABP
import OAI.Geometry.PrescribedPotential.QuadraticContact

namespace OAI

/-! Local Potential A B P. -/

section

 

noncomputable section
open Matrix Set Filter Topology Metric MeasureTheory
open scoped InnerProductSpace ContDiff
namespace PotentialABP
variable {d : ℕ}
local notation "E" => EuclideanSpace ℂ (Fin d)
local instance localPotentialABPRealInnerProductSpace (d : ℕ) :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin d)) :=
  InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin d))
local notation "e" => EuclideanSpace.equiv (Fin d) ℂ

lemma quadratic_levi_pair {f : (Fin d → ℂ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (c x v : E) (δ : ℝ) :
    let u : E → ℝ := fun y => f (e y) + δ*‖y-c‖^2
    fderiv ℝ (fderiv ℝ u) x v v +
      fderiv ℝ (fderiv ℝ u) x (Complex.I • v) (Complex.I • v) =
        4 * inner ℝ ((PotentialKaehler.potentialMatrix f (e x)).toEuclideanLin v) v
          + 4*δ*‖v‖^2 := by
  let er := (EuclideanSpace.equiv (Fin d) ℂ).toContinuousLinearMap.restrictScalars ℝ
  have he : ContDiff ℝ ∞ (f ∘ e) := hf.comp er.contDiff
  change ContDiff ℝ ∞ (fun y : E => f (e y)) at he
  dsimp only
  rw [quadratic_add_hessian he, quadratic_add_hessian he]
  have hi : inner ℝ (Complex.I • v) (Complex.I • v) = ‖v‖^2 := by
    simp [norm_smul]
  rw [real_inner_self_eq_norm_sq, hi]
  have hp := levi_coord_pair hf x v
  dsimp only [Function.comp_def] at hp
  linarith

lemma quadratic_contact_det {f : (Fin d → ℂ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (c x : E) (δ : ℝ) (G : Matrix (Fin d) (Fin d) ℂ) (hG : G.IsHermitian)
    (hGδ : ∀ v : E, δ * ‖v‖^2 ≤ inner ℝ (G.toEuclideanLin v) v)
    (hB : ∀ v : E, 0 ≤ fderiv ℝ (fderiv ℝ
      (fun y : E => f (e y) + δ*‖y-c‖^2)) x v v) :
    |(fderiv ℝ (gradient (fun y : E => f (e y) + δ*‖y-c‖^2)) x).det| ≤
      (4:ℝ)^(2*d) * (G + PotentialKaehler.potentialMatrix f (e x)).det.re^2 := by
  let er := (EuclideanSpace.equiv (Fin d) ℂ).toContinuousLinearMap.restrictScalars ℝ
  have hu : ContDiff ℝ ∞ (fun y : E => f (e y) + δ*‖y-c‖^2) :=
    (hf.comp er.contDiff).add (contDiff_const.mul
      ((contDiff_id.sub contDiff_const).norm_sq ℝ))
  apply gradient_det_le_hermitian hu hB _
    (hG.add (PotentialKaehler.potentialMatrix_hermitian hf.contDiffAt))
  intro v
  have hp := quadratic_levi_pair hf c x v δ
  have hb := hB (Complex.I • v)
  have hg := hGδ v
  rw [map_add, LinearMap.add_apply, inner_add_left]
  linarith

 

theorem local_potential_sublevel_volume
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : (Fin d → ℂ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (G : E → Matrix (Fin d) (Fin d) ℂ)
    {c : E} {r δ K : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hmin : ∀ x ∈ closedBall c r, f (e c) ≤ f (e x))
    (hG : ∀ x ∈ closedBall c r, (G x).IsHermitian)
    (hGδ : ∀ x ∈ closedBall c r, ∀ v : E,
      δ*‖v‖^2 ≤ inner ℝ ((G x).toEuclideanLin v) v)
    (hdet : ∀ x ∈ closedBall c r,
      |(G x + PotentialKaehler.potentialMatrix f (e x)).det.re| ≤ K) :
    μ (closedBall (0:E) (δ*r/2)) ≤ ENNReal.ofReal ((4:ℝ)^(2*d)*K^2) *
      μ {x | x ∈ closedBall c r ∧ f (e x) ≤ f (e c) + δ*r^2/2} := by
  let u : E → ℝ := fun y => f (e y) + δ*‖y-c‖^2
  let er := (EuclideanSpace.equiv (Fin d) ℂ).toContinuousLinearMap.restrictScalars ℝ
  have hu : ContDiff ℝ ∞ u := (hf.comp er.contDiff).add
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))
  have ha : 0 ≤ δ*r/2 := by positivity
  have hgap : δ*r/2*r < δ*r^2 := by nlinarith [mul_pos hδ (sq_pos_of_pos hr)]
  have hboundary : ∀ x, dist x c = r → u c + δ*r^2 ≤ u x := by
    intro x hx
    have hm := hmin x (by change dist x c ≤ r; exact hx.le)
    simp only [u, ← dist_eq_norm, hx, dist_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero]
    linarith
  have hi := contacts_interior hr ha hgap hboundary
  have hlocal : μ (closedBall (0:E) (δ*r/2)) ≤
      ENNReal.ofReal ((4:ℝ)^(2*d)*K^2) * μ (contacts u c r (δ*r/2)) := by
    apply contact_measure_estimate μ hu hr ha hgap hboundary
    intro x hx
    have hd := quadratic_contact_det hf c x δ (G x) (hG x hx.1)
      (hGδ x hx.1) (contacts_hessian_nonneg hu hx (hi hx))
    apply hd.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hdet x hx.1)
  apply hlocal.trans
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply measure_mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hs := contacts_sublevel hr.le ha hx
  have hn : 0 ≤ δ*‖x-c‖^2 := by positivity
  simp only [u, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    add_zero] at hs
  nlinarith

end PotentialABP

end
end

end OAI

import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.IteratedReduction

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
namespace CoulombAtom
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma l2_norm_sq (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  rw [integral_ofReal]
  rfl

lemma l2_inner_re (f g : Lp ℂ 2 μ) :
    (⟪f, g⟫_ℂ).re = ∫ x, (⟪f x, g x⟫_ℂ).re ∂μ := by
  rw [L2.inner_def]
  exact (integral_re (L2.integrable_inner (𝕜 := ℂ) f g)).symm

lemma l2_multiplier_pairing (p : α → ℝ) (f g h : Lp ℂ 2 μ)
    (hg : (g : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * f x)
    (hh : (h : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * g x) :
    (⟪h, f⟫_ℂ).re = ‖g‖ ^ 2 := by
  rw [l2_inner_re, l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hg, hh] with x hx hy
  rw [hy, hx]
  simp only [Complex.sq_norm, Complex.normSq_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma l2_ims_identity (p d : α → ℝ) (a b v w : Lp ℂ 2 μ)
    (hv : (v : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * a x + (d x : ℂ) * b x)
    (hw : (w : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * v x +
      (d x : ℂ) * ((p x : ℂ) * b x)) :
    ‖v‖ ^ 2 - (⟪w, a⟫_ℂ).re = ∫ x, (d x) ^ 2 * ‖b x‖ ^ 2 ∂μ := by
  rw [l2_norm_sq, l2_inner_re]
  have hi : Integrable (fun x => ‖v x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp v).aestronglyMeasurable).mp (Lp.memLp v)
  have hj : Integrable (fun x => (⟪w x, a x⟫_ℂ).re) μ :=
    (L2.integrable_inner (𝕜 := ℂ) w a).re
  rw [← integral_sub hi hj]
  apply integral_congr_ae
  filter_upwards [hv, hw] with x hx hy
  rw [hy, hx]
  exact complex_ims_identity (p x) (d x) (a x) (b x)

end CoulombAtom

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff

end

end OAI

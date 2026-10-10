import Mathlib
import OAI.Analysis.Crouzeix.ExteriorCollar

namespace OAI

/-! Exterior Normal. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate

open scoped InnerProductSpace

namespace CrouzeixHilbert.Conformal

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma parameter_open : IsOpen {t : ℂ | C.radius < ‖t‖} := isOpen_lt continuous_const continuous_norm

lemma deriv_ne_zero {t : ℂ} (ht : C.radius < ‖t‖) : deriv C.G t ≠ 0 :=
  deriv_ne_zero_of_injOn C.parameter_open C.analytic.differentiableOn C.injective ht

theorem supporting_normal (hc : Convex ℝ U) {t : ℂ} (ht : ‖t‖ = 1)
    {z : ℂ} (hz : z ∈ closure U) :
    0 ≤ (conj (t * deriv C.G t) * (C.G t - z)).re := by
  have htC : C.radius < ‖t‖ := ht ▸ C.radius_lt_one
  have hdn := C.deriv_ne_zero htC
  let d := (C.analytic t htC).hasStrictDerivAt.hasStrictFDerivAt_equiv hdn
  let e := (d.toOpenPartialHomeomorph C.G).restrOpen {t : ℂ | C.radius < ‖t‖} C.parameter_open
  have heC : e.source ⊆ {t : ℂ | C.radius < ‖t‖} := inter_subset_right
  have het : t ∈ e.source := ⟨d.mem_toOpenPartialHomeomorph_source, htC⟩
  have heG : (e : ℂ → ℂ) = C.G := rfl
  have hegt : C.G t ∈ e.target := e.map_source het
  have hei : e.symm (C.G t) = t := e.left_inv het
  have hp : C.G t ∈ closure U := (C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr ht)).1
  have hemax : IsLocalMaxOn (fun w : ℂ => ‖e.symm w‖ ^ 2) (closure U) (C.G t) := by
    filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds hegt),
      self_mem_nhdsWithin] with w hw hwU
    rw [hei, ht, one_pow]
    have hwsmall : ‖e.symm w‖ ≤ 1 := by
      by_contra hn
      have houtside := C.outside.mapsTo (lt_of_not_ge hn)
      have heq : C.G (e.symm w) = w := e.right_inv hw
      exact houtside (heq.symm ▸ hwU)
    nlinarith [norm_nonneg (e.symm w)]
  have heder : HasDerivAt e.symm (deriv C.G t)⁻¹ (C.G t) :=
    e.hasDerivAt_symm hegt hdn (by rw [hei, heG]; exact (C.analytic t htC).differentiableAt.hasDerivAt)
  have hdir := hemax.hasFDerivWithinAt_nonpos
    (heder.hasFDerivAt.restrictScalars ℝ).norm_sq.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hc.closure.segment_subset hp hz))
  simp only [ContinuousLinearMap.comp_apply, smul_apply] at hdir
  simp only [innerSL_apply_apply] at hdir
  rw [hei, real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply] at hdir
  simp only [two_smul] at hdir
  change (((z - C.G t) * (deriv C.G t)⁻¹) * conj t).re +
    (((z - C.G t) * (deriv C.G t)⁻¹) * conj t).re ≤ 0 at hdir
  have halg : (((z - C.G t) * (deriv C.G t)⁻¹) * conj t).re =
      - (conj (t * deriv C.G t) * (C.G t - z)).re / Complex.normSq (deriv C.G t) := by
    rw [Complex.inv_def]
    simp only [map_mul, div_eq_mul_inv, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
    ring
  rw [halg] at hdir
  have hpos := Complex.normSq_pos.mpr hdn
  have hle : - (conj (t * deriv C.G t) * (C.G t - z)).re /
      Complex.normSq (deriv C.G t) ≤ 0 := by linarith
  exact neg_nonpos.mp (by simpa only [zero_mul] using (div_le_iff₀ hpos).mp hle)

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI

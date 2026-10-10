import OAI.Analysis.NumericalRange.DensityTransport

namespace OAI

section

section
noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

lemma circle_log_derivative_real {ψ : ℂ → ℂ} {t : ℂ}
    (ht : ‖t‖ = 1) (hψ : DifferentiableAt ℂ ψ t)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖ψ z‖ = 1) :
    (t*deriv ψ t/ψ t).im = 0 := by
  have hp : ‖ψ t‖ = 1 := hb t ht
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => exp ((s:ℂ)*I)*t)
      (exp ((s:ℂ)*I)*I*t) s := by
    simpa using (((hasDerivAt_id s).ofReal_comp.mul_const I).cexp.mul_const t)
  have he : HasDerivAt (fun s : ℝ => ψ (exp ((s:ℂ)*I)*t))
      (I*t*deriv ψ t) 0 := by
    simpa only [ofReal_zero, zero_mul, exp_zero, one_mul, Function.comp_def,
      smul_eq_mul] using (show HasDerivAt ψ (deriv ψ t) (exp (((0:ℝ):ℂ)*I)*t) from by simpa using hψ.hasDerivAt).scomp 0 (hd 0)
  have hn : (fun s : ℝ => ‖ψ (exp ((s:ℂ)*I)*t)‖^2) = fun _ => (1:ℝ) := by
    funext s
    rw [hb _ (by rw [norm_mul, norm_exp_ofReal_mul_I, ht, one_mul]), one_pow]
  have heq := he.norm_sq
  rw [hn] at heq
  have hz := heq.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  have hi : inner ℝ (ψ t) (I*t*deriv ψ t) = -(conj (ψ t)*(t*deriv ψ t)).im := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
    change (conj (ψ t)*(I*t*deriv ψ t)).re = _
    rw [show conj (ψ t)*(I*t*deriv ψ t) = I*(conj (ψ t)*(t*deriv ψ t)) by ring]
    simp
  simp only [ofReal_zero, zero_mul, exp_zero, one_mul] at hz
  rw [hi] at hz
  have hconj : (ψ t)⁻¹ = conj (ψ t) := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hp]
    simp
  rw [div_eq_mul_inv, hconj, mul_comm (t*deriv ψ t)]
  linarith

lemma circle_log_derivative_nonneg {ψ : ℂ → ℂ} {t : ℂ}
    (_ht : ‖t‖ = 1) (hψ : DifferentiableAt ℂ ψ t)
    (hb : ‖ψ t‖ = 1)
    (hin : ∀ᶠ r : ℝ in 𝓝[Iic 1] 1, ‖ψ ((r:ℂ)*t)‖ ≤ 1) :
    0 ≤ (t*deriv ψ t/ψ t).re := by
  have hd : HasDerivAt (fun r : ℝ => (r:ℂ)*t) t 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).ofReal_comp.mul_const t
  have he : HasDerivAt (fun r : ℝ => ψ ((r:ℂ)*t)) (t*deriv ψ t) 1 := by
    simpa only [ofReal_one, one_mul, Function.comp_def, smul_eq_mul] using
      (show HasDerivAt ψ (deriv ψ t) (((1:ℝ):ℂ)*t) from by simpa using hψ.hasDerivAt).scomp 1 hd
  have hm : IsLocalMaxOn (fun r : ℝ => ‖ψ ((r:ℂ)*t)‖^2) (Iic 1) 1 := by
    filter_upwards [hin] with r hr
    simpa only [ofReal_one, one_mul, hb, one_pow] using
      (pow_le_pow_left₀ (norm_nonneg _) hr 2)
  have hy : (-1:ℝ) ∈ posTangentConeAt (Iic (1:ℝ)) 1 := by
    apply mem_posTangentConeAt_of_segment_subset
    apply (convex_Iic (1:ℝ)).segment_subset <;> simp
  have hh := hm.hasFDerivWithinAt_nonpos he.norm_sq.hasFDerivAt.hasFDerivWithinAt hy
  simp only [ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, ofReal_one, one_mul] at hh
  have hi : inner ℝ (ψ t) (t*deriv ψ t) = (conj (ψ t)*(t*deriv ψ t)).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']; rfl
  rw [hi] at hh
  have hconj : (ψ t)⁻¹ = conj (ψ t) := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hb]
    simp
  rw [div_eq_mul_inv, hconj, mul_comm (t*deriv ψ t)]
  linarith

end CompleteCrouzeix

end

end
end

end OAI

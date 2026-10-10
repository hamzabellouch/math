import OAI.Probability.SLE.Geometry.EndpointMonotonicity

namespace OAI

/-! A complex linear equation with nonpositive real coefficient contracts,
including an initial endpoint where the coefficient may be singular. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

lemma complex_normSq_hasDerivWithinAt {S : Set ℝ} {t : ℝ}
    (f : ℝ → ℂ) (v : ℂ) (hf : HasDerivWithinAt f v S t) :
    HasDerivWithinAt (fun s => Complex.normSq (f s))
      (2*((f t).re*v.re+(f t).im*v.im)) S t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hf
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hf
  change HasDerivWithinAt (fun s => (f s).re) v.re S t at hr
  change HasDerivWithinAt (fun s => (f s).im) v.im S t at hi
  convert! (hr.pow 2).add (hi.pow 2) using 1
  · funext s
    simp only [Complex.normSq_apply,pow_two,Pi.add_apply,Pi.mul_apply]
  · ring

theorem complex_linear_endpoint_contraction {T : ℝ} (hT : 0 ≤ T)
    (f c : ℝ → ℂ) (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioc 0 T, HasDerivWithinAt f (c t*f t) (Ici t) t)
    (hb : ∀ t ∈ Ioc 0 T, (c t).re ≤ 0) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ ‖f 0‖ := by
  have hsq := le_initial_of_deriv_nonpos_on_Ioc hT
    (fun t => Complex.normSq (f t))
    (fun t => 2*(c t).re*Complex.normSq (f t))
    (Complex.continuous_normSq.comp_continuousOn hc) (fun t ht => ?_) (fun t ht => ?_)
  · intro t ht
    have hh := hsq t ht
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg (f t),norm_nonneg (f 0)]
  · convert! complex_normSq_hasDerivWithinAt f (c t*f t) (hd t ht) using 1
    simp only [Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
    ring
  · exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hb t ht)) (Complex.normSq_nonneg _)

end SLEExactGauge

end

end OAI

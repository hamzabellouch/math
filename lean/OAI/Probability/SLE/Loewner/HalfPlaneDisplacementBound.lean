import OAI.Probability.SLE.Mass.HalfPlaneZeroMass

namespace OAI

/-! The total hydrodynamic mass bounds a nonnegative-imaginary displacement. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

lemma hydrodynamic_vertical_limits {f : ℂ → ℂ} {c : ℝ}
    (hcoef : Tendsto (fun z : ℂ => z*f z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 (-c:ℂ))) :
    Tendsto (fun n : ℕ => f (verticalInfinity n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((n:ℝ)+1)*(f (verticalInfinity n)).im) atTop (𝓝 c) := by
  have hp := hcoef.comp verticalInfinity_tendsto
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
  have hh := hp.mul (hi.comp (verticalInfinity_tendsto.mono_right inf_le_left))
  have hzero : Tendsto (fun n : ℕ => f (verticalInfinity n)) atTop (𝓝 0) := by
    simp only [mul_zero] at hh
    apply hh.congr
    intro n
    have hn : verticalInfinity n ≠ 0 := by
      intro he
      have hv := verticalInfinity_mem n
      simp only [upperHalfPlane,mem_ofPred_eq,he,zero_im,lt_self_iff_false] at hv
    simp only [Function.comp_apply]
    field_simp [hn]
  refine ⟨hzero,?_⟩
  have ht := (Complex.continuous_re.tendsto (-c:ℂ) |>.comp hp).neg
  simpa only [Function.comp_apply,verticalInfinity,mul_re,mul_im,ofReal_re,ofReal_im,
    I_re,I_im,mul_zero,zero_mul,add_zero,mul_one,neg_re,neg_neg,neg_zero,zero_sub] using ht

lemma nonnegative_im_hydrodynamic_bound {f : ℂ → ℂ} {c : ℝ}
    (hf : DifferentiableOn ℂ f upperHalfPlane)
    (hm : ∀ z∈upperHalfPlane, 0≤(f z).im) (hc : 0≤c)
    (hcoef : Tendsto (fun z : ℂ => z*f z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 (-c:ℂ)))
    {z : ℂ} (hz : z∈upperHalfPlane) : ‖f z‖≤c/z.im := by
  obtain ⟨hzero,hmass⟩ := hydrodynamic_vertical_limits hcoef
  rcases holomorphic_nonnegative_im_dichotomy hf hm with ⟨a,ha⟩ | hpos
  · have ht : Tendsto (fun _ : ℕ => a) atTop (𝓝 0) :=
      hzero.congr (fun n => ha _ (verticalInfinity_mem n))
    have ha0 : a=0 := tendsto_nhds_unique tendsto_const_nhds ht
    rw [ha z hz,ha0,norm_zero]
    exact div_nonneg hc (show 0<z.im from hz).le
  · exact norm_le_mass_div_height hz hc (halfPlane_vanishing_mass_bound hf hpos hzero hmass hz)

end SLEExactGauge

end

end OAI

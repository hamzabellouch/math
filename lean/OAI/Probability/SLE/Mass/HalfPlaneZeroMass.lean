import OAI.Probability.SLE.Mass.HalfPlaneHerglotzMass
import Mathlib.Analysis.Complex.OpenMapping

namespace OAI

/-! A holomorphic map with nonnegative imaginary part, vanishing value
and zero mass at infinity is identically zero. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

lemma holomorphic_nonnegative_im_dichotomy {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane)
    (hm : ∀ z ∈ upperHalfPlane, 0≤(f z).im) :
    (∃ c : ℂ, ∀ z ∈ upperHalfPlane, f z=c) ∨ MapsTo f upperHalfPlane upperHalfPlane := by
  rcases (hf.analyticOnNhd isOpen_upperHalfPlane).is_constant_or_isOpen
    (convex_halfSpace_im_gt (0:ℝ)).isPreconnected with hc|ho
  · exact Or.inl hc
  right
  intro z hz
  change 0 < (f z).im
  by_contra hn
  have hzero : (f z).im=0 := le_antisymm (le_of_not_gt hn) (hm z hz)
  have hi := (ho upperHalfPlane Subset.rfl isOpen_upperHalfPlane).mem_nhds
    (mem_image_of_mem f hz)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hi
  have hw : f z-((ε/2:ℝ):ℂ)*I ∈ ball (f z) ε := by
    rw [mem_ball,dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_mul,norm_I,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨w,hwH,he⟩ := hball hw
  have him := hm w hwH
  rw [he] at him
  simp only [sub_im,mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero,hzero] at him
  linarith

theorem halfPlane_zero_mass_eq_zero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane)
    (hm : ∀ z ∈ upperHalfPlane, 0≤(f z).im)
    (hzero : Tendsto (fun n : ℕ => f (verticalInfinity n)) atTop (𝓝 0))
    (hc : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(f (verticalInfinity n)).im) atTop (𝓝 0)) :
    ∀ z ∈ upperHalfPlane, f z=0 := by
  rcases holomorphic_nonnegative_im_dichotomy hf hm with ⟨c,hc'⟩|hpos
  · have ht : Tendsto (fun _ : ℕ => c) atTop (𝓝 0) := by
      apply hzero.congr
      intro n
      exact hc' _ (verticalInfinity_mem n)
    have he : c=0 := tendsto_nhds_unique tendsto_const_nhds ht
    exact fun z hz => (hc' z hz).trans he
  · have hi : I ∈ upperHalfPlane := by simp [upperHalfPlane]
    have hb := halfPlane_vanishing_mass_bound hf hpos hzero hc hi
    simp only [I_im,one_mul,zero_mul] at hb
    have he : f I=0 := normSq_eq_zero.mp (le_antisymm hb (normSq_nonneg _))
    have hp := hpos hi
    simp only [upperHalfPlane,mem_ofPred_eq,he,zero_im,lt_self_iff_false] at hp

theorem holomorphic_zero_hydrodynamic_mass {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane)
    (hm : ∀ z ∈ upperHalfPlane, 0≤(f z).im)
    (hcoef : Tendsto (fun z : ℂ => z*f z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 0)) :
    ∀ z ∈ upperHalfPlane, f z=0 := by
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
    field_simp
  have hmass : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(f (verticalInfinity n)).im) atTop (𝓝 0) := by
    have ht := (Complex.continuous_re.tendsto (0:ℂ) |>.comp hp).neg
    simpa only [Function.comp_apply,verticalInfinity,mul_re,mul_im,ofReal_re,ofReal_im,
      I_re,I_im,mul_zero,zero_mul,add_zero,mul_one,zero_re,neg_zero,zero_sub,neg_neg] using ht
  exact halfPlane_zero_mass_eq_zero hf hm hzero hmass

end SLEExactGauge

end

end OAI

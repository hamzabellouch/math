import OAI.Probability.SLE.Loewner.VerticalHalfPlaneUniqueness

namespace OAI

/-! Vertical displacement bounds imply the normalization used in half-plane
automorphism uniqueness. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma vertical_displacement_zero_of_bound {F : ℂ → ℂ} {C : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, ‖F (verticalInfinity n)-verticalInfinity n‖≤C/((n:ℝ)+1)) :
    Tendsto (fun n : ℕ => F (verticalInfinity n)-verticalInfinity n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' h
  simpa only [div_eq_mul_inv,mul_zero] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp verticalHeights_tendsto) :
      Tendsto (fun n : ℕ => C*((n:ℝ)+1)⁻¹) atTop (𝓝 (C*0)))

lemma vertical_normalization_of_displacement {F : ℂ → ℂ}
    (h : Tendsto (fun n : ℕ => F (verticalInfinity n)-verticalInfinity n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => F (verticalInfinity n)/(((n:ℝ)+1:ℝ):ℂ)) atTop (𝓝 I) := by
  have hi : Tendsto (fun n : ℕ => ((((n:ℝ)+1)⁻¹:ℝ):ℂ)) atTop (𝓝 0) := by
    exact_mod_cast continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero.comp verticalHeights_tendsto)
  have hh := (h.mul hi).add_const I
  simp only [zero_mul,zero_add] at hh
  apply hh.congr
  intro n
  have hn : (((n:ℝ)+1:ℝ):ℂ)≠0 := ofReal_ne_zero.mpr (by positivity)
  dsimp only [verticalInfinity]
  push_cast
  field_simp
  ring

end SLEExactGauge

end

end OAI

import OAI.Probability.SLE.Loewner.HydrodynamicComposition

namespace OAI

/-! The Schwarz–Pick bound for a half-plane map vanishing at infinity.
Only the total mass coefficient is used; no representation theorem is assumed. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma halfPlane_schwarz_pick_vanishing_scaled {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane) (hm : MapsTo f upperHalfPlane upperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlane) {y : ℝ} (hy : 0<y) :
    z.im*normSq (f z-conj (f ((y:ℂ)*I))) ≤
      (f z).im*(y*(f ((y:ℂ)*I)).im)*normSq (z/(y:ℂ)+I) := by
  have hw : (y:ℂ)*I ∈ upperHalfPlane := by simpa [upperHalfPlane] using hy
  have hh := halfPlane_schwarz_pick_kernel hf hm hz hw
  have h2 : z/(y:ℂ)+I = (z-conj ((y:ℂ)*I))/(y:ℂ) := by
    simp only [map_mul,conj_ofReal,conj_I]
    field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
    ring
  rw [h2,normSq_div_real]
  have hi : ((y:ℂ)*I).im=y := by simp
  rw [hi] at hh
  apply (mul_le_mul_iff_of_pos_right hy).mp
  field_simp
  nlinarith [hh]

theorem halfPlane_vanishing_mass_bound {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane) (hm : MapsTo f upperHalfPlane upperHalfPlane)
    {c : ℝ} (hzero : Tendsto (fun n : ℕ => f (verticalInfinity n)) atTop (𝓝 0))
    (hc : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(f (verticalInfinity n)).im) atTop (𝓝 c))
    {z : ℂ} (hz : z ∈ upperHalfPlane) : z.im*normSq (f z) ≤ c*(f z).im := by
  have hi := tendsto_inv_atTop_zero.comp verticalHeights_tendsto
  have hsmall : Tendsto (fun n : ℕ => z/(((n:ℝ)+1:ℝ):ℂ)) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := z) (f := atTop)).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hi)
    simpa only [Function.comp_apply,ofReal_zero,mul_zero,ofReal_inv,div_eq_mul_inv] using hh
  have hleft := (tendsto_const_nhds (x := z.im) (f := atTop)).mul
    (continuous_normSq.tendsto (f z-conj 0) |>.comp
      ((tendsto_const_nhds (x := f z) (f := atTop)).sub
        (Complex.continuous_conj.tendsto 0 |>.comp hzero)))
  have hright := ((tendsto_const_nhds (x := (f z).im) (f := atTop)).mul hc).mul
    (continuous_normSq.tendsto ((0:ℂ)+I) |>.comp (hsmall.add_const I))
  have hh := le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall (fun n => halfPlane_schwarz_pick_vanishing_scaled hf hm hz
      (by positivity : 0<(n:ℝ)+1)))
  simpa only [map_zero,sub_zero,zero_add,normSq_I,mul_one,mul_comm] using hh

lemma norm_le_mass_div_height {w : ℂ} {c y : ℝ} (hy : 0<y) (hc : 0≤c)
    (hb : y*normSq w ≤ c*w.im) : ‖w‖ ≤ c/y := by
  by_cases hw : w=0
  · subst w
    simpa only [norm_zero] using div_nonneg hc hy.le
  have hnorm : 0<‖w‖ := norm_pos_iff.mpr hw
  have hi := Complex.im_le_norm w
  have hh := mul_le_mul_of_nonneg_left hi hc
  rw [normSq_eq_norm_sq] at hb
  apply (le_div_iff₀ hy).mpr
  nlinarith

end SLEExactGauge

end

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSubunitPressure
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralUniformError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicForm

namespace OAI

/-! The exterior small-pressure hypothesis follows from subunit amplitude
convergence. The scale is the reciprocal of the nonlinear exponent. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralPower_pressure_away (R L K : ℝ) (hK : 0 ≤ K)
    (w : ℕ → SpectralHarmonicWeight R)
    (hw : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, ‖(w n).density r‖ ≤ K)
    (H : ℕ → ℝ → ℝ) (H₀ : ℝ → ℝ)
    (hH : TendstoUniformlyOn H H₀ atTop (Icc 0 R ∩ Ioi L))
    (hunit : ∀ n r, r ∈ Icc 0 R ∩ Ioi L → ‖H n r‖ ≤ 1)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hbound : ∀ r ∈ Icc 0 R ∩ Ioi L, ‖H₀ r‖ ≤ ρ)
    (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) :
    ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ n, ∀ᵐ r ∂radialPressureMeasure R, L < r →
        ‖(1/(p n : ℝ))⁻¹*((w n).density r*(H n r)^(p n))‖ ≤ η n := by
  have ht := spectralSubunit_scaled_power_uniform H H₀ hH ρ hρ hρ1 hbound p hp
  have hb (n : ℕ) : ∃ B : ℝ, ∀ r ∈ Icc 0 R ∩ Ioi L,
      ‖(p n : ℝ)*(H n r)^(p n)-(0 : ℝ)‖ ≤ B := by
    refine ⟨p n,fun r hr => ?_⟩
    rw [sub_zero,norm_mul,norm_pow,Real.norm_natCast]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (hunit n r hr))
  obtain ⟨δ,hδ,hδ0,hδb⟩ := spectralUniform_error_bound
    (fun n r => (p n : ℝ)*(H n r)^(p n)) (fun _ => 0) ht hb
  refine ⟨fun n => K*δ n,fun n => mul_nonneg hK (hδ n),?_,?_⟩
  · simpa only [mul_zero] using hδ0.const_mul K
  · intro n
    have hr : ∀ᵐ r ∂radialPressureMeasure R, r ∈ Icc 0 R := by
      unfold radialPressureMeasure
      apply (ae_withDensity_iff (by fun_prop)).2
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr _
      exact hr
    filter_upwards [hw n,hr] with r hwr hr hL
    have hd : ‖(p n : ℝ)*(H n r)^(p n)‖ ≤ δ n := by
      simpa only [sub_zero] using hδb n r ⟨hr,hL⟩
    calc
      _ = ‖(w n).density r‖*‖(p n : ℝ)*(H n r)^(p n)‖ := by
        simp only [one_div,inv_inv,norm_mul]
        ring
      _ ≤ K*δ n := mul_le_mul hwr hd (norm_nonneg _) hK

end DefocusingNLS

end OAI

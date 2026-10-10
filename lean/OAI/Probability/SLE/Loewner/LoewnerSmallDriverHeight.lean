import OAI.Probability.SLE.Loewner.LoewnerInverseCompactness
import OAI.Probability.SLE.Loewner.VerticalMapDerivative
import OAI.Probability.SLE.Loewner.LoewnerHeightClearance

namespace OAI

/-! Drivers converging uniformly to zero cannot all generate traces below
a height strictly smaller than the corresponding vertical slit. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

theorem small_drivers_not_all_height_bounded
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ) (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (h : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n))
    (T : ℝ≥0) (H : ℝ) (hH : 0 ≤ H) (hHT : H < 2*Real.sqrt T)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hU : ∀ n t, t ∈ Icc 0 T → |U n t| ≤ δ n) :
    ¬ ∀ n t, t ∈ Icc 0 T → (γ n t).im ≤ H := by
  intro hlow
  obtain ⟨σ,f,hσ,hf,hlim⟩ := inverse_family_subsequence U γ G F h T
  have haxis (y : ℝ) (hy : 0 < y) : f ((y:ℂ)*I)=verticalReversePath y T := by
    exact tendsto_nhds_unique
      (hlim.tendsto_at (by simpa [upperHalfPlane] using hy))
      ((inverse_vertical_tendsto U γ G F h T δ hδ hU hy).comp hσ.tendsto_atTop)
  let r : ℝ := (2*Real.sqrt T-H)/4
  have hr : 0 < r := by dsimp [r]; linarith
  have hT : 0 < (T:ℝ) := by
    by_contra hn
    have he : (T:ℝ)=0 := le_antisymm (le_of_not_gt hn) T.coe_nonneg
    simp only [he,Real.sqrt_zero,mul_zero] at hHT
    linarith
  have hsqrt (y : ℝ) : 2*Real.sqrt T ≤ Real.sqrt (y^2+4*T) := by
    have h1 := Real.sq_sqrt T.coe_nonneg
    have h2 := Real.sq_sqrt (show 0 ≤ y^2+4*(T:ℝ) by positivity)
    nlinarith [Real.sqrt_nonneg (T:ℝ),Real.sqrt_nonneg (y^2+4*(T:ℝ))]
  have hbound (y : ℝ) (hy : 0 < y) :
      r ≤ (128*Real.pi)*y*(y/Real.sqrt (y^2+4*T)) := by
    have hiy : (y:ℂ)*I ∈ upperHalfPlane := by simpa [upperHalfPlane] using hy
    have hi := Complex.continuous_im.continuousAt.tendsto.comp (hlim.tendsto_at hiy)
    rw [haxis y hy] at hi
    have hheight : H+2*r < (verticalReversePath y T).im := by
      simp only [verticalReversePath,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
        Complex.ofReal_im,Complex.I_re,mul_one,mul_zero,add_zero]
      dsimp [r]
      linarith [hsqrt y]
    have hev : ∀ᶠ n in atTop, H+2*r < (F (σ n) T ((y:ℂ)*I)).im :=
      hi.eventually (Ioi_mem_nhds hheight)
    have hb : ∀ᶠ n in atTop,
        r ≤ (128*Real.pi)*y*‖deriv (F (σ n) T) ((y:ℂ)*I)‖ := by
      filter_upwards [hev] with n hn
      have hball : ball (F (σ n) T ((y:ℂ)*I)) r ⊆ survivingDomain (γ (σ n)) T := by
        intro z hz
        have hzdist : ‖z-F (σ n) T ((y:ℂ)*I)‖ < r := by
          simpa only [mem_ball,dist_eq_norm] using hz
        have hzheight := (abs_lt.mp ((Complex.abs_im_le_norm
          (z-F (σ n) T ((y:ℂ)*I))).trans_lt hzdist)).1
        simp only [Complex.sub_im] at hzheight
        apply survives_above_trace_height (γ (σ n)) T H (hlow (σ n))
        · linarith
        · linarith
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
        Complex.ofReal_im,Complex.I_re,mul_zero,add_zero] using
        (h (σ n)).inverse_clearance_bound T hiy hr hball
    have hd := ((hlim.deriv (Eventually.of_forall fun n => (h (σ n)).2.2.2.2.1 T)
      isOpen_upperHalfPlane).tendsto_at hiy).norm
    have hh := ge_of_tendsto (hd.const_mul ((128*Real.pi)*y)) hb
    rw [vertical_axis_derivative f T hf haxis hy,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hy.le (Real.sqrt_nonneg _))] at hh
    exact hh
  let y : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hy : Tendsto y atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hden := ((hy.pow 2).add_const (4*(T:ℝ))).sqrt
  have hden0 : Real.sqrt (0^2+4*(T:ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hl := ((hy.const_mul (128*Real.pi)).mul (hy.div hden hden0))
  have hzero : r ≤ 0 := by
    apply ge_of_tendsto (by simpa using hl)
    exact Eventually.of_forall (fun n => hbound (y n) (by dsimp [y]; positivity))
  exact (not_le_of_gt hr) hzero

end SLEExactGauge

end

end OAI

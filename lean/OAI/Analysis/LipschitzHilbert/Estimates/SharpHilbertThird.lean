import OAI.Analysis.LipschitzHilbert.Estimates.SharpHilbertL2
import OAI.Analysis.LipschitzHilbert.Estimates.SharpHilbertFourth
import OAI.Analysis.LipschitzHilbert.Fourier.ConvolutionThird

namespace OAI

/-! The third-moment bound, including bounded measurable inputs needed
as explicit dual test functions. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpHilbert_two_four_constants : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ r R : ℝ, 0<r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^2)≤A^2*(∫ x, ‖f x‖^2) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^4)≤C^4*(∫ x, ‖f x‖^4) := by
  obtain ⟨A,hA,hTwo⟩ := sharpHilbert_uniform_L2
  obtain ⟨D,hD,hFour⟩ := sharpHilbert_uniform_fourth
  have hDle : D≤(D+1)^4 := by
    nlinarith [sq_nonneg D,pow_nonneg hD 3,pow_nonneg hD 4]
  refine ⟨A,D+1,hA,by positivity,?_⟩
  intro r R hr hrR f
  have h2 := hTwo r R hr hrR f
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2.2
  rw [←Lp.norm_toLp _ h2.1,ENNReal.toReal_ofReal (mul_nonneg hA.le (norm_nonneg _))] at hn
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow,memLp_toL2_norm_sq volume _ h2.1] at hp
  have hfe : ‖f.toLp 2 volume‖^2=∫ x, ‖f x‖^2 := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  rw [hfe] at hp
  exact ⟨hp,(hFour r R hr hrR f).2.trans
    (mul_le_mul_of_nonneg_right hDle (integral_nonneg fun x => by positivity))⟩

theorem sharpHilbert_uniform_third_bounded : ∃ E : ℝ, 0≤E ∧
    ∀ r R : ℝ, 0<r → r≤R → ∀ f : ℝ → ℂ, Measurable f →
      MemLp f 2 volume → MemLp f 4 volume →
      ∀ M : ℝ, (∀ x, ‖f x‖≤M) →
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^3) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^3)≤E*(∫ x, ‖f x‖^3) := by
  obtain ⟨A,C,hA,hC,hb⟩ := sharpHilbert_two_four_constants
  refine ⟨3*(4*A^2+16*C^4),by positivity,?_⟩
  intro r R hr hrR f hfm hf2 hf4 M hM
  exact convolution_third_bound (sharpTimeKernel r R) f
    (sharpTimeKernel_integrable r R hr (hr.trans_le hrR)) (sharpTimeKernel_measurable r R)
    hfm hf2 hf4 M hM A C hA.le hC.le
    (fun g => (hb r R hr hrR g).1) (fun g => (hb r R hr hrR g).2)

end LipschitzHilbert.PacketRepresentation

end

end OAI

import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedBilinearError
import OAI.Analysis.RieszRectifiability.Kernel.ComplexHeightPairing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap

theorem complex_height_interior_re {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (q : Ambient d × Ambient d) :
    (complexHeightInteriorIntegrand m w g q).re =
      fractionalBilinear m w (fun x => (g x).re) q.1 q.2 := by
  unfold complexHeightInteriorIntegrand fractionalBilinear inverseDistancePow
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.sub_re]
  ring

theorem complex_height_interior_im {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (q : Ambient d × Ambient d) :
    (complexHeightInteriorIntegrand m w g q).im =
      fractionalBilinear m w (fun x => (g x).im) q.1 q.2 := by
  unfold complexHeightInteriorIntegrand fractionalBilinear inverseDistancePow
  simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.sub_im]
  ring

theorem complex_height_interior_integrable_of_energy {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (hgrowth : GlobalUpperGrowth (p + 1) C ν)
    (w : Ambient d → ℝ) (hwm : Measurable w) (hw : Integrable w ν)
    (g : 𝓢(Ambient d, ℂ))
    (henergy : Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) w q.1 q.2) (ν.prod ν)) :
    Integrable (complexHeightInteriorIntegrand (p + 1) w g) (ν.prod ν) := by
  let gr : 𝓢(Ambient d, ℝ) := g.postcompCLM Complex.reCLM
  let gi : 𝓢(Ambient d, ℝ) := g.postcompCLM Complex.imCLM
  obtain ⟨Lr, Br, hLr, hBr⟩ := schwartz_real_bounded_lipschitz gr
  obtain ⟨Li, Bi, hLi, hBi⟩ := schwartz_real_bounded_lipschitz gi
  have hr := (fractional_bilinear_integrable_and_cap_error p C ν hgrowth w gr hwm hw
    Lr Br hLr hBr henergy 1 zero_lt_one).1
  have hi := (fractional_bilinear_integrable_and_cap_error p C ν hgrowth w gi hwm hw
    Li Bi hLi hBi henergy 1 zero_lt_one).1
  apply Integrable.re_im_iff.mp
  constructor
  · change Integrable (fun q => (complexHeightInteriorIntegrand (p + 1) w g q).re) (ν.prod ν)
    simpa only [complex_height_interior_re] using! hr
  · change Integrable (fun q => (complexHeightInteriorIntegrand (p + 1) w g q).im) (ν.prod ν)
    simpa only [complex_height_interior_im] using! hi

end

end RieszRectifiability

end OAI

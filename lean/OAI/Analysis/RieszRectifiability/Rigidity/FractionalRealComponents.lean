import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Filter

theorem fractionalSchwartzTest_re (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    (fractionalSchwartzTest p g x).re = (-1 / 2 : ℝ) *
      ∫ h, fractionalSchwartzKernel (p + 1) (g.postcompCLM Complex.reCLM) x h := by
  have hi := fractionalSchwartzKernel_integrable p g x
  have hcomm : (∫ h, fractionalSchwartzKernel (p + 1) g x h).re =
      ∫ h, (fractionalSchwartzKernel (p + 1) g x h).re :=
    (Complex.reCLM.integral_comp_comm hi).symm
  unfold fractionalSchwartzTest
  rw [Complex.smul_re, smul_eq_mul, hcomm]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun h => ?_)
  change Complex.reCLM (inverseDistancePow (p + 1 + 1) 0 h •
    (g (x + h) + g (x - h) - (2 : ℝ) • g x)) =
    inverseDistancePow (p + 1 + 1) 0 h •
      (Complex.reCLM (g (x + h)) + Complex.reCLM (g (x - h)) -
        (2 : ℝ) • Complex.reCLM (g x))
  rw [map_smul, map_sub, map_add, map_smul]

theorem fractionalSchwartzTest_im (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    (fractionalSchwartzTest p g x).im = (-1 / 2 : ℝ) *
      ∫ h, fractionalSchwartzKernel (p + 1) (g.postcompCLM Complex.imCLM) x h := by
  have hi := fractionalSchwartzKernel_integrable p g x
  have hcomm : (∫ h, fractionalSchwartzKernel (p + 1) g x h).im =
      ∫ h, (fractionalSchwartzKernel (p + 1) g x h).im :=
    (Complex.imCLM.integral_comp_comm hi).symm
  unfold fractionalSchwartzTest
  rw [Complex.smul_im, smul_eq_mul, hcomm]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun h => ?_)
  change Complex.imCLM (inverseDistancePow (p + 1 + 1) 0 h •
    (g (x + h) + g (x - h) - (2 : ℝ) • g x)) =
    inverseDistancePow (p + 1 + 1) 0 h •
      (Complex.imCLM (g (x + h)) + Complex.imCLM (g (x - h)) -
        (2 : ℝ) • Complex.imCLM (g x))
  rw [map_smul, map_sub, map_add, map_smul]

theorem compact_complex_fractional_equation_of_real (p : ℕ)
    (f : Ambient (p + 1) → ℝ)
    (hreal : ∀ ψ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport ψ →
      Integrable (fun y => f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g) :
    Integrable (fun x => f x • fractionalSchwartzTest p g x) volume ∧
      (∫ x, f x • fractionalSchwartzTest p g x) = 0 := by
  let gr : 𝓢(Ambient (p + 1), ℝ) := g.postcompCLM Complex.reCLM
  let gi : 𝓢(Ambient (p + 1), ℝ) := g.postcompCLM Complex.imCLM
  have hcr : HasCompactSupport gr := hc.comp_left (g := Complex.re) rfl
  have hci : HasCompactSupport gi := hc.comp_left (g := Complex.im) rfl
  obtain ⟨hrI, hr⟩ := hreal gr hcr
  obtain ⟨hiI, hi⟩ := hreal gi hci
  have hRI : Integrable (fun x => (f x • fractionalSchwartzTest p g x).re) volume := by
    simpa only [Complex.smul_re, fractionalSchwartzTest_re] using! hrI
  have hII : Integrable (fun x => (f x • fractionalSchwartzTest p g x).im) volume := by
    simpa only [Complex.smul_im, fractionalSchwartzTest_im] using! hiI
  have hI : Integrable (fun x => f x • fractionalSchwartzTest p g x) volume :=
    Integrable.re_im_iff.mp ⟨hRI, hII⟩
  refine ⟨hI, Complex.ext ?_ ?_⟩
  · have hcomm : (∫ x, f x • fractionalSchwartzTest p g x).re =
        ∫ x, (f x • fractionalSchwartzTest p g x).re :=
      (Complex.reCLM.integral_comp_comm hI).symm
    rw [hcomm]
    simpa only [Complex.smul_re, fractionalSchwartzTest_re, Complex.zero_re] using! hr
  · have hcomm : (∫ x, f x • fractionalSchwartzTest p g x).im =
        ∫ x, (f x • fractionalSchwartzTest p g x).im :=
      (Complex.imCLM.integral_comp_comm hI).symm
    rw [hcomm]
    simpa only [Complex.smul_im, fractionalSchwartzTest_im, Complex.zero_im] using! hi

end

end RieszRectifiability

end OAI

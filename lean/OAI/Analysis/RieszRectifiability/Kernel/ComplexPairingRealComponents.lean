import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ComplexInteriorEnergy

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter

theorem complex_renormalized_normal_re {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (a : Ambient d) (q : Ambient d × Ambient d) :
    (complexRenormalizedNormalIntegrand m w g a q).re =
      renormalizedNormalIntegrand m w (fun x => (g x).re) a q := by
  unfold complexRenormalizedNormalIntegrand renormalizedNormalIntegrand
  rw [Complex.smul_re, smul_eq_mul]
  ring

theorem complex_renormalized_normal_im {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (a : Ambient d) (q : Ambient d × Ambient d) :
    (complexRenormalizedNormalIntegrand m w g a q).im =
      renormalizedNormalIntegrand m w (fun x => (g x).im) a q := by
  unfold complexRenormalizedNormalIntegrand renormalizedNormalIntegrand
  rw [Complex.smul_im, smul_eq_mul]
  ring

theorem complex_height_pairing_re {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hI : Integrable (complexHeightInteriorIntegrand m w g) ((μ.restrict s).prod (μ.restrict s)))
    (hN : Integrable (complexRenormalizedNormalIntegrand m w g a)
      ((μ.restrict s).prod (μ.restrict sᶜ))) :
    (complexHeightPairingOn m μ a s w g).re =
      heightPairingOn m μ a s w (fun x => (g x).re) := by
  have hi : (∫ q, complexHeightInteriorIntegrand m w g q ∂(μ.restrict s).prod (μ.restrict s)).re =
      ∫ q, fractionalBilinear m w (fun x => (g x).re) q.1 q.2 ∂(μ.restrict s).prod (μ.restrict s) := by
    calc
      _ = ∫ q, (complexHeightInteriorIntegrand m w g q).re ∂(μ.restrict s).prod (μ.restrict s) :=
        (Complex.reCLM.integral_comp_comm hI).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (complex_height_interior_re m w g))
  have hn : (∫ q, complexRenormalizedNormalIntegrand m w g a q
      ∂(μ.restrict s).prod (μ.restrict sᶜ)).re =
      ∫ q, renormalizedNormalIntegrand m w (fun x => (g x).re) a q
        ∂(μ.restrict s).prod (μ.restrict sᶜ) := by
    calc
      _ = ∫ q, (complexRenormalizedNormalIntegrand m w g a q).re
          ∂(μ.restrict s).prod (μ.restrict sᶜ) := (Complex.reCLM.integral_comp_comm hN).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (complex_renormalized_normal_re m w g a))
  unfold complexHeightPairingOn heightPairingOn
  rw [Complex.add_re, Complex.smul_re, hi, hn, smul_eq_mul]

theorem complex_height_pairing_im {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hI : Integrable (complexHeightInteriorIntegrand m w g) ((μ.restrict s).prod (μ.restrict s)))
    (hN : Integrable (complexRenormalizedNormalIntegrand m w g a)
      ((μ.restrict s).prod (μ.restrict sᶜ))) :
    (complexHeightPairingOn m μ a s w g).im =
      heightPairingOn m μ a s w (fun x => (g x).im) := by
  have hi : (∫ q, complexHeightInteriorIntegrand m w g q ∂(μ.restrict s).prod (μ.restrict s)).im =
      ∫ q, fractionalBilinear m w (fun x => (g x).im) q.1 q.2 ∂(μ.restrict s).prod (μ.restrict s) := by
    calc
      _ = ∫ q, (complexHeightInteriorIntegrand m w g q).im ∂(μ.restrict s).prod (μ.restrict s) :=
        (Complex.imCLM.integral_comp_comm hI).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (complex_height_interior_im m w g))
  have hn : (∫ q, complexRenormalizedNormalIntegrand m w g a q
      ∂(μ.restrict s).prod (μ.restrict sᶜ)).im =
      ∫ q, renormalizedNormalIntegrand m w (fun x => (g x).im) a q
        ∂(μ.restrict s).prod (μ.restrict sᶜ) := by
    calc
      _ = ∫ q, (complexRenormalizedNormalIntegrand m w g a q).im
          ∂(μ.restrict s).prod (μ.restrict sᶜ) := (Complex.imCLM.integral_comp_comm hN).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (complex_renormalized_normal_im m w g a))
  unfold complexHeightPairingOn heightPairingOn
  rw [Complex.add_im, Complex.smul_im, hi, hn, smul_eq_mul]

theorem complex_height_pairing_zero_of_real_equations {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hI : Integrable (complexHeightInteriorIntegrand m w g) ((μ.restrict s).prod (μ.restrict s)))
    (hN : Integrable (complexRenormalizedNormalIntegrand m w g a)
      ((μ.restrict s).prod (μ.restrict sᶜ)))
    (hr : heightPairingOn m μ a s w (fun x => (g x).re) = 0)
    (hi : heightPairingOn m μ a s w (fun x => (g x).im) = 0) :
    complexHeightPairingOn m μ a s w g = 0 := by
  apply Complex.ext
  · rw [complex_height_pairing_re m μ a s w g hI hN, hr]
    rfl
  · rw [complex_height_pairing_im m μ a s w g hI hN, hi]
    rfl

end

end RieszRectifiability

end OAI

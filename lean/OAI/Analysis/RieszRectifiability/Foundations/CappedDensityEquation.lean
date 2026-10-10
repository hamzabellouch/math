import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedDensityPairing
import OAI.Analysis.RieszRectifiability.Limits.ScalarRieszDensityLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

theorem density_riesz_test_equation_of_capped_equation (p : ℕ)
    (e a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (f : Ambient (p + 1) → ℝ) (hfm : Measurable f) (M : ℝ) (hfb : ∀ y, |f y| ≤ M)
    (g : 𝓢(Ambient (p + 1), ℝ)) (hmean : (∫ y, g y) = 0)
    (hgs : ∀ y, g y ≠ 0 → dist y a ≤ H)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hEq : Tendsto (fun j =>
      (∫ x, scalarCappedTransform (p + 1) (volume.restrict (ball a R)) e (ε j) f x * g x) +
        ∫ x, (∫ y in closedExterior a R,
          f y * inner ℝ e (kernel (p + 1) x y - kernel (p + 1) a y)) * g x) atTop (𝓝 0)) :
    Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) volume ∧
      (∫ y, f y * scalarRieszSchwartzTest (p + 1) e g y) = 0 := by
  have hlimit := scalarCappedTransform_density_integral_tendsto p _ volume
    (volume_global_upper_growth (p + 1)) e a H hH g hmean hgs f hfm M hfb ε hεpos hε
  have hsmall : ∀ᶠ j in atTop, ε j ≤ H :=
    (hε.eventually (gt_mem_nhds hH)).mono fun _ h => h.le
  have heq : (fun j =>
      (∫ x, scalarCappedTransform (p + 1) (volume.restrict (ball a R)) e (ε j) f x * g x) +
        ∫ x, (∫ y in closedExterior a R,
          f y * inner ℝ e (kernel (p + 1) x y - kernel (p + 1) a y)) * g x) =ᶠ[atTop]
      (fun j => -(∫ y, f y * scalarCappedTransform (p + 1) volume e (ε j) g y)) := by
    filter_upwards [hsmall] with j hj
    exact (local_plus_exterior_capped_density_pairing (p + 1) _ volume
      (volume_global_upper_growth (p + 1)) e a H R (ε j) hH hR hHR (hεpos j) hj
      f g hfm g.continuous.measurable M hfb g.integrable hmean hgs).2
  have hz : -(∫ y, f y * scalarRieszSchwartzTest (p + 1) e g y) = 0 :=
    tendsto_nhds_unique hlimit.2.neg (hEq.congr' heq)
  exact ⟨hlimit.1, neg_eq_zero.mp hz⟩

end

end RieszRectifiability

end OAI

import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.DensityWeakPairing
import OAI.Analysis.RieszRectifiability.Kernel.DensityRieszTransforms

namespace OAI

/-!
# Removing density weights from capped equations

A positive lower bound on a measurable density allows weak pairings for its
weighted measure to be rewritten against volume. The capped local transform
and the integrable far-field correction then converge together to the constant
pairing on compactly supported tests.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem unweighted_capped_pairing_tendsto_constant {n : ℕ} (m : ℕ) (G : ℝ)
    (f : Ambient n → ℝ) (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (hgrowth : GlobalUpperGrowth m G ((volume : Measure (Ambient n)).withDensity
      (fun x => ENNReal.ofReal (f x))))
    (e a : Ambient n) (H R b : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (ε : ℕ → ℝ) (v : Ambient n → ℝ)
    (hweak : ∀ g : Ambient n → ℝ,
      MemLp g 2 (((volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x))).restrict (ball a R)) →
      Tendsto (fun j => ∫ x in ball a R,
        scalarCappedTransform m
          (((volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y))).restrict (ball a R))
          e (ε j) (fun _ => 1) x * g x
            ∂(volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y))) atTop
        (𝓝 (∫ x in ball a R, v x * g x
          ∂(volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y)))))
    (hconstant : ∀ᵐ x ∂(volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y)),
      x ∈ ball a H → v x + scalarFarRieszTransform m
        ((volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y))) e a R x = b)
    (g : Ambient n → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B)
    (hgI : Integrable g volume) (hgs : ∀ x, g x ≠ 0 → x ∈ ball a H) :
    Tendsto (fun j =>
      (∫ x, scalarCappedTransform m (volume.restrict (ball a R)) e (ε j) f x * g x) +
        ∫ x, (∫ y in closedExterior a R, f y * inner ℝ e (kernel m x y - kernel m a y)) * g x)
      atTop (𝓝 (b * ∫ x, g x)) := by
  let ρ : Measure (Ambient n) := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let := finiteMeasure_restrict_ball_of_globalGrowth m G ρ hgrowth a R hR
  have hpos : ∀ x, 0 < f x := fun x => hc.trans_le (hlower x)
  have hFI := scalarFarRieszTransform_mul_test_integrable m G ρ hgrowth volume e a H R
    hR hHR g hg hgI (fun x hx => (hgs x hx).le)
  have h := weak_L2_pairings_cancel_density_add_correction volume f hf (ball a R)
    measurableSet_ball c hc hlower
    (fun j => scalarCappedTransform m (ρ.restrict (ball a R)) e (ε j) (fun _ => 1)) v hweak
    (scalarFarRieszTransform m ρ e a R) (ball a H) b hconstant g hg B hB hgs hgI.restrict hFI.restrict
  have hgzero : ∀ x ∉ ball a R, g x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hgs x hn).trans (by linarith : H < R))
  have hlocal (F : Ambient n → ℝ) : (∫ x in ball a R, F x * g x) = ∫ x, F x * g x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hgzero x hx, mul_zero]
  have hmean : (∫ x in ball a R, g x) = ∫ x, g x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hgzero
  simpa only [ρ, scalarCappedTransform_withDensity m volume f hf hpos (ball a R) measurableSet_ball,
    scalarFarRieszTransform_withDensity m volume f hf hpos, hlocal, hmean] using! h

end

end RieszRectifiability

end OAI

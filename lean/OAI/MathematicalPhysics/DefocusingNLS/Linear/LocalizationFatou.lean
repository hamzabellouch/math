import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevWeights
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Passing the localization energy bound to a Fourier-series limit

Fatou's lemma applies to the nonnegative Fourier energy densities indexed by
finite frequency sets. A uniform bound gives integrability of the limit as
well as the same numerical energy bound.
-/

open Filter MeasureTheory Topology

namespace DefocusingNLS

theorem localization_integral_limit
    (F : Finset frequencyLattice → EuclideanSpace ℝ (Fin 12) → ℝ)
    (f : EuclideanSpace ℝ (Fin 12) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hFI : ∀ S, Integrable (F S))
    (hFn : ∀ S x, 0 ≤ F S x) (hfn : ∀ x, 0 ≤ f x)
    (hlim : ∀ x, Tendsto (fun S => F S x) atTop (𝓝 (f x)))
    (hbound : ∀ S, (∫ x, F S x) ≤ C) :
    Integrable f ∧ (∫ x, f x) ≤ C := by
  have hm : AEStronglyMeasurable f := aestronglyMeasurable_of_tendsto_ae atTop
    (fun S => (hFI S).aestronglyMeasurable) (Eventually.of_forall hlim)
  have hlimE (x) : Tendsto (fun S => ENNReal.ofReal (F S x)) atTop (𝓝 (ENNReal.ofReal (f x))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim x)
  have hFatou : (∫⁻ x, ENNReal.ofReal (f x)) ≤
      liminf (fun S => ∫⁻ x, ENNReal.ofReal (F S x)) atTop := by
    convert lintegral_liminf_le' (u := (atTop : Filter (Finset frequencyLattice))) (fun S =>
      (hFI S).aestronglyMeasurable.aemeasurable.ennreal_ofReal) using 1
    apply lintegral_congr
    intro x
    exact (hlimE x).liminf_eq.symm
  have hlimbound : liminf (fun S => ∫⁻ x, ENNReal.ofReal (F S x)) atTop ≤ ENNReal.ofReal C := by
    have hb (S : Finset frequencyLattice) : (∫⁻ x, ENNReal.ofReal (F S x)) ≤ ENNReal.ofReal C := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hFI S) (Eventually.of_forall (hFn S))]
      exact ENNReal.ofReal_le_ofReal (hbound S)
    simpa only [liminf_const] using
      liminf_le_liminf (f := (atTop : Filter (Finset frequencyLattice))) (Eventually.of_forall hb)
  have hL := hFatou.trans hlimbound
  have hI : Integrable f :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hm (Eventually.of_forall hfn)).mp
      (ne_of_lt (hL.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hI, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hfn)] at hL
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hL
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hfn), ENNReal.toReal_ofReal hC] using hreal

end DefocusingNLS

end OAI

import OAI.Analysis.KadisonKastler.GaussianStateKernel
import OAI.Analysis.KadisonKastler.RegularWeightedIntegral
import OAI.Analysis.KadisonKastler.RegularCoreIntersection

namespace OAI

/-! # Gaussian averages of strongly continuous algebra actions -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def stateActionOrbit (a : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  unitaryConj (U (Multiplicative.ofAdd t)) a

include hU in
theorem stateActionOrbit_continuous (a : H →L[ℂ] H) (x : H) :
    Continuous (fun t => stateActionOrbit U a t x) := by
  have hs (y : H) : Continuous (fun t : ℝ =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) y) := by
    simp_rw [← Unitary.coe_star, regularGroup_star_eq]
    exact (hU y).comp continuous_neg
  exact continuous_unitary_field_apply _ hU _ (a.continuous.comp (hs x))

theorem stateActionOrbit_norm (a : H →L[ℂ] H) (t : ℝ) :
    ‖stateActionOrbit U a t‖ = ‖a‖ := norm_unitaryConj _ _

def gaussianStateAverage (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) : H →L[ℂ] H :=
  weightedOperatorIntegral volume (gaussianStateKernel r z) (gaussianStateKernel_integrable hr z)
    (stateActionOrbit U a) (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Filter.Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)

theorem gaussianStateAverage_norm (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    ‖gaussianStateAverage U hU a r hr z‖ ≤
      Real.exp (r * z.im ^ 2) * Real.sqrt (Real.pi / r) * ‖a‖ := by
  have h := norm_weightedOperatorIntegral_le volume (gaussianStateKernel r z)
    (gaussianStateKernel_integrable hr z) (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (norm_nonneg a) (Filter.Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)
  rw [gaussianStateKernel_norm_integral] at h
  exact h

theorem gaussianStateAverage_mem (M : VonNeumannAlgebra H)
    (hnormal : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (a : H →L[ℂ] H) (ha : a ∈ M) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    gaussianStateAverage U hU a r hr z ∈ M :=
  weightedOperatorIntegral_mem volume (gaussianStateKernel r z) (gaussianStateKernel_integrable hr z)
    (stateActionOrbit U a) (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Filter.Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) M
    (Filter.Eventually.of_forall fun _ => hnormal _ _ ha)

end

end KadisonKastler

end OAI

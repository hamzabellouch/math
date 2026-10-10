import OAI.Analysis.ModularTheory.KernelIdentification
import OAI.Analysis.OperatorAlgebra.GaussianConvolutionApproximation
import OAI.Analysis.OperatorAlgebra.VonNeumannWeakConvergence
import OAI.Analysis.ModularTheory.FixedPointExpectation

namespace OAI

/-! Identification of the modular right-action fixed points with the
actual crossed product, and the resulting concrete cpc core retraction. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem convolutionSmoothed_mem_core (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hM : T ∈ amplifiedModularAlgebra volume S)
    (hT : ∀ s f, T (modularRightTranslation volume S.D s f) =
      modularRightTranslation volume S.D s (T f))
    (f g : Lp ℂ 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → ℂ)) (hg : Integrable (g : ℝ → ℂ)) :
    convolutionSmoothedOperator T f g hf hg ∈ modularCrossedProduct volume S := by
  let X := convolutionSmoothedOperator T f g hf hg
  have hX (n : ℕ) : modularDualGaussianAverage X n ∈ modularCrossedProduct volume S := by
    rw [← modularKernelRegularization_eq_dualAverage S T hT f g hf hg n]
    exact modularKernelRegularization_mem S T hM f g _ _
  rw [← (modularCrossedProduct volume S).commutant_commutant,
    VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  exact (commute_of_strong_limit b X (fun n => modularDualGaussianAverage X n)
    (fun n => (VonNeumannAlgebra.mem_commutant_iff.mp hb _ (hX n)).symm)
    (modularDualGaussianAverage_strong X)).eq

theorem modular_fixedPoint_mem_core (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hM : T ∈ amplifiedModularAlgebra volume S)
    (hT : ∀ s f, T (modularRightTranslation volume S.D s f) =
      modularRightTranslation volume S.D s (T f)) :
    T ∈ modularCrossedProduct volume S := by
  let C := fun n => integratedModularTranslation (H := H) (gaussianConvolutionVector n)
    (gaussianConvolutionVector_integrable n)
  apply vonNeumann_mem_of_sandwiches (modularCrossedProduct volume S) C
    gaussianConvolutionVector_strong T
  intro n
  exact convolutionSmoothed_mem_core S T hM hT _ _
    (gaussianConvolutionVector_integrable n) (gaussianConvolutionVector_integrable n)

theorem modular_mem_core_iff (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    T ∈ modularCrossedProduct volume S ↔ T ∈ amplifiedModularAlgebra volume S ∧
      ∀ s f, T (modularRightTranslation volume S.D s f) =
        modularRightTranslation volume S.D s (T f) := by
  constructor
  · intro hT
    exact ⟨modularCore_mem_amplification volume S T hT, modularCore_fixed_right volume S T hT⟩
  · rintro ⟨hM, hT⟩
    exact modular_fixedPoint_mem_core S T hM hT

open KirchbergRordam.GenericRW.GroupedFactors

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

theorem nuclear_quotient_modular_core_expectation
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : BoundedRecovery.StandardModularData H)
    (hS : S.M = bicommutant π.range) :
    ∃ Q : (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) →L[ℂ]
        (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)),
      CompletelyPositive Q ∧ ‖Q‖ ≤ 1 ∧
      (∀ T, Q T ∈ modularCrossedProduct volume S) ∧
      (∀ T, T ∈ modularCrossedProduct volume S → Q T = T) := by
  obtain ⟨Q, hQ, hQn, hQM, hQc, hQf⟩ :=
    nuclear_quotient_modular_fixedPoint_expectation ω hω hA q hq π S hS
  exact ⟨Q, hQ, hQn, fun T => modular_fixedPoint_mem_core S (Q T) (hQM T) (hQc T), hQf⟩

end WeakPureInfiniteness

end

end OAI

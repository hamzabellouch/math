import OAI.MathematicalPhysics.Boltzmann.Collision.KernelInvariantPowers
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

namespace OAI

/-! # Almost-everywhere kernel comparison suffices below an occupation measure -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.KernelHistoryOrder

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem measure_comp_mono_ae {K L : Kernel X Y} {μ ν : Measure X}
    (hK : ∀ᵐ x ∂μ, K x ≤ L x) (hμ : μ ≤ ν) : K ∘ₘ μ ≤ L ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA K.aemeasurable,Measure.bind_apply hA L.aemeasurable]
  apply (lintegral_mono_ae ?_).trans (lintegral_mono' hμ le_rfl)
  filter_upwards [hK] with x hx
  exact hx A

theorem measure_comp_mono_ae_of_le {K L : Kernel X Y} {μ ν ξ : Measure X}
    (hK : ∀ᵐ x ∂ξ, K x ≤ L x) (hμξ : μ ≤ ξ) (hμν : μ ≤ ν) :
    K ∘ₘ μ ≤ L ∘ₘ ν :=
  measure_comp_mono_ae (hμξ.absolutelyContinuous.ae_le hK) hμν

end BoltzmannNonuniqueness.KernelHistoryOrder

namespace BoltzmannNonuniqueness.PositiveMeasureHistories

variable {X : Type*} [MeasurableSpace X]

theorem restricted_source_renewal_ae (K L R : Kernel X X)
    {occupation source seed : Measure X} {A : Set X} (hA : MeasurableSet A)
    (hoccupation : occupation.restrict A = R ∘ₘ (seed+source.restrict A))
    (hKL : ∀ᵐ x ∂occupation, K x ≤ L x)
    (hsource : L ∘ₘ occupation ≤ source) :
    seed+((K.restrict hA) ∘ₖ R) ∘ₘ (seed+source.restrict A) ≤ seed+source.restrict A := by
  apply restricted_source_renewal K R hA hoccupation
  exact (KernelHistoryOrder.measure_comp_mono_ae hKL le_rfl).trans hsource

theorem finite_occupation_histories_ae (K L R : Kernel X X)
    {occupation source seed : Measure X} {A : Set X} (hA : MeasurableSet A)
    (hoccupation : occupation.restrict A = R ∘ₘ (seed+source.restrict A))
    (hKL : ∀ᵐ x ∂occupation, K x ≤ L x)
    (hsource : L ∘ₘ occupation ≤ source) (n : ℕ) :
    R ∘ₘ (∑ j ∈ Finset.range n, (((K.restrict hA) ∘ₖ R)^j) ∘ₘ seed) ≤
      occupation.restrict A := by
  rw [hoccupation]
  exact endpoint_histories_le _ R
    (restricted_source_renewal_ae K L R hA hoccupation hKL hsource) n

end BoltzmannNonuniqueness.PositiveMeasureHistories

end

end OAI

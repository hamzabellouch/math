import OAI.NumberTheory.CubicMoment.Estimates.UniformHighStoppedTail
import OAI.NumberTheory.CubicMoment.Estimates.UpperTailGeometry
import OAI.NumberTheory.CubicMoment.Estimates.UpperStoppedRange
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionEnvelope

namespace OAI

/-! The literal upper stopped dyad has arbitrary logarithmic saving.
Its stopping exponent is fixed before arities and logarithmic losses. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

lemma angular_upperTailStoppedDyads_envelope (i : ℕ) (κ ρ ξ H T : ℝ)
    {X : ℝ} (hX : 0 < X)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      upperTailStoppedDyad i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d q j k) =
      envelopeCutoffBilinearTail (stoppedNormDyad (distinguishedStoppedSide X) j)
        (stoppedNormDyad (distinguishedStoppedSide X) k)
        (fun a => theta ℓ a*distinguishedStoppedAlpha ρ ξ X q a)
        (fun b => theta ℓ b*upperStoppedBeta i κ ρ ξ X d q b)
        primeProductEnvelope H T X := by
  unfold envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro s _
  unfold upperTailStoppedDyad
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hpa := (distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1).1
  have hpb := (distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1).1
  rw [scaleFirstTailKernel_indicator ℓ H _ hX (primary_mul hpa hpb)]
  simp only [scaleFirstTailKernel,theta_mul]
  ring

end CubicFirstMoment

end

end OAI

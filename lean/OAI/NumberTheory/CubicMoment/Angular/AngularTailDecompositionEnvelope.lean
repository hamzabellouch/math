import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionEnvelope

namespace OAI

/-! Angular coefficient transfer in the original stopped product envelope. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_scaleFirstTailStoppedDyads_envelope (i : ℕ) (ρ ξ H T : ℝ) {X : ℝ} (hX : 0 < X)
    (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstTailStoppedDyad i ℓ ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k) =
      envelopeCutoffBilinearTail (stoppedNormDyad (distinguishedStoppedSide X) j)
        (stoppedNormDyad (distinguishedStoppedSide X) k)
        (fun a => theta ℓ a*distinguishedStoppedAlpha ρ ξ X q a)
        (fun b => theta ℓ b*distinguishedStoppedBeta i ρ ξ X h early d q b) primeProductEnvelope H T X := by
  unfold envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro s _
  unfold scaleFirstTailStoppedDyad
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

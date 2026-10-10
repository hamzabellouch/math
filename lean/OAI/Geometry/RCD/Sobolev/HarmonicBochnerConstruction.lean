import OAI.Geometry.RCD.Sobolev.DirectionalGradientBound
import OAI.Geometry.RCD.Heat.HarmonicBochnerHeat
import OAI.Geometry.RCD.Sobolev.HarmonicBochnerMass

namespace OAI

/-! # Constructing the Bochner family of an actual first-order splitting map -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A uniform bound for all constant directions of the splitting map. -/
def splittingDirectionBound (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) : ℝ≥0 :=
  ⟨(n : ℝ) * (1 + ε), mul_nonneg (Nat.cast_nonneg _) (by linarith)⟩

/-- Local calculus for the harmonic map gives a positive finite measure
family satisfying the heat and mass identities. -/
theorem FirstOrderSplittingOn.local_bochner {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hpublished : LocalHarmonicBochnerInput hX)
    {κ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K) {p : X} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε)
    {u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic} {w : X → Euclidean n}
    (h : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (8 * r) ε u w) :
    ∃ M : PositiveBilinearMeasure X (Euclidean n),
      ∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u) M κ p r
        (splittingDirectionBound n ε hε) v) := by
  apply hpublished κ hκ hK p r hr (splittingDirectionBound n ε hε)
    (sobolevColumnMap (hausdorff n X) hX.quadratic u)
  · intro v
    exact IsSobolevHarmonicOn.linearCombination (hausdorff n X) hX.quadratic h.harmonic v
  · intro v
    exact h.directional_gradient (hausdorff n X) hX.quadratic v

end RegularPointCoordinates

end

end OAI

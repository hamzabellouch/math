import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialOperations

namespace OAI

/-! # The zero-width quotient has subexponential Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter
open scoped Manifold Topology ENNReal

/-- The actual nilpotent exponential chart gives finite quotient log boxes
with subexponential volume whenever their radii are subexponential. -/
theorem exists_haar_subexponential_quotient_boxes
    {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
    [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [SimplyConnectedSpace Q]
    [MeasurableSpace Q] [BorelSpace Q]
    (haar : NilpotentExponentialHaarInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    {n : ℕ} (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q)) :
    ∃ μ : Measure Q, μ.IsHaarMeasure ∧ ∀ R : ℝ → ℝ,
      (∀ r, 0 ≤ R r) → HasSubexponentialUpperBound R →
      (∀ r, μ (exponentialCoordinateBox Exp b (R r)) ≠ ⊤) ∧
      HasSubexponentialUpperBound (fun r =>
        (μ (exponentialCoordinateBox Exp b (R r))).toReal) := by
  obtain ⟨_, μ, _, hμ, hvol⟩ := exists_haar_exponential_cube_volume haar Exp hExp hnil b
  refine ⟨μ, hμ, ?_⟩
  intro R hR0 hR
  constructor
  · intro r
    rw [hvol _ (hR0 r)]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · have htwo : HasSubexponentialUpperBound (fun r => 2 * R r) :=
      (subexponential_upper_const 2).mul hR (Eventually.of_forall (fun _ => by norm_num))
    have hp := htwo.pow (Eventually.of_forall (fun r => mul_nonneg (by norm_num) (hR0 r))) n
    intro ε hε
    filter_upwards [hp ε hε] with r hr
    rw [hvol _ (hR0 r), ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (show 0 ≤ 2 * R r from mul_nonneg (by norm_num) (hR0 r))]
    exact hr

end PolycyclicRecognition

end

end OAI

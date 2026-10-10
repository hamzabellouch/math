import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordLogarithms
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceQuotientVolume

namespace OAI

/-! # The Cartan log restriction has subexponential Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule MeasureTheory Set Filter
open scoped Manifold Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace D] [ChartedSpace E D] [Group D]
  [LieGroup (𝓘(ℝ, E)) ⊤ D] [T2Space D] [SimplyConnectedSpace D]
  [MeasurableSpace D] [BorelSpace D]

/-- The coordinate restriction produced by the actual path lifts is an
exponential box. Its volume is finite and subexponential in any Haar
normalization, with no separate volume hypothesis. -/
theorem cartan_log_regions_volume
    (haar : NilpotentExponentialHaarInput E D)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) D → D) (hExp : IsGroupExponential Exp)
    (e : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) D) (hbij : Function.Bijective Exp)
    (μ : Measure D) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let B := fun n => {d : D | ‖(finBasis ℝ H).equivFun (cartanLog H e Exp hbij d)‖ ≤ R n}
    (∀ n, μ (B n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (μ (B n)).toReal) := by
  have hnil : LieRing.IsNilpotent H := by infer_instance
  have hbox (n : ℕ) :
      {d : D | ‖(finBasis ℝ H).equivFun (cartanLog H e Exp hbij d)‖ ≤ R n} =
        exponentialCoordinateBox (Exp ∘ e) (finBasis ℝ H) (R n) := by
    ext d
    constructor
    · intro hd
      exact ⟨cartanLog H e Exp hbij d, exp_cartanLog H e Exp hbij d, hd⟩
    · rintro ⟨v, rfl, hv⟩
      change ‖(finBasis ℝ H).equivFun (cartanLog H e Exp hbij (Exp (e v)))‖ ≤ R n
      rw [cartanLog_exp]
      exact hv
  simpa only [hbox] using
    haar_model_sequence_boxes haar Exp hExp e hnil (finBasis ℝ H) μ scale R hs hR0 hR

end PolycyclicRecognition

end

end OAI

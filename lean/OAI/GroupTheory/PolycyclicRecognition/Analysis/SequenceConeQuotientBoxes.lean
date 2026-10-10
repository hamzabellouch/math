import OAI.GroupTheory.PolycyclicRecognition.Analysis.ZeroWidthQuotientBoxes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceQuotientVolume

namespace OAI

/-! # A common finite-volume quotient envelope for first-sheet paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory Set Filter
open scoped Manifold Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

/-- The actual cone quotient sends all first-sheet boxes, at every scale
and in every selected word basis, into one common sequence of quotient
log boxes of subexponential Haar volume. The measure can be the one already
chosen for the quotient Jacobian. -/
theorem exists_sequence_cone_quotient_envelope
    {N : Type*} [Group N] (ExpN : cartanRootIdeal H → N)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (π : N →* Q.carrier)
    (hπ : ∀ v, π (ExpN v) = ExpQ (Q.equiv (M.coneProjection C v)))
    {k : ℕ} (bQ : Basis (Fin k) ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (μ : Measure Q.carrier) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ T : ℕ → Set Q.carrier,
      (∀ n, μ (T n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (μ (T n)).toReal) ∧
      ∀ n (β : M.Bases) (s : Fin M.letterCount → ℝ),
        (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → s i = 0) →
        π '' exponentialCoordinateBox ExpN
          (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
            (fun j => bracketWordExponent s (β.val j)) (scale n)) (R n) ⊆ T n := by
  obtain ⟨A, hA, hbound⟩ := M.exists_cone_quotient_box_bound C ExpN
    (ExpQ ∘ Q.equiv) π hπ bQ
  let RQ := fun n => A * R n
  have hRQ0 : ∀ n, 0 ≤ RQ n := fun n => mul_nonneg hA (hR0 n)
  have hRQ : HasSubexponentialUpperBoundSeq scale RQ :=
    (sequence_subexponential_upper_const hs A).mul hR
      (Eventually.of_forall (fun _ => hA))
  obtain ⟨hfinite, hvol⟩ := haar_model_sequence_boxes haar ExpQ hExpQ Q.equiv
    (M.coneQuotient_nilpotent C) bQ μ scale RQ hs hRQ0 hRQ
  exact ⟨fun n => exponentialCoordinateBox (ExpQ ∘ Q.equiv) bQ (RQ n),
    hfinite, hvol, fun n β s hz => hbound β s hz (scale n) (R n)⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI

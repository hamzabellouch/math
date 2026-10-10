import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixFutureMass
import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingFutureInformation

namespace OAI

/-! # Integrating the exact whole-future information in a root box

The result retains the restriction to the actual box range. It is not a
replacement of that restricted integral by the global canonical mean.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

/-- Integrability and the exact ambient restricted integral follow from
positive finite future mass and the local conditional probability formula. -/
theorem wholeFuture_conditionalInformation_integrable_integral
    (B : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (hQ : Measurable Q)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k] x))
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP₀ hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP₀ hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1)
    (hcontained : ∀ᵐ z ∂B.coordinateMeasure μ,
      countableFutureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
        Q (C.timeParam c hP₀ hf g) z ⊆ B.time) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP₀ hf g
    let J := conditionalInformation (B.coordinateMeasure μ) (Q ∘ F)
      (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z)))
    let I := fun x => -Real.log
      (c.remainingTimeProduct hP₀ hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
        c.remainingTimeProduct hP₀ hf μ x (c.remainingFutureAtom ell hell Q 1 x)).toReal
    Integrable J (B.coordinateMeasure μ) ∧
      (∫ z, J z ∂B.coordinateMeasure μ) = ∫ x in B.range, I x ∂μ := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := C.timeParam c hP₀ hf g
  let J := conditionalInformation (B.coordinateMeasure μ) (Q ∘ F)
    (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z)))
  let I := fun x => -Real.log
    (c.remainingTimeProduct hP₀ hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
      c.remainingTimeProduct hP₀ hf μ x (c.remainingFutureAtom ell hell Q 1 x)).toReal
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hI : Integrable I μ :=
    (c.remainingFutureInformation_integrable_integral d hP₀ hf μ hA ell hell Q hQ hmass).1
  have heq : J =ᵐ[B.coordinateMeasure μ] I ∘ F := by
    simpa only [J, I, T, F, Function.comp_def, ENNReal.toReal_div, Measure.real] using
      B.conditionalInformation_eq_wholeFuture_ratio R hBR μ ell hell Q hQ hgood hcontained
  have hi := hI.mono_measure (Measure.restrict_le_self : μ.restrict B.range ≤ μ)
  rw [←B.map_coordinateMeasure μ] at hi
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable
  refine ⟨(hi.comp_measurable hF).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  have H := integral_map hF.aemeasurable hi.aestronglyMeasurable
  rw [B.map_coordinateMeasure μ] at H
  exact H.symm

end RootPrefixBox
end DukePrimeDegree

end

end OAI

import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureBlockConditionalInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteFactorInformation

namespace OAI

/-! # Finite word entropy under the actual delayed root conditional -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem delayedFuture_clippedWord_entropy_le
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q 1 x)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1)
    (N L : ℕ) :
    let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
    let K := delayedFutureKernel κ (diagonalOneParameter ell hell (-1)) N
    conditionalSigmaEntropy μ (orbitName T (heightClip Q L) (N+1))
      (MeasurableSpace.comap K inferInstance) ≤ (N+1 : ℝ) *
        ∑ p : ↥(allPositiveRoots (d+1) \ P),
          (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
  let K := delayedFutureKernel κ (diagonalOneParameter ell hell (-1)) N
  let W := orbitName T Q (N+1)
  let f : (Fin (N+1) → ℕ) → (Fin (N+1) → Fin (L+1)) :=
    fun w i => heightClip id L (w i)
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hW : Measurable W := measurable_pi_iff.mpr fun i => hQ.comp (hT.iterate i.val)
  have hfm : Measurable f := measurable_pi_iff.mpr fun i =>
    (heightClip_measurable measurable_id L).comp (measurable_pi_apply i)
  have hK := delayedFutureKernel_spec d c hP hf μ hA ell hell Q κ hstat hself hversion N
  have hp := c.futureBlock_conditionalProbability d hP hf μ ell hell Q hQ K
    hK.1 hK.2.1 (N+1) hK.2.2
  have hm := c.ae_all_futureMass_pos_ne_top d hP hf μ hA ell hell Q hQ hmass
  have hpos : ∀ᵐ x ∂μ, 0 < (μ[({y | W y=W x}.indicator (fun _ => (1 : ℝ))) |
      MeasurableSpace.comap K inferInstance]) x := by
    filter_upwards [hp,hm] with x hx hm
    rw [hx,ENNReal.toReal_div]
    exact div_pos (ENNReal.toReal_pos (hm 0).1.ne' (hm 0).2)
      (ENNReal.toReal_pos (hm (N+1)).1.ne' (hm (N+1)).2)
  have HI := delayedFuture_conditionalInformation_integrable_integral d c hP hf μ hA
    ell hell Q hQ κ hstat hself hversion hmass N
  have H := finiteFactor_conditionalEntropy_le_information
    (MeasurableSpace.comap K inferInstance) μ W hW f hfm K.measurable.comap_le hpos HI.1
  change conditionalSigmaEntropy μ (f ∘ W) (MeasurableSpace.comap K inferInstance) ≤ _
  exact H.trans_eq HI.2

end DukePrimeDegree

end

end OAI

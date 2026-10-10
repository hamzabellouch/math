import OAI.Analysis.KadisonKastler.NormalTracialSpatialSplit
import OAI.Analysis.KadisonKastler.ConcreteTraceHilbert
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

/-! # Spatial splitting for every represented type II₁ commutant

The canonical trace representation removes the need for a trace vector
in the original Hilbert space. No separability assumption is used.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_split_of_II1_commutant
    (M : VonNeumannAlgebra H) (hN : IsII1Factor M.commutant.toStarSubalgebra)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  let hf := traceHilbert_factor hN
  let hu := traceHilbert_nonzero hN
  let P := traceFreeHilbertClosure hf hN.diffuse hN.finite hu
  let e := traceFreeHilbertEquiv hf hN.diffuse hN.finite hu
  let τ : TracialRepresentation P := traceFreeHilbertClosureTrace hf hN.diffuse hN.finite hu
  apply exists_selfAdjoint_split_of_normal_tracial_commutant M P e τ _ T hTsa hT
  intro C
  exact traceFreeHilbertBallMap_continuous hf hN.diffuse hN.finite hu C

end

end KadisonKastler

end OAI

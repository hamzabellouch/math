import OAI.Combinatorics.BalancedRyser.Candidates.FreshExternalCountBound

namespace OAI

noncomputable section
open scoped BigOperators
open _root_.Balanced _root_.OAI.Balanced MeasureTheory

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable [MeasurableSpace F] [MeasurableSingletonClass F]

example (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (((ExternalAssembly.witnesses g M).filter
      (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card : ℝ)
      ∂(CandidateExposure.exposedLaw D a).toMeasure) ≤
      (5242880 * (m + 1)^4 : ℝ) :=
  FreshExternalWitness.canonical_fresh_count_integral_le g D a m hD

example (g : Direction F) (a : MergedPairs F) :
    (∫ M, ((ExternalAssembly.witnesses g M).card : ℝ)
      ∂(CandidateExposure.exposedLaw ∅ a).toMeasure) ≤ (5242880 : ℝ) := by
  simpa using FreshExternalWitness.canonical_fresh_count_integral_le g ∅ a 0 (by simp)

end

end OAI

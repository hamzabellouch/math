import OAI.Combinatorics.BalancedRyser.Candidates.ExternalFreshGeneratorBound

namespace OAI

namespace Balanced.ExternalAssembly
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

example (D : Finset (Direction F)) (a : MergedPairs F) :
    CandidateExposure.exposedLaw D a = FreshWitnessProbability.exposedLaw D a := by
  rfl

example (g : Direction F) (T : FourTuple F) (i : Fin 4) (d e : Direction F) :
    witnessEvent g ((T, (i, i)), (d, e)) = ∅ := by
  ext M
  simp [witnessEvent]

example (g : Direction F) (T : FourTuple F) (i j : Fin 4) (d : Direction F) :
    witnessEvent g ((T, (i, j)), (d, d)) = ∅ := by
  ext M
  simp [witnessEvent]

example (g : Direction F) (M : MergedPairs F) :
    ((witnesses g M).filter (fun w =>
      (∀ i, w.1.1.generator i ∉ (∅ : Finset (Direction F))) ∧
      w.2.1 ∈ (∅ : Finset (Direction F)))).card = 0 := by
  simp

end
end Balanced.ExternalAssembly

end OAI

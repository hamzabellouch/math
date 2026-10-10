import OAI.Combinatorics.BalancedRyser.Probability.ConditionalMultiplicity

namespace OAI

noncomputable section
open scoped Classical
open _root_.Balanced _root_.OAI.Balanced Balanced.CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

example (M : MergedPairs F) (p : Point F) :
    exposedMultiplicity ∅ M p = 0 := by
  simp [exposedMultiplicity]

example (M : MergedPairs F) (p : Point F) :
    freshMultiplicity Finset.univ M p = 0 := by
  let : IsEmpty {d : Direction F // d ∉ (Finset.univ : Finset (Direction F))} :=
    ⟨fun d => d.2 (Finset.mem_univ _)⟩
  simp [freshMultiplicity]

example (M : MergedPairs F) (p : Point F) :
    freshMultiplicity ∅ M p = sampledMultiplicity M p := by
  have h := sampledMultiplicity_eq_exposed_add_fresh ∅ M p
  simpa [exposedMultiplicity] using h.symm

example (a : MergedPairs F) (p : Point F) :
    conditionalProbability Finset.univ a
      {M | sampledMultiplicity M p = sampledMultiplicity a p} = 1 := by
  let : IsEmpty {d : Direction F // d ∉ (Finset.univ : Finset (Direction F))} :=
    ⟨fun d => d.2 (Finset.mem_univ _)⟩
  have hsplit := sampledMultiplicity_eq_exposed_add_fresh Finset.univ a p
  have hfixed : exposedMultiplicity Finset.univ a p = sampledMultiplicity a p := by
    simpa [freshMultiplicity] using hsplit.symm
  simpa [Direction, hfixed] using
    sampledMultiplicity_conditional_atom Finset.univ a p 0

example (D : Finset (Direction F)) (a : MergedPairs F) (p : Point F)
    (n : ℕ) (hn : n < exposedMultiplicity D a p) :
    conditionalProbability D a {M | sampledMultiplicity M p = n} = 0 := by
  unfold conditionalProbability
  have hz : (exposedLaw D a).toOuterMeasure
      {M | sampledMultiplicity M p = n} = 0 := by
    apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
    apply Set.disjoint_left.mpr
    intro M hM he
    have hsplit := sampledMultiplicity_eq_fixed_add_fresh D a M p hM
    change sampledMultiplicity M p = n at he
    omega
  rw [hz, ENNReal.toReal_zero]

end

end OAI

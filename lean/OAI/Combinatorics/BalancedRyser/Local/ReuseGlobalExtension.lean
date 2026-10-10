import OAI.Combinatorics.BalancedRyser.Local.GlobalPartialAlignment
import OAI.Combinatorics.BalancedRyser.Local.ReuseExtensionSum

namespace OAI

namespace Balanced
open scoped _root_.Balanced
open PartialAlignment TupleAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem global_external_alignment_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (p : Point F) (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
      (canonical_exposure_supported old a)).toOuterMeasure
      {M | (∀ i, OnLine (tuplePoint M T i) (lineThrough g p)) ∧
        ∀ i, tuplePoint M T i ≠ p}).toReal =
      externalAlignmentProbability T.generator (adjacent_ne_of_injective T hT)
        T.side p g (oldGeneratorIndices T old) (fun i => a (T.generator i)) := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Bool → F) :=
    {o | (∀ i, OnLine (tuplePositionEquiv T.generator hd T.side o i) (lineThrough g p)) ∧
      ∀ i, tuplePositionEquiv T.generator hd T.side o i ≠ p}
  have h := congrArg (fun law => (law.toOuterMeasure E).toReal)
    (global_exposed_tuple_law T hT old a)
  have hJ : exposedTupleIndices T old = oldGeneratorIndices T old := by
    ext i
    simp [exposedTupleIndices, oldGeneratorIndices]
  rw [hJ] at h
  rw [partialOffsets_conditional_law, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply] at h
  simp only [E, Set.preimage_ofPred_eq, tuplePositionEquiv_apply] at h
  simp only [offsetLaw_eq_uniform, externalAlignmentProbability,
    externalAlignmentEvent, tuplePositionEquiv_apply, tuplePoint, constituent]
  exact h

def globalTupleCodeTargetMass (old : Finset (Direction F)) (a : MergedPairs F)
    (p : Point F) (c : (Fin 4 → Direction F) × (Fin 4 → Bool)) : ℝ :=
  if Function.Injective c.1 then
    ∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, c.1 i ≠ g)),
      (((offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
        (canonical_exposure_supported old a)).toOuterMeasure
        {M | (∀ i, OnLine (tuplePoint M ⟨c.1, c.2⟩ i) (lineThrough g p)) ∧
          ∀ i, tuplePoint M ⟨c.1, c.2⟩ i ≠ p}).toReal
  else 0

theorem globalTupleCodeTargetMass_eq (old : Finset (Direction F))
    (a : MergedPairs F) (p : Point F)
    (c : (Fin 4 → Direction F) × (Fin 4 → Bool)) :
    globalTupleCodeTargetMass old a p c = tupleCodeTargetMass old a p c := by
  unfold globalTupleCodeTargetMass tupleCodeTargetMass
  split_ifs with hinj
  · apply Finset.sum_congr rfl
    intro g _
    exact global_external_alignment_probability_eq ⟨c.1, c.2⟩ hinj p g old a
  · rfl

theorem sum_globalTupleCodeTargetMass_extension_le (old : Finset (Direction F))
    (a : MergedPairs F) (p : Point F) (j : ℕ)
    (hold : old.card ≤ 24) (hj : j ≤ 4) (K : ℝ) (hK : 0 ≤ K) :
    2 * (∑ c ∈ tupleCodesWithOldCount old j,
      globalTupleCodeTargetMass old a p c * (K / Fintype.card F)) ≤
      (4 * (4096 * 24 ^ 4) : ℝ) * K /
        (Fintype.card F : ℝ) ^ reuseSaving j := by
  simp_rw [globalTupleCodeTargetMass_eq]
  exact sum_tupleCodeTargetMass_extension_le old a p j hold hj K hK

end
end Balanced

end OAI

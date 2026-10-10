import OAI.Combinatorics.BalancedRyser.Local.AlignedUnusedLaw
import OAI.Combinatorics.BalancedRyser.Local.LocalFourEventProbability
import OAI.Combinatorics.BalancedRyser.Local.LocalUnusedTripleProbability

namespace OAI

noncomputable section
open scoped Classical

namespace Balanced.Local.UnusedTripleProbability

open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def unusedArrayEquiv (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) :
    AlignedUnused.UnusedArray P a ≃
      UnusedOffsetIncidence.Offsets (unusedDirections a) where
  toFun v d := v ⟨d.1, (mem_unusedDirections d.1).mp d.2⟩
  invFun o d := o ⟨d.1, (mem_unusedDirections d.1).mpr d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem conditioned_unusedNoncollinearTriple_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    conditionedOffsetProbability (Aligned P a bits p)
      (FourEvents.UnusedNoncollinearTriple P a bits) ≤
        384 * (b : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  rw [AlignedUnused.conditionedOffsetProbability_eq_alignedLaw P hκ a ha bits p,
    AlignedUnused.alignedLaw_eq_bind]
  apply UnusedOffsetIncidence.bind_probability_le
  intro u
  have hlaw := TupleAlignment.uniform_map_equiv (unusedArrayEquiv P a).symm
  rw [← hlaw, PMF.map_comp, PMF.toOuterMeasure_map_apply]
  change ((PMF.uniformOfFintype
    (UnusedOffsetIncidence.Offsets (unusedDirections a))).toOuterMeasure
    {o | FourEvents.UnusedNoncollinearTriple P a bits
      ((AlignedUnused.split P a).symm (u, (unusedArrayEquiv P a).symm o))}).toReal ≤ _
  rw [← UnusedOffsetIncidence.probability_eq_pmf]
  have h := refreshed_unusedNoncollinearTriple_probability_le P a bits
    ((AlignedUnused.split P a).symm (u, fun _ _ => 0))
    (fun o => (AlignedUnused.split P a).symm (u, (unusedArrayEquiv P a).symm o))
    (fun o d hd => ?_) (fun o d => ?_)
  · convert h using 1; ring
  · have ho := congrFun (congrArg Prod.fst
      ((AlignedUnused.split P a).apply_symm_apply (u, (unusedArrayEquiv P a).symm o)))
      ⟨d, hd⟩
    have hn := congrFun (congrArg Prod.fst
      ((AlignedUnused.split P a).apply_symm_apply (u, fun _ _ => 0))) ⟨d, hd⟩
    exact ho.trans hn.symm
  · exact congrFun (congrArg Prod.snd
      ((AlignedUnused.split P a).apply_symm_apply (u, (unusedArrayEquiv P a).symm o)))
      ⟨d.1, (mem_unusedDirections d.1).mp d.2⟩

theorem aligned_unusedNoncollinearTriple_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    offsetProbability (fun M => Aligned P a bits p M ∧
      FourEvents.UnusedNoncollinearTriple P a bits M) ≤
        offsetProbability (Aligned P a bits p) *
          (384 * (b : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 2) := by
  rw [UnusedOffsetProbability.offsetProbability_joint_eq_mul_conditioned]
  exact mul_le_mul_of_nonneg_left
    (conditioned_unusedNoncollinearTriple_le P hκ a ha bits p)
    (UnusedOffsetProbability.offsetProbability_nonneg _)

theorem conditioned_badCover_le_used_events
    (P : EqualityPattern b κ) (hb : 3 ≤ b) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
      conditionedOffsetProbability (Aligned P a bits p)
        (fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) +
      conditionedOffsetProbability (Aligned P a bits p)
        (fun M => Admissible P a bits p M ∧ FourEvents.ForbiddenCollinearTriple P a bits p M) +
      (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 +
      384 * (b : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  have h := UnusedOffsetProbability.conditioned_badCover_four_events_le
    P a bits p hb hκ ha
  have h₁ := UnusedOffsetProbability.conditioned_fourEvents_unusedPrecoverage_le
    (P := P) (a := a) (bits := bits) (p := p)
  have h₄ := conditioned_unusedNoncollinearTriple_le P hκ a ha bits p
  linarith

end Balanced.Local.UnusedTripleProbability

end

end OAI

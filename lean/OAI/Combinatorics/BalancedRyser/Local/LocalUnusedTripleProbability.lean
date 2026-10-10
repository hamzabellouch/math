import OAI.Combinatorics.BalancedRyser.Local.LocalFourEventWitnesses
import OAI.Combinatorics.BalancedRyser.Local.LocalUnusedOffsetProbability
import OAI.Combinatorics.BalancedRyser.Probability.UnusedOffsetAveraging

namespace OAI

noncomputable section
open scoped Classical

namespace Balanced.Local.UnusedTripleProbability

open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def unusedOffsets (a : DirectionAssignment F b κ) (M : MergedPairs F) :
    UnusedOffsetIncidence.Offsets (unusedDirections a) := fun d => M d.1

omit [Fintype F] in
theorem prescribedDesignated_card_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F) :
    (prescribedDesignated P a bits M).card ≤ 4 * b := by
  apply Finset.card_image_le.trans
  simp [Nat.mul_comm]

omit [Fintype F] in
theorem prescribedDesignated_eq_of_used_agreement (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M N : MergedPairs F)
    (h : ∀ d ∈ Finset.univ.image a.2, M d = N d) :
    prescribedDesignated P a bits M = prescribedDesignated P a bits N := by
  unfold prescribedDesignated
  congr 1
  funext ij
  exact UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement M N h ij

theorem unusedNoncollinearTriple_imp (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)
    (h : FourEvents.UnusedNoncollinearTriple P a bits M) :
    UnusedOffsetIncidence.NoncollinearTripleInPair (unusedDirections a)
      (prescribedDesignated P a bits M) (unusedOffsets a M) := by
  obtain ⟨d, i, j, k, hd, _, _, _, hi, hj, hk, hn⟩ :=
    FourEvents.unusedNoncollinearTriple_indices P a bits M h
  have hdu : d ∈ unusedDirections a := (mem_unusedDirections d).mpr hd
  refine ⟨prescribedPoint P a bits M i, ?_, prescribedPoint P a bits M j, ?_,
    prescribedPoint P a bits M k, ?_, hn, ⟨⟨d,hdu⟩, ?_, ?_, ?_⟩⟩
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · rcases Finset.mem_union.mp hi with hfalse | htrue
    · exact ⟨false, (Finset.mem_filter.mp hfalse).2⟩
    · exact ⟨true, (Finset.mem_filter.mp htrue).2⟩
  · rcases Finset.mem_union.mp hj with hfalse | htrue
    · exact ⟨false, (Finset.mem_filter.mp hfalse).2⟩
    · exact ⟨true, (Finset.mem_filter.mp htrue).2⟩
  · rcases Finset.mem_union.mp hk with hfalse | htrue
    · exact ⟨false, (Finset.mem_filter.mp hfalse).2⟩
    · exact ⟨true, (Finset.mem_filter.mp htrue).2⟩

theorem refreshed_unusedNoncollinearTriple_probability_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (N : MergedPairs F)
    (Ms : UnusedOffsetIncidence.Offsets (unusedDirections a) → MergedPairs F)
    (hused : ∀ o d, d ∈ Finset.univ.image a.2 → Ms o d = N d)
    (hunused : ∀ o (d : unusedDirections a), Ms o d.1 = o d) :
    UnusedOffsetIncidence.probability
      (fun o => FourEvents.UnusedNoncollinearTriple P a bits (Ms o)) ≤
      6 * (4 * (b : ℝ)) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  have hmono : UnusedOffsetIncidence.probability
      (fun o => FourEvents.UnusedNoncollinearTriple P a bits (Ms o)) ≤
      UnusedOffsetIncidence.probability
        (UnusedOffsetIncidence.NoncollinearTripleInPair (unusedDirections a)
          (prescribedDesignated P a bits N)) := by
    apply UnusedOffsetIncidence.probability_mono
    intro o ho
    have h := unusedNoncollinearTriple_imp P a bits (Ms o) ho
    have hpoints := prescribedDesignated_eq_of_used_agreement P a bits
      (Ms o) N (hused o)
    have hoff : unusedOffsets a (Ms o) = o := by
      funext d
      exact hunused o d
    rwa [hpoints, hoff] at h
  apply hmono.trans
  apply (UnusedOffsetIncidence.noncollinearTripleInPair_probability_le
    (unusedDirections a) (prescribedDesignated P a bits N)).trans
  gcongr
  exact_mod_cast prescribedDesignated_card_le P a bits N

theorem mixed_unusedNoncollinearTriple_probability_le {A : Type*} [Fintype A]
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) (bits : Bits b)
    (μ : PMF A) (N : A → MergedPairs F)
    (Ms : A → UnusedOffsetIncidence.Offsets (unusedDirections a) → MergedPairs F)
    (hused : ∀ x o d, d ∈ Finset.univ.image a.2 → Ms x o d = N x d)
    (hunused : ∀ x o (d : unusedDirections a), Ms x o d.1 = o d) :
    ((μ.bind (fun x =>
      (PMF.uniformOfFintype (UnusedOffsetIncidence.Offsets (unusedDirections a))).map
        (Ms x))).toOuterMeasure
      {M | FourEvents.UnusedNoncollinearTriple P a bits M}).toReal ≤
        6 * (4 * (b : ℝ)) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  apply UnusedOffsetIncidence.bind_probability_le
  intro x
  rw [PMF.toOuterMeasure_map_apply]
  change ((PMF.uniformOfFintype
    (UnusedOffsetIncidence.Offsets (unusedDirections a))).toOuterMeasure
    {o | FourEvents.UnusedNoncollinearTriple P a bits (Ms x o)}).toReal ≤ _
  rw [← UnusedOffsetIncidence.probability_eq_pmf]
  exact refreshed_unusedNoncollinearTriple_probability_le P a bits (N x)
    (Ms x) (hused x) (hunused x)

end Balanced.Local.UnusedTripleProbability

end

end OAI

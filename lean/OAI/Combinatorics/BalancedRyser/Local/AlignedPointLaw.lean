import OAI.Combinatorics.BalancedRyser.Local.GlobalAlignedParentCoordinates

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition AlignedUnused

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem PointSystem.generated_points {b κ : ℕ} {P : EqualityPattern b κ}
    {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}
    {R : Finset (Fin b)} (S : PointSystem P a bits p R)
    (hκ : κ ≤ 2) (hD : (dependentOccurrences P R).card = 2*κ) (ha : Eligible P a)
    (z : (FreeIndex P R → F) × UnusedArray P a) (ij : Fin b × Fin 4) :
    prescribedPoint P a bits ((coordinateEquiv P hκ R hD a ha bits p).symm z).1 ij =
      S.point ij (z.1 (S.underlying ij)) := by
  let e := coordinateEquiv P hκ R hD a ha bits p
  have hcoord := congrFun (congrArg Prod.fst (e.apply_symm_apply z)) (S.underlying ij)
  exact (S.realizes (e.symm z) ij).trans (congrArg (S.point ij) hcoord)

theorem PointSystem.aligned_pointLaw {b κ : ℕ} {P : EqualityPattern b κ}
    {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}
    {R : Finset (Fin b)} (S : PointSystem P a bits p R)
    (hκ : κ ≤ 2) (hD : (dependentOccurrences P R).card = 2*κ) (ha : Eligible P a) :
    (alignedLaw P hκ a ha bits p).map
      (fun M => (prescribedPoint P a bits M, (fun d => M d.1 : UnusedArray P a))) =
      (PMF.uniformOfFintype ((FreeIndex P R → F) × UnusedArray P a)).map
        (fun z => ((fun ij => S.point ij (z.1 (S.underlying ij))), z.2)) := by
  rw [alignedLaw_eq_uniform_coordinates P hκ R hD a ha bits p, PMF.map_comp]
  congr 1
  funext z
  apply Prod.ext
  · funext ij
    exact S.generated_points hκ hD ha z ij
  · funext d
    exact generated_unused P hκ R hD a ha bits p z d

theorem PointSystem.conditioned_probability {b κ : ℕ} {P : EqualityPattern b κ}
    {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}
    {R : Finset (Fin b)} (S : PointSystem P a bits p R)
    (hκ : κ ≤ 2) (hD : (dependentOccurrences P R).card = 2*κ) (ha : Eligible P a)
    (E : ((Fin b × Fin 4) → Point F) → UnusedArray P a → Prop) :
    conditionedOffsetProbability (Aligned P a bits p)
      (fun M => E (prescribedPoint P a bits M) (fun d => M d.1)) =
      ((PMF.uniformOfFintype ((FreeIndex P R → F) × UnusedArray P a)).toOuterMeasure
        {z | E (fun ij => S.point ij (z.1 (S.underlying ij))) z.2}).toReal := by
  rw [conditionedOffsetProbability_eq_alignedLaw P hκ a ha bits p]
  have h := congrArg (fun law => (law.toOuterMeasure {z | E z.1 z.2}).toReal)
    (S.aligned_pointLaw hκ hD ha)
  simpa only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using h

theorem exists_smallReuse_pointLaw {b κ : ℕ} (P : EqualityPattern b κ)
    (hb : 3 ≤ b) (hκ : κ ≤ 1) (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    ∃ R : Finset (Fin b), ∃ _ : (dependentOccurrences P R).card = 2*κ,
      ∃ S : PointSystem P a bits p R,
      ∀ E : ((Fin b × Fin 4) → Point F) → UnusedArray P a → Prop,
        conditionedOffsetProbability (Aligned P a bits p)
          (fun M => E (prescribedPoint P a bits M) (fun d => M d.1)) =
          ((PMF.uniformOfFintype ((FreeIndex P R → F) × UnusedArray P a)).toOuterMeasure
            {z | E (fun ij => S.point ij (z.1 (S.underlying ij))) z.2}).toReal := by
  obtain ⟨R, hD, ⟨S⟩⟩ := exists_smallReuse_pointSystem P hb hκ a ha bits p
  exact ⟨R, hD, S, S.conditioned_probability (by omega) hD ha⟩

end
end Balanced.Local.AlignedGlobal

end OAI

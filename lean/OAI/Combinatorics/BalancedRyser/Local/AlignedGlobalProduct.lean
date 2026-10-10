import OAI.Combinatorics.BalancedRyser.Local.AlignedFreeCoordinates
import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalCardinality
import OAI.Combinatorics.BalancedRyser.Local.OneReuseDecomposition

namespace OAI

namespace Balanced.Local.AlignedGlobal

open TupleAlignment RootChildPartition AlignedUnused
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev FreeIndex {b κ : ℕ} (P : EqualityPattern b κ) (R : Finset (Fin b)) :=
  {ij : Fin b × Fin 4 // ij ∉ dependentOccurrences P R}

abbrev AlignedOffsets {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) :=
  {M : MergedPairs F // Aligned P a bits p M}

def coordinates {b κ : ℕ} (P : EqualityPattern b κ) (R : Finset (Fin b))
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) :
    (FreeIndex P R → F) × UnusedArray P a :=
  ((fun ij => linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)
      ⟨prescribedPoint P a bits M.1 ij.1, M.2 ij.1⟩),
    fun d => M.1 d.1)

omit [Fintype F] [DecidableEq F] in

theorem tuple_offsets_eq_of_points (T : FourTuple F)
    (hT : Function.Injective T.generator) (M N : MergedPairs F)
    (h : ∀ j, tuplePoint M T j = tuplePoint N T j) :
    ∀ j, M (T.generator j) = N (T.generator j) := by
  have heq : (fun j => M (T.generator j)) = (fun j => N (T.generator j)) := by
    apply (tuplePositionEquiv T.generator (adjacent_ne_of_injective T hT) T.side).injective
    funext j
    simpa only [tuplePositionEquiv_apply, tuplePoint, constituent] using h j
  exact congrFun heq

omit [Fintype F] in

theorem coordinates_injective {b κ : ℕ} (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    Function.Injective (coordinates P R a bits p) := by
  intro M N heq
  have hfree (ij : Fin b × Fin 4) (hij : ij ∉ dependentOccurrences P R) :
      prescribedPoint P a bits M.1 ij = prescribedPoint P a bits N.1 ij := by
    have h := congrFun (congrArg Prod.fst heq) (⟨ij, hij⟩ : FreeIndex P R)
    exact congrArg Subtype.val ((linePointEquiv (a.1 ij.1)
      (lineEval (a.1 ij.1) p)).injective h)
  have hroot (i : Fin b) (hi : i ∈ R) (j : Fin 4) :
      M.1 (a.2 (P.classOf i j)) = N.1 (a.2 (P.classOf i j)) := by
    apply tuple_offsets_eq_of_points (prescribedTuple P a bits i)
      (ha.2.1.comp (P.withinTuple i)) M.1 N.1
    intro k
    apply hfree (i,k)
    simp only [mem_dependentOccurrences, not_and]
    exact fun hnot => (hnot hi).elim
  have hold (c : Fin (4*b-κ)) (hc : c ∈ R.biUnion P.classSet) :
      M.1 (a.2 c) = N.1 (a.2 c) := by
    obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
    exact hroot i hi j
  have hpoint (ij : Fin b × Fin 4) :
      prescribedPoint P a bits M.1 ij = prescribedPoint P a bits N.1 ij := by
    by_cases hdep : ij ∈ dependentOccurrences P R
    · have hd := (mem_dependentOccurrences P R ij).mp hdep
      let T := prescribedTuple P a bits ij.1
      have hT : Function.Injective T.generator := ha.2.1.comp (P.withinTuple ij.1)
      have hleft (O : MergedPairs F) :
          lineEval (a.2 (P.classOf ij.1 ij.2)) (prescribedPoint P a bits O ij) =
            O (a.2 (P.classOf ij.1 ij.2)) (bits ij.1 ij.2) := by
        exact tuplePosition_lineEval_left T.generator (adjacent_ne_of_injective T hT)
          T.side (fun j => O (T.generator j)) ij.2
      have hright (O : MergedPairs F) :
          lineEval (a.2 (P.classOf ij.1 (ij.2+1))) (prescribedPoint P a bits O ij) =
            O (a.2 (P.classOf ij.1 (ij.2+1))) (!(bits ij.1 (ij.2+1))) := by
        exact tuplePosition_lineEval_right T.generator (adjacent_ne_of_injective T hT)
          T.side (fun j => O (T.generator j)) ij.2
      rcases hd.2 with hl | hr
      · apply (lineEvalEquiv (a.2 (P.classOf ij.1 ij.2)) (a.1 ij.1)
          (ha.2.2 ij.1 ij.2)).injective
        apply Prod.ext
        · change lineEval _ _ = lineEval _ _
          rw [hleft, hleft, hold _ hl]
        · exact (M.2 ij).trans (N.2 ij).symm
      · apply (lineEvalEquiv (a.2 (P.classOf ij.1 (ij.2+1))) (a.1 ij.1)
          (ha.2.2 ij.1 (ij.2+1))).injective
        apply Prod.ext
        · change lineEval _ _ = lineEval _ _
          rw [hright, hright, hold _ hr]
        · exact (M.2 ij).trans (N.2 ij).symm
    · exact hfree ij hdep
  apply Subtype.ext
  funext d
  by_cases hd : d ∈ usedDirections P a
  · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨⟨i,j⟩, rfl⟩ := P.everyClass c
    exact tuple_offsets_eq_of_points (prescribedTuple P a bits i)
      (ha.2.1.comp (P.withinTuple i)) M.1 N.1 (fun k => hpoint (i,k)) j
  · exact congrFun (congrArg Prod.snd heq) ⟨d, hd⟩

def coordinateEquiv {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    AlignedOffsets P a bits p ≃ ((FreeIndex P R → F) × UnusedArray P a) :=
  Equiv.ofBijective (coordinates P R a bits p)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨coordinates_injective P R a ha bits p,
        card_aligned_eq_free_product P hκ a ha bits p (dependentOccurrences P R) hD⟩)

@[simp] theorem coordinateEquiv_apply {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) :
    coordinateEquiv P hκ R hD a ha bits p M = coordinates P R a bits p M := rfl

theorem generated_free {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (z : (FreeIndex P R → F) × UnusedArray P a) (ij : FreeIndex P R) :
    prescribedPoint P a bits ((coordinateEquiv P hκ R hD a ha bits p).symm z).1 ij.1 =
      ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm (z.1 ij)).1 := by
  let e := coordinateEquiv P hκ R hD a ha bits p
  have h := congrFun (congrArg Prod.fst (e.apply_symm_apply z)) ij
  change linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)
      ⟨prescribedPoint P a bits (e.symm z).1 ij.1, (e.symm z).2 ij.1⟩ = z.1 ij at h
  have hp := congrArg (fun t => ((linePointEquiv (a.1 ij.1.1)
    (lineEval (a.1 ij.1.1) p)).symm t).1) h
  simpa only [Equiv.symm_apply_apply] using hp

theorem generated_unused {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (z : (FreeIndex P R → F) × UnusedArray P a)
    (d : {d : Direction F // d ∉ usedDirections P a}) :
    ((coordinateEquiv P hκ R hD a ha bits p).symm z).1 d.1 = z.2 d := by
  exact congrFun (congrArg Prod.snd
    ((coordinateEquiv P hκ R hD a ha bits p).apply_symm_apply z)) d

theorem alignedLaw_eq_uniform_coordinates {b κ : ℕ} (P : EqualityPattern b κ)
    (hκ : κ ≤ 2) (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    alignedLaw P hκ a ha bits p =
      (PMF.uniformOfFintype ((FreeIndex P R → F) × UnusedArray P a)).map
        (fun z => ((coordinateEquiv P hκ R hD a ha bits p).symm z).1) := by
  let e := coordinateEquiv P hκ R hD a ha bits p
  let : Nonempty (AlignedOffsets P a bits p) :=
    ⟨e.symm ((fun _ => 0), fun _ _ => 0)⟩
  let : Nonempty ({M : MergedPairs F | Aligned P a bits p M} : Set (MergedPairs F)) :=
    ⟨e.symm ((fun _ => 0), fun _ _ => 0)⟩
  unfold alignedLaw
  rw [Balanced.uniform_filter_eq_subtype_map]
  change (PMF.uniformOfFintype (AlignedOffsets P a bits p)).map Subtype.val = _
  have h := uniform_map_equiv e.symm
  rw [← h, PMF.map_comp]
  rfl

theorem conditioned_probability_eq_uniform_coordinates {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (E : MergedPairs F → Prop) :
    conditionedOffsetProbability (Aligned P a bits p) E =
      ((PMF.uniformOfFintype ((FreeIndex P R → F) × UnusedArray P a)).toOuterMeasure
        {z | E ((coordinateEquiv P hκ R hD a ha bits p).symm z).1}).toReal := by
  rw [conditionedOffsetProbability_eq_alignedLaw P hκ a ha bits p E,
    alignedLaw_eq_uniform_coordinates P hκ R hD a ha bits p,
    PMF.toOuterMeasure_map_apply]
  rfl

end
end Balanced.Local.AlignedGlobal

end OAI

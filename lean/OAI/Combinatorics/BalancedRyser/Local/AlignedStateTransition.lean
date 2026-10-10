import OAI.Combinatorics.BalancedRyser.Local.AlignmentStepLaw

namespace OAI

namespace Balanced.AlignedListProbability

open Local PartialAlignment
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def installCurrentTupleOffsets (T : FourTuple F)
    (o : Fin 4 → Bool → F) (a : MergedPairs F) : MergedPairs F :=
  Function.extend T.generator o a

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem installCurrentTupleOffsets_generator
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (o : Fin 4 → Bool → F) (a : MergedPairs F) (j : Fin 4) :
    installCurrentTupleOffsets T o a (T.generator j) = o j :=
  hT.extend_apply o a j

omit [Field F] [Fintype F] in

theorem installCurrentTupleOffsets_outside (T : FourTuple F)
    (o : Fin 4 → Bool → F) (a : MergedPairs F) (d : Direction F)
    (hd : d ∉ generatorSet T) :
    installCurrentTupleOffsets T o a d = a d := by
  apply Function.extend_apply'
  intro h
  obtain ⟨j, rfl⟩ := h
  exact hd (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

omit [Field F] [Fintype F] in

theorem installCurrentTupleOffsets_agree_old
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (D : Finset (Direction F)) (o : Fin 4 → Bool → F) (a : MergedPairs F)
    (ho : ∀ j ∈ exposedTupleIndices T D, o j = a (T.generator j)) :
    ∀ d ∈ D, installCurrentTupleOffsets T o a d = a d := by
  intro d hd
  by_cases hg : d ∈ generatorSet T
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hg
    rw [installCurrentTupleOffsets_generator T hT]
    exact ho j (by simpa only [exposedTupleIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hd)
  · exact installCurrentTupleOffsets_outside T o a d hg

def generateCurrentState
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) (x : CurrentFreeCoordinates T D) : MergedPairs F :=
  installCurrentTupleOffsets T (generateCurrentTupleOffsets T hT g hg c D hD a x) a

theorem generateCurrentState_agree_old
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) (x : CurrentFreeCoordinates T D) :
    ∀ d ∈ D, generateCurrentState T hT g hg c D hD a x d = a d := by
  apply installCurrentTupleOffsets_agree_old T hT D
  exact ((alignedFreeCoordinatesEquiv T.generator
    (TupleAlignment.adjacent_ne_of_injective T hT) T.side g hg c
    (exposedTupleIndices T D) hD (fun j => a (T.generator j))).symm x).1.2

theorem generateCurrentState_aligned
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) (x : CurrentFreeCoordinates T D) :
    ∀ j, OnLine (tuplePoint (generateCurrentState T hT g hg c D hD a x) T j) (g,c) := by
  intro j
  have h := ((alignedFreeCoordinatesEquiv T.generator
    (TupleAlignment.adjacent_ne_of_injective T hT) T.side g hg c
    (exposedTupleIndices T D) hD (fun k => a (T.generator k))).symm x).2 j
  simpa only [generateCurrentState, tuplePoint, constituent,
    installCurrentTupleOffsets_generator T hT,
    TupleAlignment.tuplePositionEquiv_apply, generateCurrentTupleOffsets] using h

omit [Field F] [Fintype F] in

theorem installCurrentTupleOffsets_reconstruct
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (D : Finset (Direction F)) (a M : MergedPairs F)
    (hfix : ∀ d ∈ D, M d = a d) :
    ∀ d ∈ D ∪ generatorSet T,
      M d = installCurrentTupleOffsets T (fun j => M (T.generator j)) a d := by
  intro d hd
  by_cases hg : d ∈ generatorSet T
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hg
    rw [installCurrentTupleOffsets_generator T hT]
  · rw [installCurrentTupleOffsets_outside T _ a d hg]
    exact hfix d ((Finset.mem_union.mp hd).resolve_right hg)

omit [Field F] in

theorem conditionedOffsetProbability_congr_on (A E G : MergedPairs F → Prop)
    (h : ∀ M, A M → (E M ↔ G M)) :
    conditionedOffsetProbability A E = conditionedOffsetProbability A G := by
  have he : (fun M => A M ∧ E M) = (fun M => A M ∧ G M) := by
    funext M
    apply propext
    by_cases ha : A M
    · simp only [ha, true_and, h M ha]
    · simp only [ha, false_and]
  unfold conditionedOffsetProbability
  rw [he]

theorem current_state_generated_probability
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) (E : MergedPairs F → Prop)
    (hE : ∀ M N, (∀ d ∈ D ∪ generatorSet T, M d = N d) → (E M ↔ E N)) :
    conditionedOffsetProbability
      (fun M => (∀ d ∈ D, M d = a d) ∧ ∀ j, OnLine (tuplePoint M T j) (g,c)) E =
      ((PMF.uniformOfFintype (CurrentFreeCoordinates T D)).toOuterMeasure
        {x | E (generateCurrentState T hT g hg c D hD a x)}).toReal := by
  let G : (Fin 4 → Bool → F) → Prop := fun o => E (installCurrentTupleOffsets T o a)
  have hc := conditionedOffsetProbability_congr_on
    (fun M => (∀ d ∈ D, M d = a d) ∧ ∀ j, OnLine (tuplePoint M T j) (g,c))
    E (fun M => G (fun j => M (T.generator j)))
    (fun M hm => hE M _ (installCurrentTupleOffsets_reconstruct T hT D a M hm.1))
  exact hc.trans (current_tuple_generated_probability T hT g hg c D hD a G)

theorem generateCurrentState_freePoint
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) (x : CurrentFreeCoordinates T D)
    (j : {j : Fin 4 // j ∈ freePositions (exposedTupleIndices T D)}) :
    tuplePoint (generateCurrentState T hT g hg c D hD a x) T j.1 =
      ((TupleAlignment.linePointEquiv g c).symm (x j)).1 := by
  have h := alignedPartial_generated_free T.generator
    (TupleAlignment.adjacent_ne_of_injective T hT) T.side g hg c
    (exposedTupleIndices T D) hD (fun k => a (T.generator k)) x j
  simpa only [generateCurrentState, tuplePoint, constituent,
    installCurrentTupleOffsets_generator T hT,
    TupleAlignment.tuplePositionEquiv_apply, generateCurrentTupleOffsets] using h

theorem generateCurrentState_old_left
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) (x : CurrentFreeCoordinates T D)
    (j : Fin 4) (hj : T.generator j ∈ D) :
    tuplePoint (generateCurrentState T hT g hg c D hD a x) T j =
      (TupleAlignment.lineEvalEquiv (T.generator j) g (hg j)).symm
        (a (T.generator j) (T.side j), c) := by
  have h := alignedPartial_position_old_left T.generator
    (TupleAlignment.adjacent_ne_of_injective T hT) T.side g hg c
    (exposedTupleIndices T D) (fun k => a (T.generator k))
    ((alignedFreeCoordinatesEquiv T.generator
      (TupleAlignment.adjacent_ne_of_injective T hT) T.side g hg c
      (exposedTupleIndices T D) hD (fun k => a (T.generator k))).symm x)
    j (by simpa only [exposedTupleIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj)
  simpa only [generateCurrentState, tuplePoint, constituent,
    installCurrentTupleOffsets_generator T hT,
    TupleAlignment.tuplePositionEquiv_apply, generateCurrentTupleOffsets] using h

theorem generateCurrentState_old_right
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) (x : CurrentFreeCoordinates T D)
    (j : Fin 4) (hj : T.generator (j+1) ∈ D) :
    tuplePoint (generateCurrentState T hT g hg c D hD a x) T j =
      (TupleAlignment.lineEvalEquiv (T.generator (j+1)) g (hg (j+1))).symm
        (a (T.generator (j+1)) (!(T.side (j+1))), c) := by
  have h := alignedPartial_position_old_right T.generator
    (TupleAlignment.adjacent_ne_of_injective T hT) T.side g hg c
    (exposedTupleIndices T D) (fun k => a (T.generator k))
    ((alignedFreeCoordinatesEquiv T.generator
      (TupleAlignment.adjacent_ne_of_injective T hT) T.side g hg c
      (exposedTupleIndices T D) hD (fun k => a (T.generator k))).symm x)
    j (by simpa only [exposedTupleIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj)
  simpa only [generateCurrentState, tuplePoint, constituent,
    installCurrentTupleOffsets_generator T hT,
    TupleAlignment.tuplePositionEquiv_apply, generateCurrentTupleOffsets] using h

theorem generateCurrentState_listAligned {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (pre : List ι) (i : ι)
    (hi : Function.Injective (T i).generator)
    (hg : ∀ j, (T i).generator j ≠ (L i).1)
    (hD : (exposedTupleIndices (T i)
      (pre.toFinset.biUnion (fun k => generatorSet (T k)))).card ≤ 1)
    (a : MergedPairs F) (ha : ListAligned T L pre a)
    (x : CurrentFreeCoordinates (T i)
      (pre.toFinset.biUnion (fun k => generatorSet (T k)))) :
    ListAligned T L (i :: pre)
      (generateCurrentState (T i) hi (L i).1 hg (L i).2
        (pre.toFinset.biUnion (fun k => generatorSet (T k))) hD a x) := by
  intro k hk
  rcases List.mem_cons.mp hk with hki | hk
  · subst k
    exact generateCurrentState_aligned (T i) hi (L i).1 hg (L i).2 _ hD a x
  · have hp := (listAligned_agree T L pre _ a
      (generateCurrentState_agree_old (T i) hi (L i).1 hg (L i).2 _ hD a x)).mpr ha
    exact hp k hk

theorem full_aligned_state_generated_probability {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (post pre : List ι) (i : ι)
    (hT : ∀ k ∈ post ++ i :: pre, Function.Injective (T k).generator)
    (hg : ∀ k ∈ post ++ i :: pre, ∀ j, (T k).generator j ≠ (L k).1)
    (horder : SmallReuseOrder (fun k => generatorSet (T k)) (post ++ i :: pre))
    (a : MergedPairs F) (ha : ListAligned T L pre a)
    (E : MergedPairs F → Prop)
    (hE : ∀ M N, (∀ d ∈ (i :: pre).toFinset.biUnion (fun k => generatorSet (T k)),
      M d = N d) → (E M ↔ E N)) :
    let D := pre.toFinset.biUnion (fun k => generatorSet (T k))
    conditionedOffsetProbability
      (fun M => ListAligned T L (post ++ i :: pre) M ∧ ∀ d ∈ D, M d = a d) E =
      ((PMF.uniformOfFintype (CurrentFreeCoordinates (T i) D)).toOuterMeasure
        {x | E (generateCurrentState (T i) (hT i (by simp)) (L i).1
          (hg i (by simp)) (L i).2 D
          (step_exposed_count T post pre i (hT i (by simp)) horder) a x)}).toReal := by
  let D := pre.toFinset.biUnion (fun k => generatorSet (T k))
  have hdep (M N : MergedPairs F)
      (h : ∀ d ∈ D ∪ generatorSet (T i), M d = N d) : E M ↔ E N := by
    apply hE M N
    intro d hd
    apply h d
    simpa only [D, List.toFinset_cons, Finset.biUnion_insert, Finset.union_comm] using hd
  have hs := conditioned_alignment_step T L post pre i hT hg horder a ha E hE
  have hc := current_state_generated_probability (T i) (hT i (by simp)) (L i).1
    (hg i (by simp)) (L i).2 D
    (step_exposed_count T post pre i (hT i (by simp)) horder) a E hdep
  exact hs.trans (by simpa only [and_comm, Prod.eta] using hc)

end
end Balanced.AlignedListProbability

end OAI

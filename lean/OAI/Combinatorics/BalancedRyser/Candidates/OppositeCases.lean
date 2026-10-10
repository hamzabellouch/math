import OAI.Combinatorics.BalancedRyser.Candidates.CandidateOldOppositeOverlap
import OAI.Combinatorics.BalancedRyser.Candidates.ExposedOppositeSum

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Label (F : Type*) := (FourTuple F × Fin 4) × Direction F

def witnesses (g : Direction F) (M : MergedPairs F) : Finset (Label F) :=
  (((eligibleTuples g).product Finset.univ).product Finset.univ).filter
    (fun w => M ∈ successfulInDirection w.1.1 g ∧ w.2 ≠ g ∧
      w.2 ∉ generatorSet w.1.1 ∧
      PairWitness M w.2 (tuplePoint M w.1.1 w.1.2)
        (tuplePoint M w.1.1 (w.1.2 + 2)))

theorem mem_witnesses (g : Direction F) (M : MergedPairs F)
    (T : FourTuple F) (i : Fin 4) (d : Direction F) :
    ((T,i),d) ∈ witnesses g M ↔
      T ∈ eligibleTuples g ∧ M ∈ successfulInDirection T g ∧ d ≠ g ∧
      d ∉ generatorSet T ∧ PairWitness M d (tuplePoint M T i)
        (tuplePoint M T (i+2)) := by
  simp [witnesses]

theorem exists_witness_of_opposite {g : Direction F} {M : MergedPairs F}
    {T : FourTuple F} {S : Line F} (hS : SuccessfulOn M T S) (hg : S.1 = g)
    (hopp : OppositeWitness M T S) :
    ∃ i d, ((T,i),d) ∈ witnesses g M := by
  obtain ⟨i,d,hdg,hdT,hp⟩ := hopp
  refine ⟨i,d,(mem_witnesses g M T i d).mpr ⟨?_,?_,?_,hdT,hp⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS.1,
      fun j => by simpa only [hg] using hS.2.1 j⟩
  · refine ⟨⟨S.2,?_⟩,hS.2.2.1⟩
    simpa only [← hg] using hS.2.2.2
  · simpa only [hg] using hdg

def freshWitnesses (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : Finset (Label F) :=
  (witnesses g M).filter (fun w => w.2 ∉ D)

def oldFreshWitnesses (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : Finset (Label F) :=
  (witnesses g M).filter (fun w => w.2 ∈ D ∧ ∀ i, w.1.1.generator i ∉ D)

theorem witnesses_subset_cases (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : witnesses g M ⊆
      freshWitnesses g D M ∪
        (oldFreshWitnesses g D M ∪ CandidateOldOpposite.overlappingWitnesses g D M) := by
  rintro ⟨⟨T,i⟩,d⟩ hw
  by_cases hd : d ∈ D
  · apply Finset.mem_union_right
    by_cases hf : ∀ j, T.generator j ∉ D
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw,hd,hf⟩)
    · apply Finset.mem_union_right
      obtain ⟨hT,hs,hdg,hdT,hp⟩ := (mem_witnesses g M T i d).mp hw
      have hpos : 0 < (exposedTupleIndices T D).card := by
        apply Finset.card_pos.mpr
        push Not at hf
        obtain ⟨j,hj⟩ := hf
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
      exact (CandidateOldOpposite.mem_overlappingWitnesses_iff g D M T i d).mpr
        ⟨hT,hpos,hs,hd,hdg,hdT,hp⟩
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw,hd⟩)

theorem witnesses_card_le_cases (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : (witnesses g M).card ≤
      (freshWitnesses g D M).card + (oldFreshWitnesses g D M).card +
        (CandidateOldOpposite.overlappingWitnesses g D M).card := by
  have h := (Finset.card_le_card (witnesses_subset_cases g D M)).trans
    (Finset.card_union_le _ _)
  have h' := Finset.card_union_le (oldFreshWitnesses g D M)
    (CandidateOldOpposite.overlappingWitnesses g D M)
  omega

theorem oldFreshWitnesses_card_le (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : (oldFreshWitnesses g D M).card ≤
      ExposedOppositeSum.oldOppositeFreshCount g D M := by
  let S := ((((ExposedOppositeSum.freshTuples D).product (Finset.univ : Finset F)).product
    (D.erase g)).product (Finset.univ : Finset (Fin 4))).filter
    (fun x => SuccessfulOn M x.1.1.1 (g,x.1.1.2) ∧
      PairWitness M x.1.2 (tuplePoint M x.1.1.1 x.2)
        (tuplePoint M x.1.1.1 (x.2+2)))
  let f : Label F → ((FourTuple F × F) × Direction F) × Fin 4 :=
    fun w => (((w.1.1,lineEval g (tuplePoint M w.1.1 0)),w.2),w.1.2)
  have hmap : ∀ w ∈ oldFreshWitnesses g D M, f w ∈ S := by
    rintro ⟨⟨T,i⟩,d⟩ hw
    obtain ⟨hw,hd,hfresh⟩ := Finset.mem_filter.mp hw
    obtain ⟨hT,hs,hdg,hdT,hp⟩ := (mem_witnesses g M T i d).mp hw
    obtain ⟨hinj,havoid⟩ := (Finset.mem_filter.mp hT).2
    obtain ⟨⟨c,hc⟩,hpoints⟩ := hs
    have halign : ∀ j, OnLine (tuplePoint M T j)
        (g,lineEval g (tuplePoint M T 0)) := by
      intro j
      exact (hc j).trans (hc 0).symm
    apply Finset.mem_filter.mpr
    refine ⟨?_,⟨hinj,havoid,hpoints,halign⟩,hp⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hinj,hfresh⟩,Finset.mem_univ _⟩,
        Finset.mem_erase.mpr ⟨hdg,hd⟩⟩,Finset.mem_univ _⟩
  have hinj : Set.InjOn f (oldFreshWitnesses g D M : Set (Label F)) := by
    intro x hx y hy he
    have hT := congrArg (fun z : ((FourTuple F × F) × Direction F) × Fin 4 => z.1.1.1) he
    have hi := congrArg (fun z : ((FourTuple F × F) × Direction F) × Fin 4 => z.2) he
    have hd := congrArg (fun z : ((FourTuple F × F) × Direction F) × Fin 4 => z.1.2) he
    exact Prod.ext (Prod.ext hT hi) hd
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  have hS : S.card = ExposedOppositeSum.oldOppositeFreshCount g D M := by
    simp only [S, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product,
      ExposedOppositeSum.oldOppositeFreshCount]
  exact hc.trans_eq hS

end
end Balanced.OppositeAssembly

end OAI

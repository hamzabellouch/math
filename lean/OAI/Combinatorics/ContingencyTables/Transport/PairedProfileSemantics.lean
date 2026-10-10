import OAI.Combinatorics.ContingencyTables.Machines.PairedProfileProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionComputedInitial
import OAI.Combinatorics.ContingencyTables.Counting.CompanionWeightOracle

namespace OAI

/-! # The computed paired counts are the manuscript's literal profile -/

namespace ContingencyTables.PairedProfileSemantics

open PairedProfileProgram CanonicalInitialEncoding InitialTransversals
open CompanionArithmeticProposal CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {q : ℕ} (b : Fin q → ℕ)

def cellRows (S : Set (Copy b × Bool)) : List (List ℕ) :=
  List.ofFn (fun i => interleave (List.ofFn (fun k : Fin (b i) =>
    (if (⟨i,k⟩,false) ∈ S then 1 else 0,
     if (⟨i,k⟩,true) ∈ S then 1 else 0))))

lemma cellRows_lengths (S : Set (Copy b × Bool)) :
    (cellRows b S).map List.length=(List.ofFn b).map width := by
  simp only [cellRows,List.map_ofFn,Function.comp_def,interleave_length,List.length_ofFn,width]

lemma cellRows_flatten (S : Set (Copy b × Bool)) :
    (cellRows b S).flatten=encodeSet (coordinateEquiv b) S := by
  rw [encodeSet_eq_map]
  simp only [cellRows,interleave_flatMap,pairOrder,copyOrder,List.sigma,List.product,
    List.ofFn_eq_map,List.flatten_eq_flatMap,List.flatMap_map,List.map_flatMap,
    List.flatMap_assoc,List.map_map]
  apply List.flatMap_congr
  intro i _
  simp only [id_eq,Function.comp_def]
  apply List.flatMap_congr
  intro k _
  rfl

lemma rows_encode (S : Set (Copy b × Bool)) :
    rows (List.ofFn b,encodeSet (coordinateEquiv b) S)=cellRows b S := by
  rw [rows,←cellRows_lengths b S,←cellRows_flatten b S]
  exact NaturalBlockProgram.blocks_flatten _

lemma counts_cellRow (S : Set (Copy b × Bool)) (i : Fin q) :
    counts (interleave (List.ofFn (fun k : Fin (b i) =>
      (if (⟨i,k⟩,false) ∈ S then 1 else 0,
       if (⟨i,k⟩,true) ∈ S then 1 else 0))))=
      ((∑ k : Fin (b i), if (⟨i,k⟩,false) ∈ S then 1 else 0),
       (∑ k : Fin (b i), if (⟨i,k⟩,true) ∈ S then 1 else 0)) := by
  simp only [counts,sideCount,sideEntries_interleave,List.map_ofFn,Function.comp_def,ite_false,ite_true,
    Bool.false_eq_true,List.sum_ofFn]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> split_ifs <;> simp_all

theorem profileRows_encode (S : Set (Copy b × Bool)) :
    profileRows (List.ofFn b,encodeSet (coordinateEquiv b) S)=List.ofFn (fun i =>
      ((∑ k : Fin (b i), if (⟨i,k⟩,false) ∈ S then 1 else 0),
       (∑ k : Fin (b i), if (⟨i,k⟩,true) ∈ S then 1 else 0))) := by
  rw [profileRows,rows_encode]
  simp only [cellRows,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact counts_cellRow b S i

lemma copy_viewCount (S : Set (Copy b × Bool)) (i : Fin q) (side : Bool) :
    TwoLiftStates.viewCount (fun p : Copy b => p.1) S i side=
      ∑ k : Fin (b i), if (⟨i,k⟩,side) ∈ S then 1 else 0 := by
  unfold TwoLiftStates.viewCount
  rw [Fintype.sum_sigma]
  calc
    _=∑ x : Fin q, if x=i then
        (∑ k : Fin (b x), if (⟨x,k⟩,side) ∈ S then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x=i
      · subst x
        simp
      · simp [hx]
    _=_ := by simp

variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

lemma physical_profile_reindex (S : Set (Labels A × Bool)) (s : SmallCell A) (side : Bool) :
    CompanionWeightOracle.profile A S (s,side)=
      TwoLiftStates.viewCount (fun p : Copy (CompanionComputedInitial.capacities A) => p.1)
        ((CompanionComputedInitial.pairOrder A).symm ⁻¹' S)
        (CompanionComputedInitial.cellOrder A s) side := by
  rw [CompanionWeightOracle.profile,TwoLiftStates.groupCount_eq_viewCount]
  unfold TwoLiftStates.viewCount
  exact Fintype.sum_equiv (CompanionComputedInitial.copyOrder A) _ _ (fun p => by
    have he : (CompanionComputedInitial.copyOrder A p).1=
        CompanionComputedInitial.cellOrder A p.1 := rfl
    simp only [Set.mem_preimage,CompanionComputedInitial.pairOrder,Equiv.prodCongr_symm,
      Equiv.prodCongr_apply,Prod.map_apply,
      Equiv.refl_symm,Equiv.refl_apply,Equiv.symm_apply_apply,
      he,Equiv.apply_eq_iff_eq,CompanionFactorialApplication.labelCell]
    split_ifs <;> simp_all)

/-- The executed rows use the catalog's actual order, with one pair of
counts per retained physical cell. -/
theorem profileRows_physical (S : Set (Labels A × Bool)) :
    profileRows (List.ofFn (CompanionComputedInitial.capacities A),
      encodeSet (CompanionComputedInitial.coordinateOrder A) S)=
      List.ofFn (fun i =>
        (CompanionWeightOracle.profile A S ((CompanionComputedInitial.cellOrder A).symm i,false),
         CompanionWeightOracle.profile A S ((CompanionComputedInitial.cellOrder A).symm i,true))) := by
  rw [CompanionComputedInitial.encodeSet_reindex,profileRows_encode]
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · change _=CompanionWeightOracle.profile A S ((CompanionComputedInitial.cellOrder A).symm i,false)
    exact ((physical_profile_reindex A S _ false).trans
      (by rw [Equiv.apply_symm_apply,copy_viewCount])).symm
  · change _=CompanionWeightOracle.profile A S ((CompanionComputedInitial.cellOrder A).symm i,true)
    exact ((physical_profile_reindex A S _ true).trans
      (by rw [Equiv.apply_symm_apply,copy_viewCount])).symm

end
end ContingencyTables.PairedProfileSemantics

end OAI

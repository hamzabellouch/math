import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeFractionExtra
import OAI.Combinatorics.MatchingCount.Algorithm.TreeScaling

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder

variable {n : ℕ}
def vectorRep (v : Fin n→ℚ) : Vector := List.ofFn fun j=>(j.val,TreeFraction.repr (v j))

lemma rowMax_rep (hn : 2≤n) (G : Fin n→Fin n→ℚ) (v : Fin n→ℚ)
    (hG : ∀ i j,i≠j→0≤G i j) (hv : ∀ j,0≤v j) (i : Fin n) :
    rowMax ((matrixRep G,vectorRep v),i.val)=TreeFraction.repr (Counting.rowMaximum hn G v i) := by
  let js := (List.finRange n).filter (fun j=>decide (j≠i))
  let qs := js.map (fun j=>G i j/v j)
  have hj : ∀ j,j∈js↔j≠i := by intro j; simp [js]
  have hq : ∀ q∈qs,0≤q := by
    intro q h
    obtain ⟨j,hj',rfl⟩:=List.mem_map.mp h
    exact div_nonneg (hG i j ((hj j).mp hj').symm) (hv j)
  have he : ((vectorRep v).filter (fun z=>decide (z.1≠i.val))).map
      (fun z=>ratio ((matrixRep G,i.val),z))=qs.map TreeFraction.repr := by
    unfold vectorRep qs
    rw [List.ofFn_eq_map,List.filter_map,List.map_map,List.map_map]
    have hp : (fun j : Fin n=>decide ((j.val,TreeFraction.repr (v j)).1≠i.val))=
        (fun j=>decide (j≠i)) := by
      funext j
      simp only [ne_eq,Fin.val_inj]
    change List.map _ (List.filter _ (List.finRange n))=_
    rw [show ((fun z : ℕ×Fraction=>decide (z.1≠i.val)) ∘ (fun j : Fin n=>(j.val,TreeFraction.repr (v j))))=
        (fun j=>decide (j≠i)) from hp]
    apply List.map_congr_left
    intro j hj'
    dsimp only [Function.comp_apply,ratio]
    rw [cell_matrixRep,div_repr (hG i j ((hj j).mp hj').symm) (hv j)]
  unfold rowMax
  dsimp only
  rw [he,show ((0,1) : Fraction)=TreeFraction.repr (0:ℚ) from rfl,maximum_fold_repr qs 0 (by decide) hq]
  congr 1
  apply le_antisymm
  · apply fold_max_le
    · obtain ⟨j,hjj⟩:=Counting.others_nonempty hn i
      have hnz:=div_nonneg (hG i j (Finset.mem_erase.mp hjj).1.symm) (hv j)
      exact hnz.trans (Counting.ratio_le_rowMaximum hn G v i j (Finset.mem_erase.mp hjj).1)
    · intro q h
      obtain ⟨j,hj',rfl⟩:=List.mem_map.mp h
      exact Counting.ratio_le_rowMaximum hn G v i j ((hj j).mp hj')
  · apply Finset.sup'_le
    intro j hj'
    exact mem_le_fold_max qs 0 _ (List.mem_map.mpr ⟨j,(hj j).mpr (Finset.mem_erase.mp hj').1,rfl⟩)

lemma set_vectorRep (v : Fin n→ℚ) (i : Fin n) (a : ℚ) :
    setState (vectorRep v,(i.val,TreeFraction.repr a))=vectorRep (Function.update v i a) := by
  unfold setState vectorRep
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply,Function.update_apply,Fin.val_inj]
  split_ifs <;> rfl
lemma step_rep (hn : 2≤n) (G : Fin n→Fin n→ℚ) (v : Fin n→ℚ)
    (hG : ∀ i j,i≠j→0≤G i j) (hv : ∀ j,0≤v j) (i : Fin n) :
    step (i.val,(matrixRep G,vectorRep v))=(matrixRep G,vectorRep (Counting.scaleUpdate hn G v i)) := by
  unfold step
  dsimp only
  rw [rowMax_rep hn G v hG hv i,set_vectorRep]
  rfl
lemma initial_rep (G : Fin n→Fin n→ℚ) : initial (matrixRep G)=(matrixRep G,vectorRep (fun _ : Fin n=>2)) := by
  unfold initial vectorRep
  rw [matrixRep_length]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rfl
lemma sweep_rep (hn : 2≤n) (G : Fin n→Fin n→ℚ)
    (hsym : ∀ i j,G i j=G j i)
    (hG : ∀ i j,i≠j→ Counting.alpha≤G i j ∧ G i j≤3) (k : ℕ) (hk : k≤n) :
    (List.range k).foldl (fun s i=>step (i,s)) (initial (matrixRep G))=
      (matrixRep G,vectorRep (Counting.scalingTrace hn G k)) := by
  induction k with
  | zero=>exact initial_rep G
  | succ k ih=>
    rw [List.range_succ,List.foldl_append,ih (by omega)]
    simp only [List.foldl_cons,List.foldl_nil]
    have hp : ∀ j,0≤Counting.scalingTrace hn G k j := fun j=>
      ((Counting.scalingTrace_invariant hn G hsym hG k).1.pos j).le
    have hG' : ∀ i j,i≠j→0≤G i j := by
      intro i j hij
      exact (by norm_num [Counting.alpha] : (0:ℚ)≤Counting.alpha).trans (hG i j hij).1
    rw [step_rep hn G _ hG' hp (⟨k,by omega⟩ : Fin n)]
    congr 2
    simp only [Counting.scalingTrace,dite_eq_left (show k<n from by omega)]
lemma scale_rep (hn : 2≤n) (G : Fin n→Fin n→ℚ)
    (hsym : ∀ i j,G i j=G j i)
    (hG : ∀ i j,i≠j→ Counting.alpha≤G i j ∧ G i j≤3) :
    scale (matrixRep G)=vectorRep (Counting.scalingTrace hn G n) := by
  unfold scale
  rw [matrixRep_length,sweep_rep hn G hsym hG n le_rfl]
end MatchingFPRAS.ExecutableScaling

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListOrdinal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListActive

namespace OAI

/-! Reindexing the actual fresh-port list by its consecutive mediator number. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem range_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum=∑ i : Fin n, f i.val := by
  have h : List.ofFn (fun i : Fin n => f i.val)=(List.range n).map f := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
  rw [← h,List.sum_ofFn]

theorem fresh_sum {M : Type*} [AddCommMonoid M] (gs : Groups) (f : ℕ → ℕ → M) :
    ((List.range gs.length).map (fun i =>
      ((List.range ((groupAt gs i).length/2)).map (fun j =>
        f i (pairStart gs i+j))).sum)).sum =
      ∑ e : Fin (pairCount gs),
        f (((catalog gs).drop e.val).headD (0,((0,0),(0,0)))).1 e.val := by
  simp only [range_sum]
  have h := (pairEquiv gs).sum_comp (fun e =>
    f (((catalog gs).drop e.val).headD (0,((0,0),(0,0)))).1 e.val)
  simp only [catalog_pairEquiv] at h
  simpa only [LocalPair,Fintype.sum_sigma,pairEquiv_val] using h

theorem next_groupAt (n : ℕ) (R : ℚ) (gs : Groups) (i : ℕ) (hi : i < gs.length) :
    groupAt ((List.range gs.length).map (nextGroup n R gs)) i=nextGroup n R gs i := by
  rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem next_active_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (R : ℚ)
    (gs : Groups) (f : Bond → M) :
    ((activeBonds ((List.range gs.length).map (nextGroup n R gs))).map f).sum =
      ((List.range (pairCount gs)).map (fun e =>
        f ((((catalog gs).drop e).headD (0,((0,0),(0,0)))).1,n+2*e,R))).sum+
      ((unpairedBonds gs).map f).sum := by
  have h : ((List.range gs.length).map (fun i =>
      ((groupAt ((List.range gs.length).map (nextGroup n R gs)) i).map
        (fun p => f (i,p.1,p.2))).sum)) =
      (List.range gs.length).map (fun i =>
        ((List.range ((groupAt gs i).length/2)).map (fun j =>
          f (i,n+2*(pairStart gs i+j),R))).sum+
        ((unpaired (groupAt gs i)).map (fun p => f (i,p.1,p.2))).sum) := by
    apply List.map_congr_left
    intro i hi
    rw [next_groupAt n R gs i (List.mem_range.mp hi)]
    simp only [nextGroup,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  simp only [activeBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,List.length_map,List.length_range]
  rw [h,List.sum_map_add]
  congr 1
  · simpa only [range_sum] using fresh_sum gs (fun i e => f (i,n+2*e,R))
  · simp only [unpairedBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
      Function.comp_def]

end ContinuumCoulomb.QuantumForkList

end

end OAI

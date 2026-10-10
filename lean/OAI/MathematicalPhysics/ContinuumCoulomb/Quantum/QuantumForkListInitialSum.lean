import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialBounds

namespace OAI

/-! Regrouping the literal initial ports recovers the two physical end
couplings of each input edge. The regrouping uses its actual endpoint table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialBond_mem (bs : List Bond) (j : ℕ) (hj : j < 2*bs.length) :
    initialBond bs j ∈ bs := by
  have hi : j/2 < bs.length := by omega
  simp only [initialBond,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem initialEndpoint_bound (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (j : ℕ) (hj : j < 2*bs.length) : initialEndpoint bs j < n := by
  have h := hb _ (initialBond_mem bs j hj)
  unfold initialEndpoint
  split
  · exact h.1
  · exact h.2

theorem initialIndices_sum {M : Type*} [AddCommMonoid M] (bs : List Bond) (i : ℕ)
    (f : ℕ → M) : ((initialIndices bs i).map f).sum =
      ((List.range (2*bs.length)).map (fun j =>
        if initialEndpoint bs j=i then f j else 0)).sum := by
  unfold initialIndices
  generalize List.range (2*bs.length)=xs
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    by_cases h : initialEndpoint bs j=i <;> simp [h,ih]

theorem initial_center_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (j : Fin (2*bs.length)) (f : ℕ → ℕ → M) :
    (∑ i : Fin n, if initialEndpoint bs j.val=i.val then f i.val j.val else 0) =
      f (initialEndpoint bs j.val) j.val := by
  let e : Fin n := ⟨initialEndpoint bs j.val,initialEndpoint_bound n bs hb j.val j.isLt⟩
  rw [Finset.sum_eq_single e]
  · simp only [e,ite_true]
  · intro i _ hi
    exact ite_eq_right (fun h => hi (Fin.ext h.symm))
  · intro h
    exact (h (Finset.mem_univ e)).elim

theorem initial_group_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (R : ℚ) (f : ℕ → Port → M) :
    ((List.range n).map (fun i => ((initialGroup n bs R i).map (f i)).sum)).sum =
      ((List.range (2*bs.length)).map (fun j =>
        f (initialEndpoint bs j) (n+j,initialWeight bs R j))).sum := by
  simp only [initialGroup,List.map_map,Function.comp_def,initialIndices_sum,range_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ =>
    initial_center_sum n bs hb j (fun i k => f i (n+k,initialWeight bs R k)))

end ContinuumCoulomb.QuantumForkList

end

end OAI

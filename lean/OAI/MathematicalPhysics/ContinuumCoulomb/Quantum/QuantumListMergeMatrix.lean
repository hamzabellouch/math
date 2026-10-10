import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListMerge

namespace OAI

/-! Canonical bond merging preserves the complete exchange matrix exactly. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open MediatorListProgram
open scoped BigOperators Classical

private theorem sum_indicator {M : Type} [AddCommMonoid M] (ps : List Pair)
    (hn : ps.Nodup) (p : Pair) (hp : p ∈ ps) (z : M) :
    (ps.map (fun q => if p=q then z else 0)).sum=z := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    obtain ⟨hq,ht⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with rfl | hp
    · have hz : (qs.map (fun q => if p=q then z else 0)).sum=0 := by
        apply List.sum_eq_zero
        intro a ha
        obtain ⟨q,hq',rfl⟩ := List.mem_map.mp ha
        have hne : p≠q := by
          intro he
          subst q
          exact hq hq'
        exact ite_eq_right hne
      simp [hz]
    · have hne : p≠q := fun he => hq (he ▸ hp)
      simpa only [List.map_cons,List.sum_cons,ite_eq_right hne,zero_add] using ih ht hp

private theorem sum_swap {α β M : Type} [AddCommMonoid M]
    (xs : List α) (ys : List β) (f : α → β → M) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.map_cons,List.sum_cons,List.sum_map_add] using
      (congrArg (fun z => (ys.map (f x)).sum+z) ih)

theorem ordered_matrix (n : ℕ) (e : Bond) (he : e.1<n ∧ e.2.1<n) :
    SourceBondLists.bondMatrix n ((ordered e).1,(ordered e).2,e.2.2) =
      SourceBondLists.bondMatrix n e := by
  by_cases h : e.1 ≤ e.2.1
  · simp only [ordered,min_eq_left h,max_eq_right h]
  · have h' : e.2.1 ≤ e.1 := by omega
    simp only [ordered,min_eq_right h',max_eq_left h']
    rw [SourceBondLists.bondMatrix,dite_eq_left ⟨he.2,he.1⟩,
      SourceBondLists.bondMatrix,dite_eq_left he]
    exact congrArg (fun a => (e.2.2:ℂ) • a)
      (qmaHeisenberg_symm n ⟨e.2.1,he.2⟩ ⟨e.1,he.1⟩)

private theorem pairMatrix_add (n : ℕ) (p : Pair) (a b : ℚ) :
    SourceBondLists.bondMatrix n (p.1,p.2,a+b) =
      SourceBondLists.bondMatrix n (p.1,p.2,a)+SourceBondLists.bondMatrix n (p.1,p.2,b) := by
  unfold SourceBondLists.bondMatrix
  split_ifs <;> simp only [Rat.cast_add,add_smul,zero_add]

private theorem pairMatrix_contribution (n : ℕ) (p : Pair) (e : Bond)
    (he : e.1<n ∧ e.2.1<n) :
    SourceBondLists.bondMatrix n (p.1,p.2,if ordered e=p then e.2.2 else 0) =
      if ordered e=p then SourceBondLists.bondMatrix n e else 0 := by
  by_cases h : ordered e=p
  · rw [ite_eq_left h,ite_eq_left h,← h]
    exact ordered_matrix n e he
  · rw [ite_eq_right h,ite_eq_right h]
    exact SourceBondLists.bondMatrix_zero n _ rfl

theorem matrix_row (n : ℕ) (xs : List Bond) (hb : SourceBondLists.bounded n xs) (p : Pair) :
    SourceBondLists.bondMatrix n (p.1,p.2,weight xs p) =
      (xs.map (fun e => if ordered e=p then SourceBondLists.bondMatrix n e else 0)).sum := by
  induction xs with
  | nil => exact SourceBondLists.bondMatrix_zero n _ rfl
  | cons e xs ih =>
    have he := hb e (List.mem_cons_self)
    have ht : SourceBondLists.bounded n xs := fun a ha => hb a (List.mem_cons_of_mem _ ha)
    change SourceBondLists.bondMatrix n
      (p.1,p.2,(if ordered e=p then e.2.2 else 0)+weight xs p) = _
    rw [pairMatrix_add,pairMatrix_contribution n p e he,ih ht]
    rfl

theorem matrix_eq (n : ℕ) (xs : List Bond) (hb : SourceBondLists.bounded n xs) :
    SourceBondLists.matrix n (value n xs)=SourceBondLists.matrix n xs := by
  have hm : (support n xs).map (fun p => SourceBondLists.bondMatrix n (p.1,p.2,weight xs p)) =
      (support n xs).map (fun p => (xs.map
        (fun e => if ordered e=p then SourceBondLists.bondMatrix n e else 0)).sum) := by
    apply List.map_congr_left
    intro p _
    exact matrix_row n xs hb p
  simp only [SourceBondLists.matrix,value,List.map_map,Function.comp_def]
  rw [hm,sum_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact sum_indicator (support n xs) (support_nodup n xs) (ordered e)
    ((mem_support hb _).mpr (List.mem_map.mpr ⟨e,he,rfl⟩)) _

end ContinuumCoulomb.QuantumListMerge

end

end OAI

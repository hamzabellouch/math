import Mathlib.Topology.Clopen
import Mathlib.Data.Fintype.Option

namespace OAI

/-! Finite clopen covers admit disjoint clopen refinements without any
separation or disconnectedness assumption on the ambient space. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma finite_disjoint_clopen_refinement
    {X : Type*} [TopologicalSpace X] (I : Type*) [Finite I] :
    ∀ (D : I → Set X), (∀ i, IsClopen (D i)) →
      ∃ C : I → Set X, (∀ i, IsClopen (C i)) ∧
        Pairwise (fun i j => Disjoint (C i) (C j)) ∧
        (∀ i, C i ⊆ D i) ∧ (⋃ i, C i) = ⋃ i, D i := by
  induction I using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro D hD
    obtain ⟨C,hC,hd,hsub,hcov⟩ := ih (D ∘ e) (fun i => hD (e i))
    refine ⟨C ∘ e.symm,fun i => hC (e.symm i),?_,?_,?_⟩
    · intro i j hij
      exact hd (fun h => hij (e.symm.injective h))
    · intro i
      simpa only [Function.comp_apply,e.apply_symm_apply] using hsub (e.symm i)
    · simp only [Function.comp_apply] at hcov ⊢
      rw [e.symm.surjective.iUnion_comp C,hcov,e.surjective.iUnion_comp D]
  | h_empty =>
    intro D hD
    exact ⟨D,hD,fun i => PEmpty.elim i,fun _ => Subset.rfl,rfl⟩
  | @h_option I inst ih =>
    intro D hD
    let D' : I → Set X := fun i => D (some i) \ D none
    obtain ⟨C,hC,hd,hsub,hcov⟩ := ih D' (fun i => (hD (some i)).diff (hD none))
    let C' : Option I → Set X := fun i => Option.casesOn i (D none) C
    refine ⟨C',?_,?_,?_,?_⟩
    · rintro (_ | i)
      · exact hD none
      · exact hC i
    · rintro (_ | i) (_ | j) hij
      · exact (hij rfl).elim
      · exact Set.disjoint_left.mpr (fun x hx hxC => (hsub j hxC).2 hx)
      · exact Set.disjoint_left.mpr (fun x hxC hx => (hsub i hxC).2 hx)
      · exact hd (fun h => hij (congrArg some h))
    · rintro (_ | i)
      · exact Subset.rfl
      · exact (hsub i).trans sdiff_subset
    · apply Subset.antisymm
      · intro x hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        cases i with
        | none => exact mem_iUnion.mpr ⟨none,hi⟩
        | some i => exact mem_iUnion.mpr ⟨some i,(hsub i hi).1⟩
      · intro x hx
        by_cases hx0 : x ∈ D none
        · exact mem_iUnion.mpr ⟨none,hx0⟩
        · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
          cases i with
          | none => exact (hx0 hi).elim
          | some i =>
            have hx' : x ∈ ⋃ j, D' j := mem_iUnion.mpr ⟨i,hi,hx0⟩
            rw [← hcov] at hx'
            obtain ⟨j,hj⟩ := mem_iUnion.mp hx'
            exact mem_iUnion.mpr ⟨some j,hj⟩

end CircleDomainRigidity

end

end OAI

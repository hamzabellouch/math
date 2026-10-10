import Mathlib.Topology.Separation.Hausdorff

namespace OAI

/-! Pairwise disjoint open neighborhoods of finitely many distinct points,
refining any prescribed neighborhoods. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [Finite ι]

theorem finite_disjoint_open_neighborhoods (p : ι → X) (hi : Function.Injective p)
    (O : ι → Set X) (hO : ∀ i, IsOpen (O i)) (hpO : ∀ i, p i ∈ O i) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i) ∧ p i ∈ U i ∧ U i ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  have hpair : ∀ i j : ι, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ p i ∈ U ∧ p j ∈ V ∧ (i ≠ j → Disjoint U V) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨univ,univ,isOpen_univ,isOpen_univ,mem_univ _,mem_univ _,fun h => False.elim (h hij)⟩
    · obtain ⟨U,V,hU,hV,hpU,hpV,hUV⟩ := t2_separation (fun he => hij (hi he))
      exact ⟨U,V,hU,hV,hpU,hpV,fun _ => hUV⟩
  choose U V hU hV hpU hpV hUV using hpair
  let W : ι → Set X := fun i => O i ∩ (⋂ j, U i j) ∩ (⋂ j, V j i)
  have hW : ∀ i, IsOpen (W i) ∧ p i ∈ W i ∧ W i ⊆ O i := by
    intro i
    refine ⟨((hO i).inter (isOpen_iInter_of_finite (hU i))).inter
      (isOpen_iInter_of_finite (fun j => hV j i)),?_,?_⟩
    · exact ⟨⟨hpO i,mem_iInter.mpr (hpU i)⟩,mem_iInter.mpr (fun j => hpV j i)⟩
    · exact fun _ hx => hx.1.1
  refine ⟨W,hW,?_⟩
  intro i j hij
  apply (hUV i j hij).mono
  · intro x hx
    exact mem_iInter.mp hx.1.2 j
  · intro x hx
    exact mem_iInter.mp hx.2 i

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

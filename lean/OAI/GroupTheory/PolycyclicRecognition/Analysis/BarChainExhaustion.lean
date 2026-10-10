import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

namespace OAI

/-! # Finite support in bar chains along a subgroup exhaustion

Every bar chain has a representative in one member of an increasing exhaustive
sequence of subgroups. The inclusion is injective in every degree.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
variable {G : Type} [Group G]

theorem finite_subset_subgroup_exhaustion (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (T : Finset G) :
    ∃ n, ∀ g ∈ T, g ∈ S n := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert g T _ ih =>
    obtain ⟨i, hi⟩ := hcover g
    obtain ⟨j, hj⟩ := ih
    refine ⟨max i j, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hS (le_max_left _ _) hi
    · exact hS (le_max_right _ _) (hj x hx)

def subgroupBarInclusion (H : Subgroup G) (A : Rep ℤ G) :
    groupHomology.inhomogeneousChains (Rep.res H.subtype A) ⟶
      groupHomology.inhomogeneousChains A :=
  groupHomology.chainsMap H.subtype (𝟙 (Rep.res H.subtype A))

theorem subgroupBarInclusion_injective (H : Subgroup G) (A : Rep ℤ G) (i : ℕ) :
    Function.Injective ((subgroupBarInclusion H A).f i) := by
  apply (ModuleCat.mono_iff_injective _).mp
  exact groupHomology.chainsMap_f_map_mono H.subtype
    (𝟙 (Rep.res H.subtype A)) Subtype.val_injective i

theorem exists_barChain_in_subgroup (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (z : (groupHomology.inhomogeneousChains A).X i) :
    ∃ n, ∃ w : (groupHomology.inhomogeneousChains (Rep.res (S n).subtype A)).X i,
      (subgroupBarInclusion (S n) A).f i w = z := by
  classical
  let T : Finset G := z.support.biUnion fun f => Finset.univ.image f
  obtain ⟨n, hn⟩ := finite_subset_subgroup_exhaustion S hS hcover T
  let f : (Fin i → S n) → (Fin i → G) := fun x => (S n).subtype ∘ x
  have hf : Function.Injective f := by
    intro a b hab
    funext j
    exact Subtype.val_injective (congrFun hab j)
  have hsupport (x : Fin i → G) (hx : x ∈ z.support) : x ∈ Set.range f := by
    refine ⟨fun j => ⟨x j, hn (x j) ?_⟩, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨x, hx,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨w, hw⟩ := (Finsupp.mem_range_mapDomain_iff f hf z).mpr (by
    intro x hx
    apply Finsupp.notMem_support_iff.mp
    exact fun h => hx (hsupport x h))
  refine ⟨n, w, ?_⟩
  simpa [subgroupBarInclusion, groupHomology.chainsMap_f, f] using hw

end PolycyclicRecognition

end

end OAI

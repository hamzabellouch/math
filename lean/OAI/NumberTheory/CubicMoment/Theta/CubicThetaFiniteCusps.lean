import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspDisjointness
import Mathlib.Data.Set.Finite.Basic

namespace OAI

/-! A finite cusp cover can be made disjoint without changing its union
at any height. Representatives are selected from the given arithmetic
charts, so all preceding analytic estimates continue to apply. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspNeighborhood_one_nonempty (δ : SL(2,Eisenstein)) :
    (cubicThetaCuspNeighborhood δ 1).Nonempty := by
  let p : CubicThetaPoint := ⟨(0,2),by norm_num⟩
  refine ⟨cubicThetaQuotientMap (δ • p),cubicThetaCuspNeighborhood_mem_of_height δ p ?_⟩
  norm_num [p,cubicThetaPointHeight,cubicThetaPointCoordinates]

theorem cubicThetaFiniteCusps_disjoint (S : Finset SL(2,Eisenstein)) :
    ∃ T : Finset SL(2,Eisenstein), T⊆S ∧
      (∀ H : ℝ, (⋃ δ∈S, cubicThetaCuspNeighborhood δ H)=
        ⋃ δ∈T, cubicThetaCuspNeighborhood δ H) ∧
      ∀ H : ℝ, 1≤H → (T : Set SL(2,Eisenstein)).PairwiseDisjoint
        (fun δ => cubicThetaCuspNeighborhood δ H) := by
  classical
  let f : SL(2,Eisenstein) → Set CubicThetaQuotient := fun δ => cubicThetaCuspNeighborhood δ 1
  have hs : (S : Set SL(2,Eisenstein)).SurjOn f (S.image f) := by
    intro U hU
    exact Finset.mem_image.mp hU
  obtain ⟨T,hTS,hT,himage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (S : Set SL(2,Eisenstein)) (S.image f) hs
  have hrep (δ : SL(2,Eisenstein)) (hδ : δ∈S) :
      ∃ ε∈T, ∀ H : ℝ, cubicThetaCuspNeighborhood δ H=cubicThetaCuspNeighborhood ε H := by
    have hmem : f δ∈T.image f := by rw [himage]; exact Finset.mem_image.mpr ⟨δ,hδ,rfl⟩
    obtain ⟨ε,hε,he⟩ := Finset.mem_image.mp hmem
    obtain ⟨q,hq⟩ := cubicThetaCuspNeighborhood_one_nonempty δ
    have hne : (cubicThetaCuspNeighborhood δ 1 ∩ cubicThetaCuspNeighborhood ε 1).Nonempty := by
      refine ⟨q,hq,?_⟩
      change q∈f ε
      rw [he]
      exact hq
    exact ⟨ε,hε,cubicThetaCuspNeighborhood_overlap δ ε (le_refl 1) hne⟩
  refine ⟨T,hTS,?_,?_⟩
  · intro H
    ext q
    constructor
    · intro hq
      obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hq
      obtain ⟨ε,hε,he⟩ := hrep δ hδ
      exact mem_iUnion₂.mpr ⟨ε,hε,(he H) ▸ hqδ⟩
    · intro hq
      obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hq
      exact mem_iUnion₂.mpr ⟨δ,hTS hδ,hqδ⟩
  · intro H hH δ hδ ε hε hne
    apply Set.disjoint_left.mpr
    intro q hqδ hqε
    have he := cubicThetaCuspNeighborhood_overlap δ ε hH ⟨q,hqδ,hqε⟩ 1
    exact hne (hT hδ hε he)

end CubicFirstMoment

end

end OAI

import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureEuler
import OAI.Geometry.HyperbolicGroups.MappedPicture
import OAI.Geometry.HyperbolicGroups.PictureRestrict

namespace OAI

section
section
noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D]

namespace PictureMap
variable (M : PictureMap D) (P : D → Prop)

/-- A union of whole polygonal components can be kept, discarding the others.
This is a literal restriction of both permutations. -/
def restrict (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    PictureMap (Subtype P) where
  face := M.face.subtypePerm hf
  edge := M.edge.subtypePerm he
  edge_sq := by
    ext x
    exact M.edge_edge x.val
  edge_ne := by
    intro x hx
    exact M.edge_ne x.val (congrArg Subtype.val hx)

omit [Fintype D] in
lemma restrict_vertex (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    (M.restrict P hf he).vertex = M.vertex.subtypePerm (fun x => (hf (M.edge x)).trans (he x)) := by
  ext x
  rfl

lemma restrict_components (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    (M.restrict P hf he).components = M.components.comap (Subtype.val : Subtype P → D) := by
  rw [components,restrict_vertex,components]
  have hv : ∀ x, P (M.vertex x) ↔ P x := fun x => (hf (M.edge x)).trans (he x)
  rw [comap_sup_of_invariant _ _ P (invariant_of_sameCycle M.vertex hv)
    (invariant_of_sameCycle M.edge he)]
  congr 1
  · ext x y
    exact sameCycle_subtypePerm_iff M.vertex hv x y
  · ext x y
    exact sameCycle_subtypePerm_iff M.edge he x y

lemma component_invariant (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x)
    {x y : D} (h : M.components x y) : P x ↔ P y := by
  have hh : M.components ≤ Setoid.ker P :=
    M.components_le (fun x => propext (hf x).symm) (fun x => propext (he x).symm)
  exact Iff.of_eq (hh h)

lemma components_split (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    Nat.card (Quotient M.components) =
      Nat.card (Quotient (M.restrict P hf he).components) +
      Nat.card (Quotient (M.restrict (fun x => ¬ P x)
        (fun x => not_congr (hf x)) (fun x => not_congr (he x))).components) := by
  rw [restrict_components,restrict_components]
  exact card_quotient_split M.components P (M.component_invariant P hf he)

variable [DecidableEq D]

lemma card_darts_even (M : PictureMap D) : ∃ n : ℤ, (Fintype.card D : ℤ) = 2*n := by
  obtain ⟨l,_,hc,_⟩ := involution_pairs M.edge M.edge_sq
  have hs : M.edge.support = Finset.univ := by ext x; simp [mem_support,M.edge_ne]
  rw [hs,Finset.card_univ] at hc
  exact ⟨l.length,by exact_mod_cast hc.symm⟩

/-- The Euler characteristic is additive over actual invariant dart subsets. -/
theorem euler_split (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    M.euler = (M.restrict P hf he).euler + (M.restrict (fun x => ¬ P x)
      (fun x => not_congr (hf x)) (fun x => not_congr (he x))).euler := by
  have hc := Fintype.card_congr (Equiv.sumCompl P)
  rw [Fintype.card_sum] at hc
  obtain ⟨n,hn⟩ := (M.restrict P hf he).card_darts_even
  obtain ⟨m,hm⟩ := (M.restrict (fun x => ¬ P x)
    (fun x => not_congr (hf x)) (fun x => not_congr (he x))).card_darts_even
  have hv := cycles_subtype_split M.vertex (fun x => (hf (M.edge x)).trans (he x))
  have hface := cycles_subtype_split M.face hf
  simp only [euler]
  rw [M.restrict_vertex P hf he,M.restrict_vertex (fun x => ¬ P x)
    (fun x => not_congr (hf x)) (fun x => not_congr (he x))]
  dsimp only [restrict]
  have hc' : (Fintype.card D : ℤ) = Fintype.card (Subtype P) + Fintype.card {x : D // ¬ P x} := by
    exact_mod_cast hc.symm
  omega

/-- Discarding components of a genus-zero picture preserves genus zero. This
justifies keeping the disk component and deleting sphere components after
crosswise switches, at the level of the actual finite side-pairing. -/
theorem restrict_genusZero (hM : M.GenusZero)
    (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    (M.restrict P hf he).GenusZero := by
  have hE := M.euler_split P hf he
  have hC := M.components_split P hf he
  have h₁ := (M.restrict P hf he).euler_le
  have h₂ := (M.restrict (fun x => ¬ P x)
    (fun x => not_congr (hf x)) (fun x => not_congr (he x))).euler_le
  change M.euler = _ at hM
  change (M.restrict P hf he).euler = _
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI

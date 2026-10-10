import Mathlib
import OAI.Geometry.HyperbolicGroups.CycleCount
import OAI.Geometry.HyperbolicGroups.PermEuler
import OAI.Geometry.HyperbolicGroups.InvolutionPairs
import OAI.Geometry.HyperbolicGroups.MappedPicture

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

omit [DecidableEq D] [Fintype D] in
lemma joins_append (s : Setoid D) (l r : List (D × D)) :
    joins s (l ++ r) = joins (joins s l) r := by
  induction l generalizing s with
  | nil => rfl
  | cons ab l ih => exact ih _

omit [Fintype D] in
lemma swaps_append (l r : List (D × D)) : swaps (l ++ r) = swaps l * swaps r := by
  simp only [swaps,List.map_append,List.prod_append]

/-- Equality in the Euler potential propagates to every initial segment.
It therefore rules out a hidden handle in every sub-pairing, not only in the
fully glued surface. -/
lemma potential_prefix_eq {p : Perm D} {s : Setoid D}
    (hp : SameCycle.setoid p ≤ s) (l r : List (D × D))
    (he : cycles (p * swaps (l ++ r)) - 2 * (Nat.card (Quotient (joins s (l ++ r))) : ℤ) =
      cycles p - 2 * (Nat.card (Quotient s) : ℤ) + (l ++ r).length) :
    cycles (p * swaps l) - 2 * (Nat.card (Quotient (joins s l)) : ℤ) =
      cycles p - 2 * (Nat.card (Quotient s) : ℤ) + l.length := by
  have h₁ := potential_list hp l
  have h₂ := potential_list (sameCycle_joins hp l) r
  rw [swaps_append,joins_append,← mul_assoc,List.length_append,Nat.cast_add] at he
  omega

/-- At an Euler-equality step, an edge already in a connected component MUST
split a boundary cycle. Merging two boundary cycles within that component
would create a handle and strictly lose two units of Euler potential. -/
lemma potential_step_sameCycle {p : Perm D} {s : Setoid D}
    (hp : SameCycle.setoid p ≤ s) (a b : D)
    (he : cycles (p * swap a b) - 2 * (Nat.card (Quotient (glue s a b)) : ℤ) =
      cycles p - 2 * (Nat.card (Quotient s) : ℤ) + 1) :
    p.SameCycle a b ↔ s a b := by
  refine ⟨fun h => hp h,?_⟩
  intro hs
  by_contra hn
  rw [glue_eq_of_rel _ _ _ hs] at he
  have hc := cycles_merge_right p hn
  omega

namespace PictureMap
variable (M : PictureMap D)

lemma paired_joins (l : List (D × D)) (hl : swaps l = M.edge)
    (hpairs : ∀ ab ∈ l, M.edge ab.1 = ab.2) :
    joins (SameCycle.setoid M.vertex) l = M.components := by
  apply le_antisymm
  · apply joins_le _ _ _ M.vertex_le_components
    intro ab hab
    apply M.edge_le_components
    rw [← hpairs ab hab]
    exact SameCycle.rfl.apply_right
  · apply sup_le
    · exact le_joins _ _
    · have h₁ : SameCycle.setoid (1 : Perm D) ≤ SameCycle.setoid M.vertex := by
        intro a b hab
        exact (hab.eq_of_left rfl).sameCycle M.vertex
      have h := sameCycle_joins h₁ l
      simpa only [one_mul,hl] using h

lemma paired_potential_eq (hG : M.GenusZero) (l : List (D × D))
    (hl : swaps l = M.edge) (hn : 2 * l.length = Fintype.card D)
    (hpairs : ∀ ab ∈ l, M.edge ab.1 = ab.2) :
    cycles (M.vertex * swaps l) -
      2 * (Nat.card (Quotient (joins (SameCycle.setoid M.vertex) l)) : ℤ) =
      cycles M.vertex - 2 * (Nat.card (Quotient (SameCycle.setoid M.vertex)) : ℤ) + l.length := by
  rw [M.paired_joins l hl hpairs,hl]
  have hv : M.vertex * M.edge = M.face := by rw [vertex,mul_assoc,M.edge_sq,mul_one]
  rw [hv,← cycles_eq_card_classes]
  have he : M.euler = cycles M.vertex + cycles M.face - l.length := by
    rw [euler]
    omega
  change M.euler = _ at hG
  omega

/-- Every actual genus-zero side pairing admits an edge ordering in which
EVERY partial gluing is maximally planar. This is a finite-permutation
consequence of the actual Euler definition, not a planarity assumption. -/
theorem planar_pairing_order (hG : M.GenusZero) :
    ∃ l : List (D × D), swaps l = M.edge ∧ 2 * l.length = Fintype.card D ∧
      (∀ ab ∈ l, ab.1 ≠ ab.2 ∧ M.edge ab.1 = ab.2) ∧
      ∀ (r t : List (D × D)) (a b : D), l = r ++ (a,b)::t →
        ((M.vertex * swaps r).SameCycle a b ↔ joins (SameCycle.setoid M.vertex) r a b) := by
  obtain ⟨l,hl,hn,hpairs⟩ := involution_pairs M.edge M.edge_sq
  have hsupp : M.edge.support = Finset.univ := by
    ext x; simp only [mem_support,Finset.mem_univ,iff_true]; exact M.edge_ne x
  rw [hsupp,Finset.card_univ] at hn
  refine ⟨l,hl,hn,hpairs,?_⟩
  intro r t a b he
  have hfull := M.paired_potential_eq hG l hl hn (fun ab hab => (hpairs ab hab).2)
  rw [he] at hfull
  have hr := potential_prefix_eq (p := M.vertex) (s := SameCycle.setoid M.vertex) le_rfl r ((a,b)::t) hfull
  have hmid : cycles (M.vertex * swaps (r ++ [(a,b)])) -
      2 * (Nat.card (Quotient (joins (SameCycle.setoid M.vertex) (r ++ [(a,b)]))) : ℤ) =
      cycles M.vertex - 2 * (Nat.card (Quotient (SameCycle.setoid M.vertex)) : ℤ) + (r ++ [(a,b)]).length := by
    apply potential_prefix_eq (p := M.vertex) (s := SameCycle.setoid M.vertex) le_rfl (r ++ [(a,b)]) t
    simpa only [List.append_assoc,List.singleton_append] using hfull
  apply potential_step_sameCycle (sameCycle_joins (p := M.vertex) (s := SameCycle.setoid M.vertex) le_rfl r) a b
  rw [swaps_append,show swaps [(a,b)] = swap a b from by simp only [swaps,List.map_cons,
      List.map_nil,List.prod_cons,List.prod_nil,mul_one],← mul_assoc,joins_append] at hmid
  simp only [joins,List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one] at hmid
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI

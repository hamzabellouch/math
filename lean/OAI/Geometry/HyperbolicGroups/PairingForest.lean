import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.CycleCount
import OAI.Geometry.HyperbolicGroups.PermEuler
import OAI.Geometry.HyperbolicGroups.InvolutionPairs
import OAI.Geometry.HyperbolicGroups.PlanarSubpairing

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}

/-- Kruskal's spanning forest, retaining literal paired-side indices. -/
def forestEdges (s : Setoid D) : List (D × D) → List (D × D)
  | [] => []
  | (a,b)::l => if s a b then forestEdges s l else (a,b)::forestEdges (glue s a b) l

lemma forestEdges_sublist (s : Setoid D) (l : List (D × D)) : (forestEdges s l).Sublist l := by
  induction l generalizing s with
  | nil => exact List.Sublist.refl _
  | cons ab l ih =>
    simp only [forestEdges]
    split_ifs
    · exact (ih s).cons _
    · exact (ih _).cons_cons _

lemma forestEdges_joins (s : Setoid D) (l : List (D × D)) :
    joins s (forestEdges s l) = joins s l := by
  induction l generalizing s with
  | nil => rfl
  | cons ab l ih =>
    simp only [forestEdges]
    split_ifs with h
    · rw [ih,joins,glue_eq_of_rel _ _ _ h]
    · exact ih _

variable [Fintype D]

lemma forestEdges_card (s : Setoid D) (l : List (D × D)) :
    (Nat.card (Quotient (joins s l)) : ℤ) + (forestEdges s l).length = Nat.card (Quotient s) := by
  induction l generalizing s with
  | nil => simp only [joins,forestEdges,List.length_nil,Nat.cast_zero,add_zero]
  | cons ab l ih =>
    simp only [forestEdges]
    split_ifs with h
    · rw [joins,glue_eq_of_rel _ _ _ h]; exact ih s
    · have hc := card_glue s ab.1 ab.2
      rw [ite_eq_right h] at hc
      have hh := ih (glue s ab.1 ab.2)
      simp only [joins,List.length_cons,Nat.cast_add,Nat.cast_one]
      omega

variable [DecidableEq D]

lemma forestEdges_cycles (p : Perm D) (s : Setoid D) (hp : SameCycle.setoid p ≤ s)
    (l : List (D × D)) :
    cycles (p * swaps (forestEdges s l)) = cycles p - (forestEdges s l).length := by
  induction l generalizing p s with
  | nil => simp only [forestEdges,swaps,List.map_nil,List.prod_nil,mul_one,List.length_nil,Nat.cast_zero,sub_zero]
  | cons ab l ih =>
    simp only [forestEdges]
    split_ifs with h
    · exact ih p s hp
    · have hh := ih (p * swap ab.1 ab.2) (glue s ab.1 ab.2) (sameCycle_glue hp _ _)
      have hc := cycles_merge_right p (fun hab => h (hp hab))
      have he : swaps (ab :: forestEdges (glue s ab.1 ab.2) l) =
          swap ab.1 ab.2 * swaps (forestEdges (glue s ab.1 ab.2) l) := rfl
      rw [he,← mul_assoc,hh]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      omega

omit [DecidableEq D] in
lemma setoid_eq_of_card_eq {s t : Setoid D} (hle : s ≤ t)
    (hc : Nat.card (Quotient s) = Nat.card (Quotient t)) : s = t := by
  let f : Quotient s → Quotient t := Quotient.map id (fun _ _ h => hle h)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
    exact ⟨Quotient.mk s x,rfl⟩
  have hi : Function.Injective f := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hc⟩).1
  apply le_antisymm hle
  intro x y h
  exact Quotient.exact (hi (show f (Quotient.mk s x) = f (Quotient.mk s y) from Quotient.sound h))

namespace PictureMap
variable (M : PictureMap D)

omit [Fintype D] in
lemma swap_subpair (a b : D) (he : M.edge a = b) (x : D) :
    swap a b x = x ∨ swap a b x = M.edge x := by
  by_cases ha : x = a
  · subst x; exact Or.inr (by rw [swap_apply_left,he])
  by_cases hb : x = b
  · subst x; apply Or.inr
    rw [swap_apply_right,← he,M.edge_edge]
  · exact Or.inl (swap_apply_of_ne_of_ne ha hb)

omit [Fintype D] [DecidableEq D] in
lemma subpairing_mul (q r : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)
    (hr : ∀ x, r x = x ∨ r x = M.edge x) (x : D) :
    (q*r) x = x ∨ (q*r) x = M.edge x := by
  rw [mul_apply]
  rcases hr x with hx | hx
  · rw [hx]; exact hq x
  · rw [hx,M.subpairing_edge q hq x]
    rcases hq x with hy | hy
    · exact Or.inr (congrArg M.edge hy)
    · exact Or.inl ((congrArg M.edge hy).trans (M.edge_edge x))

omit [Fintype D] in
lemma swaps_subpairing (l : List (D × D)) (hl : ∀ ab ∈ l, M.edge ab.1 = ab.2) (x : D) :
    swaps l x = x ∨ swaps l x = M.edge x := by
  induction l generalizing x with
  | nil => exact Or.inl rfl
  | cons ab l ih =>
    apply M.subpairing_mul (swap ab.1 ab.2) (swaps l)
    · exact M.swap_subpair _ _ (hl _ (by simp))
    · exact ih (fun cd hc => hl cd (List.mem_cons_of_mem _ hc))

/-- An actual spanning forest sub-pairing. It has precisely one boundary
cycle per component; no topological drawing, tree axiom, or separator is
assumed. This constructor is valid even before imposing genus zero. -/
theorem spanning_forest : ∃ q : Perm D,
    (∀ x, q x = x ∨ q x = M.edge x) ∧
    SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = M.components ∧
    cycles (M.vertex * q) = (Nat.card (Quotient M.components) : ℤ) := by
  obtain ⟨l,hl,hn,hpairs⟩ := involution_pairs M.edge M.edge_sq
  let t := forestEdges (SameCycle.setoid M.vertex) l
  let q := swaps t
  have hmem : ∀ ab ∈ t, M.edge ab.1 = ab.2 := by
    intro ab hab
    exact (hpairs ab ((forestEdges_sublist _ l).subset hab)).2
  have hq := M.swaps_subpairing t hmem
  have hb : cycles (M.vertex * q) = (Nat.card (Quotient M.components) : ℤ) := by
    have hc := forestEdges_cycles M.vertex (SameCycle.setoid M.vertex) le_rfl l
    have hn := forestEdges_card (SameCycle.setoid M.vertex) l
    rw [M.paired_joins l hl (fun ab hab => (hpairs ab hab).2),← cycles_eq_card_classes] at hn
    change cycles (M.vertex * q) = _ at hc
    omega
  have hle : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q ≤ M.components := by
    apply sup_le M.vertex_le_components
    apply sameCycle_le_of_apply
    intro x
    rcases hq x with hx | hx
    · rw [hx]
    · rw [hx]; exact M.edge_le_components SameCycle.rfl.apply_right
  have hvq : SameCycle.setoid (M.vertex*q) ≤ SameCycle.setoid M.vertex ⊔ SameCycle.setoid q :=
    sameCycle_mul_le le_sup_left le_sup_right
  have heq : SameCycle.setoid (M.vertex*q) = M.components := by
    apply setoid_eq_of_card_eq (hvq.trans hle)
    rw [cycles_eq_card_classes] at hb
    exact_mod_cast hb
  refine ⟨q,hq,le_antisymm hle ?_,hb⟩
  rw [← heq]
  exact hvq

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI

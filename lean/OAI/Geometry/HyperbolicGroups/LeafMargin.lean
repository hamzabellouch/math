import Mathlib
import OAI.Geometry.HyperbolicGroups.StarIncidence

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B : Type*} [Fintype F] [Fintype R] [Fintype B]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [Nonempty B]

omit [Fintype F] [Fintype B] [DecidableEq B] [Nonempty B] in
lemma coord_eq_inr (U : Finset F) {j k : B} {g : F} {f : {f : F // f ∉ U}}
    (h : coord U k g = Sum.inr (j,f)) : k = j ∧ g = f.val := by
  by_cases hg : g ∈ U
  · simp [coord,hg] at h
  · have hh : (k,(⟨g,hg⟩ : {f : F // f ∉ U})) = (j,f) := by
      exact Sum.inr.inj (by simpa only [coord,hg,↓reduceDIte] using h)
    exact ⟨congrArg Prod.fst hh,congrArg (fun q : B × {f : F // f ∉ U} => q.2.val) hh⟩

omit [Fintype F] [Fintype R] [Fintype B] [DecidableEq R] in
lemma rowSupport_nonempty (support : R → Finset F) (U : Finset F)
    (hn : ∀ r, (support r).Nonempty) (s : Pos (B := B) support U) :
    (rowSupport support U s).Nonempty := (hn _).image _

omit [Fintype F] [Fintype R] [Fintype B] [DecidableEq R] in
lemma selected_active (support : R → Finset F) (U : Finset F)
    (hsupp : ∀ r, 3 ≤ (support r).card)
    (J : Finset (Pos (B := B) support U)) (hJ : J.Nonempty) :
    let W := J.biUnion (rowSupport support U)
    center U W = ∅ →
      (∃ j, (wing U W j).Nonempty) ∧ ∀ j, (wing U W j).Nonempty → 3 ≤ (wing U W j).card := by
  dsimp only
  intro hctr
  have hW : ∀ s ∈ J, rowSupport support U s ⊆ J.biUnion (rowSupport support U) := by
    intro s hs
    exact Finset.subset_biUnion_of_mem (rowSupport support U) hs
  have hin (s : Pos (B := B) support U) (hs : s ∈ J) :
      support (array support U s) ⊆ wing U (J.biUnion (rowSupport support U)) (branch support U s) := by
    have hh := (support_subset support U _ s).mp (hW s hs)
    simpa only [hctr,Finset.empty_union] using hh
  constructor
  · obtain ⟨s,hs⟩ := hJ
    exact ⟨branch support U s,(Finset.card_pos.mp (by have := hsupp (array support U s); omega)).mono (hin s hs)⟩
  · intro j hj
    obtain ⟨f,hf⟩ := hj
    have hfu : f ∉ U := fun hfU => Finset.disjoint_left.mp (wing_disjoint U _ j) hfU hf
    have hm := (mem_wing U _ j ⟨f,hfu⟩).mp hf
    obtain ⟨s,hs,hv⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨g,hg,he⟩ := Finset.mem_image.mp hv
    have hbj := (coord_eq_inr U he).1
    exact (hsupp _).trans (Finset.card_le_card (by simpa only [hbj] using hin s hs))

/-- The entire e-field, in all branches, is pinned in the leaf count. -/
def leafPins (U : Finset F) (e : F) : Finset (Var (B := B) U) :=
  Finset.univ.filter (fun v => field U v = e)

omit [DecidableEq B] [Nonempty B] in
@[simp] lemma mem_leafPins (U : Finset F) (e : F) (v : Var (B := B) U) :
    v ∈ leafPins U e ↔ field U v = e := by
  simp only [leafPins,Finset.mem_filter,Finset.mem_univ,true_and]

lemma card_inter_leaf (U : Finset F) (e : F) (he : e ∉ U)
    (W : Finset (Var (B := B) U)) :
    (W ∩ leafPins U e).card = (Finset.univ.filter (fun j => e ∈ wing U W j)).card := by
  let f : B → Var (B := B) U := fun j => Sum.inr (j,⟨e,he⟩)
  have hi : Function.Injective f := by
    intro j k hjk
    exact congrArg Prod.fst (Sum.inr.inj hjk)
  have hm : W ∩ leafPins U e = (Finset.univ.filter (fun j => e ∈ wing U W j)).image f := by
    ext v
    cases v with
    | inl g =>
      have hge : g.val ≠ e := fun h => he (h ▸ g.property)
      simp only [Finset.mem_inter,mem_leafPins,field,hge,and_false,Finset.mem_image]
      simp [f]
    | inr jg =>
      obtain ⟨j,g⟩ := jg
      simp only [Finset.mem_inter,mem_leafPins,Finset.mem_filter,Finset.mem_univ,true_and,field,
        Finset.mem_image]
      constructor
      · rintro ⟨hv,hge⟩
        have hg : g = (⟨e,he⟩ : {f : F // f ∉ U}) := Subtype.ext hge
        subst g
        exact ⟨j,(mem_wing U W j ⟨e,he⟩).mpr hv,rfl⟩
      · rintro ⟨k,hk,hkv⟩
        have hjg : (k,(⟨e,he⟩ : {f : F // f ∉ U})) = (j,g) := Sum.inr.inj hkv
        have hj : k = j := congrArg Prod.fst hjg
        have hg : (⟨e,he⟩ : {f : F // f ∉ U}) = g := congrArg Prod.snd hjg
        subst k
        subst g
        exact ⟨(mem_wing U W j ⟨e,he⟩).mp hk,rfl⟩
  rw [hm,Finset.card_image_of_injective _ hi]

lemma free_card_leaf (U : Finset F) (e : F) (he : e ∉ U)
    (W : Finset (Var (B := B) U)) :
    ((W \ leafPins U e).card : ℤ) = (W.card : ℤ) - ∑ j : B, if e ∈ wing U W j then (1 : ℤ) else 0 := by
  have hh := Finset.card_sdiff_add_card_inter W (leafPins U e)
  rw [card_inter_leaf U e he] at hh
  have hi : ((Finset.univ.filter (fun j : B => e ∈ wing U W j)).card : ℤ) =
      ∑ j : B, if e ∈ wing U W j then (1 : ℤ) else 0 := by simp
  have hh' : ((W \ leafPins U e).card : ℤ) +
      ((Finset.univ.filter (fun j : B => e ∈ wing U W j)).card : ℤ) = W.card := by exact_mod_cast hh
  rw [hi] at hh'
  omega

omit [DecidableEq R] in
/-- Exact critical excess for the shared unconditioned entries in a leaf count.
Every nonempty selected set is a genuine union of row supports. -/
theorem leaf_critical_gap (P : SparsePattern.Pattern F R) (U : Finset F) (e : F) (he : e ∉ U)
    (budget : ∀ W : Finset F, (min 2 W.card : ℕ) ≤ P.exponent W)
    (supports : ∀ r, 3 ≤ (P.support r).card)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ P.exponent (U ∪ W) - P.exponent U)
    (J : Finset (Pos (B := B) P.support U)) (hJ : J.Nonempty) :
    1 ≤ (((J.biUnion (rowSupport P.support U)) \ leafPins U e).card : ℤ) -
      ∑ s ∈ J, P.cost (array P.support U s) := by
  let W := J.biUnion (rowSupport P.support U)
  have hl := P.leaf_margin (e := e) (center_subset U W) (wing_disjoint U W)
    budget supports gap (selected_active P.support U supports J hJ)
  rw [star_exponent_eq] at hl
  have hs := selected_cost P U J W (fun s hs => Finset.subset_biUnion_of_mem _ hs)
  have hc := free_card_leaf U e he W
  change 1 ≤ ((W \ leafPins U e).card : ℤ) - _
  omega

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI

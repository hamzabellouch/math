import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.List.Infix

namespace OAI
noncomputable section
namespace CuntzPureness
local instance freeGroupFiniteSeparationDecidableEq {α : Type*} :
    DecidableEq α := Classical.decEq α

lemma finite_translation_permutation {G : Type*} [Group G] (S : Finset G) (g : G) :
    ∃ p : Equiv.Perm S, ∀ x : S, g*x.1 ∈ S → (p x).1 = g*x.1 := by
  let D := {x : S // g*x.1 ∈ S}
  let f : D → S := Subtype.val
  let k : D → S := fun x => ⟨g*x.1.1,x.2⟩
  have hf : Function.Injective f := Subtype.val_injective
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val h)
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair f k hf hk
  refine ⟨p,fun x hx => ?_⟩
  exact congrArg Subtype.val (hp ⟨x,hx⟩)

variable {α : Type*}

def freeWordValue (w : List (α × Bool)) : FreeGroup α :=
  (w.map (fun x => bif x.2 then FreeGroup.of x.1 else (FreeGroup.of x.1)⁻¹)).prod

lemma freeWordValue_eq_mk (w : List (α × Bool)) : freeWordValue w = FreeGroup.mk w := by
  simpa [freeWordValue] using (FreeGroup.lift_of_apply (FreeGroup.mk w))

lemma finite_word_model (S : Finset (FreeGroup α)) (h1 : 1 ∈ S)
    (p : α → Equiv.Perm S)
    (hp : ∀ a (x : S), FreeGroup.of a*x.1 ∈ S → (p a x).1 = FreeGroup.of a*x.1)
    (w : List (α × Bool))
    (hw : ∀ t ∈ w.tails, freeWordValue t ∈ S) :
    ((FreeGroup.lift p (FreeGroup.mk w)) ⟨1,h1⟩).1 = freeWordValue w := by
  induction w with
  | nil => simp [freeWordValue]
  | cons ab w ih =>
    have ht : ∀ t ∈ w.tails, freeWordValue t ∈ S := fun t ht => hw t (by simp [ht])
    have hv := hw (ab::w) (by simp)
    have ih' := ih ht
    let x : S := (FreeGroup.lift p (FreeGroup.mk w)) ⟨1,h1⟩
    have hx : x.1 = freeWordValue w := ih'
    rcases ab with ⟨a,b⟩
    cases b with
    | true =>
      have hg : FreeGroup.of a*x.1 ∈ S := by simpa [freeWordValue, hx] using hv
      have he := hp a x hg
      rw [hx] at he
      simpa [FreeGroup.lift_mk, freeWordValue, Equiv.Perm.mul_apply, x] using he
    | false =>
      have hg : (FreeGroup.of a)⁻¹*x.1 ∈ S := by simpa [freeWordValue, hx] using hv
      let y : S := ⟨(FreeGroup.of a)⁻¹*x.1,hg⟩
      have he : p a y = x := by
        apply Subtype.ext
        exact (hp a y (by simp [y])).trans (by simp [y])
      have hi : (p a)⁻¹ x = y := by rw [← he]; simp
      have hiv := congrArg Subtype.val hi
      change ((p a)⁻¹ x).1 = (FreeGroup.of a)⁻¹*x.1 at hiv
      rw [hx] at hiv
      simpa [FreeGroup.lift_mk, freeWordValue, Equiv.Perm.mul_apply, x, y] using hiv

theorem freeGroup_exists_finite_permutation (g : FreeGroup α) (hg : g ≠ 1) :
    ∃ (S : Finset (FreeGroup α)) (p : FreeGroup α →* Equiv.Perm S), p g ≠ 1 := by
  obtain ⟨w,rfl⟩ : ∃ w, FreeGroup.mk w = g := Quot.exists_rep g
  let S := (w.tails.map freeWordValue).toFinset
  have hw : ∀ t ∈ w.tails, freeWordValue t ∈ S := by
    intro t ht
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩)
  have h1 : 1 ∈ S := by simpa [freeWordValue] using hw [] (by simp)
  choose p hp using (fun a : α => finite_translation_permutation S (FreeGroup.of a))
  refine ⟨S,FreeGroup.lift p,?_⟩
  intro he
  have hv := finite_word_model S h1 p hp w hw
  rw [he] at hv
  exact hg (freeWordValue_eq_mk w |>.symm.trans hv.symm)

theorem freeGroup_residuallyFinite : Group.ResiduallyFinite (FreeGroup α) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  obtain ⟨S,p,hp⟩ := freeGroup_exists_finite_permutation g hg
  exact ⟨Equiv.Perm S,inferInstance,inferInstance,p,hp⟩
end CuntzPureness

end

end OAI

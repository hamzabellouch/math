import Mathlib.GroupTheory.FreeGroup.Orbit

namespace OAI
noncomputable section
namespace CuntzPureness
local instance freeGroupFirstLetterDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
variable {X : Type*}

theorem freeGroup_firstLetter_image (w : X × Bool) :
    (fun g : FreeGroup X => FreeGroup.mk [w] * g) ''
      (FreeGroup.startsWith (w.1, !w.2))ᶜ = FreeGroup.startsWith w := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact FreeGroup.startsWith_mk_mul g hg
  · intro hz
    cases he : z.toWord with
    | nil => simp [FreeGroup.startsWith, he] at hz
    | cons p l =>
      have hp : p = w := by simpa [FreeGroup.startsWith, he] using hz
      subst p
      have hred : FreeGroup.IsReduced (w :: l) := he ▸ FreeGroup.isReduced_toWord
      have hl : FreeGroup.IsReduced l := hred.tail
      have hn : FreeGroup.mk l ∉ FreeGroup.startsWith (w.1, !w.2) := by
        cases l with
        | nil => simp [FreeGroup.startsWith]
        | cons q l =>
          have hq := (FreeGroup.isReduced_cons_cons.mp hred).1
          simp only [FreeGroup.startsWith, Set.mem_ofPred_eq, FreeGroup.toWord_mk,
            hl.reduce_eq, List.getElem?_cons_zero, Option.some.injEq]
          intro h
          subst q
          have hb := hq rfl
          cases w.2 <;> simp at hb
      refine ⟨FreeGroup.mk l, hn, ?_⟩
      change FreeGroup.mk [w] * FreeGroup.mk l = z
      rw [FreeGroup.mul_mk]
      simp only [List.singleton_append, ← he, FreeGroup.mk_toWord]

theorem freeGroup_firstLetter_disjoint (i j : X) (b c : Bool) (h : i ≠ j) :
    Disjoint (FreeGroup.startsWith (i, b)) (FreeGroup.startsWith (j, c)) :=
  FreeGroup.startsWith.disjoint_iff_ne.mpr (fun e => h (congrArg Prod.fst e))

theorem freeGroup_one_not_firstLetter (w : X × Bool) :
    (1 : FreeGroup X) ∉ FreeGroup.startsWith w := by
  simp [FreeGroup.startsWith]
end CuntzPureness

end

end OAI

import Mathlib

namespace OAI

universe uAlpha uIndex

/-! The combinatorial step from a permuted contact triple to branch selection. -/

namespace Problem356
namespace ContactSelection

variable {α : Type uAlpha} {ι : Type uIndex}

/-- If precisely the first source entry belongs to the central set, any
permutation whose first target entry is central has the same first entry. -/
theorem first_eq_of_perm
    {B : Set α} {x y z p q r : α}
    (hperm : List.Perm [x, y, z] [p, q, r])
    (hx : x ∈ B) (hq : q ∉ B) (hr : r ∉ B) : x = p := by
  have hm : x ∈ [p, q, r] := hperm.mem_iff.mp (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hp | hq' | hr'
  · exact hp
  · exact False.elim (hq (hq' ▸ hx))
  · exact False.elim (hr (hr' ▸ hx))

/-- After identifying the central entry, each remaining entry is one of the
other two entries of the contact triple. -/
theorem second_eq_or_third_of_perm
    {B : Set α} {x y z p q r : α}
    (hperm : List.Perm [x, y, z] [p, q, r])
    (hx : x ∈ B) (hq : q ∉ B) (hr : r ∉ B) : y = q ∨ y = r := by
  have hxp := first_eq_of_perm hperm hx hq hr
  subst p
  have hp : List.Perm [y, z] [q, r] := hperm.cons_inv
  have hm : y ∈ [q, r] := hp.mem_iff.mp (by simp)
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hm

/-- A contact triple parameterized by `s`, with central branch `X`,
selects either `Y x` or `W x` once `Y` inverts `X` on the parameter domain. -/
theorem second_selects_inverse_branch
    {B P : Set α} {X Z Y W : α → α} {x y z s : α}
    (hperm : List.Perm [x, y, z] [X s, s, Z s])
    (hx : x ∈ B) (hs : s ∈ P)
    (hOuter : ∀ a ∈ P, a ∉ B ∧ Z a ∉ B)
    (hInverse : ∀ a ∈ P, Y (X a) = a)
    (hW : ∀ a ∈ B, W a = Z (Y a)) : y = Y x ∨ y = W x := by
  have hout := hOuter s hs
  have hcentral := first_eq_of_perm hperm hx hout.1 hout.2
  have hinv : Y x = s := by rw [hcentral]; exact hInverse s hs
  rcases second_eq_or_third_of_perm hperm hx hout.1 hout.2 with hy | hy
  · exact Or.inl (hy.trans hinv.symm)
  · exact Or.inr (hy.trans (by rw [hW x hx, hinv]))

end ContactSelection
end Problem356

end OAI

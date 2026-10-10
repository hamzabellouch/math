import Mathlib.GroupTheory.FreeGroup.Reduce

namespace OAI
noncomputable section
namespace CuntzPureness
local instance {X : Type*} : DecidableEq X := Classical.decEq X

def wordTreeDistance {X : Type*} : List X → List X → ℕ
  | [], v => v.length
  | u, [] => u.length
  | a :: u, b :: v => if a = b then wordTreeDistance u v else u.length + v.length + 2

lemma wordTreeDistance_self {X : Type*} (u : List X) : wordTreeDistance u u = 0 := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa [wordTreeDistance] using ih

lemma wordTreeDistance_symm {X : Type*} (u v : List X) :
    wordTreeDistance u v = wordTreeDistance v u := by
  induction u generalizing v with
  | nil => cases v <;> simp [wordTreeDistance]
  | cons a u ih =>
    cases v with
    | nil => rfl
    | cons b v =>
      by_cases h : a = b
      · subst b; simp [wordTreeDistance, ih]
      · simp [wordTreeDistance, h, Ne.symm h]; omega

lemma reduced_invRev {X : Type*} {u : List (X × Bool)} (hu : FreeGroup.IsReduced u) :
    FreeGroup.IsReduced (FreeGroup.invRev u) := by
  apply FreeGroup.IsReduced.of_reduce_eq
  rw [FreeGroup.reduce_invRev, hu.reduce_eq]

lemma reduced_invRev_append_of_heads_ne {X : Type*} (a b : X × Bool)
    (u v : List (X × Bool)) (hu : FreeGroup.IsReduced (a :: u))
    (hv : FreeGroup.IsReduced (b :: v)) (hab : a ≠ b) :
    FreeGroup.IsReduced (FreeGroup.invRev (a :: u) ++ (b :: v)) := by
  apply List.IsChain.append (reduced_invRev hu) hv
  simp only [FreeGroup.invRev, List.map_cons,
    List.reverse_cons, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, List.head?_cons, Option.mem_def,
    Option.some.injEq]
  intro x hx y hy
  subst x; subst y
  dsimp
  intro h
  have hb : a.2 ≠ b.2 := fun hb => hab (Prod.ext h hb)
  cases a with | mk a s => cases b with | mk b t => cases s <;> cases t <;> simp_all

theorem reduced_word_distance {X : Type*} (u v : List (X × Bool))
    (hu : FreeGroup.IsReduced u) (hv : FreeGroup.IsReduced v) :
    (FreeGroup.reduce (FreeGroup.invRev u ++ v)).length = wordTreeDistance u v := by
  induction u generalizing v with
  | nil => simp [wordTreeDistance, hv.reduce_eq]
  | cons a u ih =>
    cases v with
    | nil => simp [wordTreeDistance, (reduced_invRev hu).reduce_eq, FreeGroup.invRev_length]
    | cons b v =>
      by_cases hab : a = b
      · subst b
        have hm : FreeGroup.mk (FreeGroup.invRev (a :: u) ++ (a :: v)) =
            FreeGroup.mk (FreeGroup.invRev u ++ v) := by
          have hu' : FreeGroup.mk (a :: u) = FreeGroup.mk [a] * FreeGroup.mk u :=
            by rw [FreeGroup.mul_mk]; rfl
          have hv' : FreeGroup.mk (a :: v) = FreeGroup.mk [a] * FreeGroup.mk v :=
            by rw [FreeGroup.mul_mk]; rfl
          calc
            _ = (FreeGroup.mk (a :: u))⁻¹ * FreeGroup.mk (a :: v) := by
              rw [FreeGroup.inv_mk, FreeGroup.mul_mk]
            _ = (FreeGroup.mk u)⁻¹ * FreeGroup.mk v := by
              rw [hu', hv', mul_inv_rev, mul_assoc, inv_mul_cancel_left]
            _ = _ := by rw [FreeGroup.inv_mk, FreeGroup.mul_mk]
        have he' := congrArg FreeGroup.toWord hm
        simp only [FreeGroup.toWord_mk] at he'
        rw [he', wordTreeDistance, ite_eq_left rfl]
        exact ih v hu.tail hv.tail
      · rw [(reduced_invRev_append_of_heads_ne a b u v hu hv hab).reduce_eq]
        simp [wordTreeDistance, hab, FreeGroup.invRev_length, List.length_append]
        omega

theorem freeGroup_mul_inv_length {X : Type*} (g h : FreeGroup X) :
    (g * h⁻¹).toWord.length = wordTreeDistance g⁻¹.toWord h⁻¹.toWord := by
  have he := reduced_word_distance g⁻¹.toWord h⁻¹.toWord
    FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
  rw [← FreeGroup.toWord_inv, inv_inv] at he
  simpa only [FreeGroup.toWord_mul] using he
end CuntzPureness

end

end OAI

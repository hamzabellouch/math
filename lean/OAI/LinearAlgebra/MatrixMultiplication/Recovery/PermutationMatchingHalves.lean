import OAI.LinearAlgebra.MatrixMultiplication.Recovery.PermutationMatchingMoments

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

noncomputable section

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

variable {P : Type*} [Fintype P] [DecidableEq P]

def twoHalfCount (A B : Finset P) (left right : Equiv.Perm P) : ℝ :=
  ∑ i : P, if left i ∈ A ∧ right i ∈ B then 1 else 0

theorem twoHalfCount_eq_matchingCount (A B : Finset P)
    (left right : Equiv.Perm P) :
    twoHalfCount A B left right =
      matchingCount A B (left.symm.trans right) := by
  classical
  unfold twoHalfCount matchingCount membership
  calc
    _ = ∑ i : P, if i ∈ A ∧ right (left.symm i) ∈ B then (1 : ℝ) else 0 := by
      simpa only [Equiv.symm_apply_apply] using
        Equiv.sum_comp left (fun i =>
          if i ∈ A ∧ right (left.symm i) ∈ B then (1 : ℝ) else 0)
    _ = ∑ i : P, if i ∈ A then
        (if right (left.symm i) ∈ B then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all
    _ = _ := by
      simp only [Equiv.trans_apply, Fintype.sum_ite_mem]
      apply Finset.sum_congr rfl
      intro i _
      apply if_congr <;> rfl

def relativePairEquiv :
    (Equiv.Perm P × Equiv.Perm P) ≃ (Equiv.Perm P × Equiv.Perm P) where
  toFun lr := (lr.1, lr.1.symm.trans lr.2)
  invFun lq := (lq.1, lq.1.trans lq.2)
  left_inv := by
    rintro ⟨left, right⟩
    dsimp only
    apply Prod.ext
    · rfl
    · ext i
      simp
  right_inv := by
    rintro ⟨left, relative⟩
    dsimp only
    apply Prod.ext
    · rfl
    · ext i
      simp

theorem average_relativePerm (f : Equiv.Perm P → ℝ) :
    average (fun lr : Equiv.Perm P × Equiv.Perm P =>
      f (lr.1.symm.trans lr.2)) = average f := by
  calc
    _ = average (fun lq : Equiv.Perm P × Equiv.Perm P => f lq.2) :=
      average_equiv relativePairEquiv (fun lq => f lq.2)
    _ = _ := average_prod_snd f

theorem average_twoHalfCount (A B : Finset P) (f : ℝ → ℝ) :
    average (fun lr : Equiv.Perm P × Equiv.Perm P =>
      f (twoHalfCount A B lr.1 lr.2)) =
      average (fun p : Equiv.Perm P => f (matchingCount A B p)) := by
  simp_rw [twoHalfCount_eq_matchingCount]
  exact average_relativePerm (fun p => f (matchingCount A B p))

theorem twoHalfCount_statisticPositions {X Y S T : Type*}
    (leftWord : P → X) (rightWord : P → Y) (sl : X → S) (sr : Y → T)
    (s : S) (t : T) (left right : Equiv.Perm P) :
    twoHalfCount (statisticPositions leftWord sl s)
        (statisticPositions rightWord sr t) left right =
      ∑ i : P, if sl (leftWord (left i)) = s ∧ sr (rightWord (right i)) = t
        then (1 : ℝ) else 0 := by
  classical
  simp [twoHalfCount, statisticPositions]

section Families

variable {C : Type*} (Q : C → Type*)

def relativeFamily
    (left right : ∀ c, Equiv.Perm (Q c)) : ∀ c, Equiv.Perm (Q c) :=
  fun c => (left c).symm.trans (right c)

def relativeFamilyPairEquiv :
    ((∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c))) ≃
      ((∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c))) where
  toFun lr := (lr.1, relativeFamily Q lr.1 lr.2)
  invFun lq := (lq.1, fun c => (lq.1 c).trans (lq.2 c))
  left_inv := by
    rintro ⟨left, right⟩
    dsimp only
    apply Prod.ext
    · rfl
    · funext c
      ext i
      simp [relativeFamily]
  right_inv := by
    rintro ⟨left, relative⟩
    dsimp only
    apply Prod.ext
    · rfl
    · funext c
      ext i
      simp [relativeFamily]

variable [Fintype C] [DecidableEq C]
  [∀ c, Fintype (Q c)] [∀ c, DecidableEq (Q c)]

theorem average_relativeFamily (f : (∀ c, Equiv.Perm (Q c)) → ℝ) :
    average (fun lr :
        (∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c)) =>
      f (relativeFamily Q lr.1 lr.2)) = average f := by
  calc
    _ = average (fun lq :
        (∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c)) => f lq.2) :=
      average_equiv (relativeFamilyPairEquiv Q) (fun lq => f lq.2)
    _ = _ := average_prod_snd f

omit [DecidableEq C] in
theorem sum_twoHalfCount_eq_matchingCount
    (A B : ∀ c, Finset (Q c)) (left right : ∀ c, Equiv.Perm (Q c)) :
    (∑ c, twoHalfCount (A c) (B c) (left c) (right c)) =
      ∑ c, matchingCount (A c) (B c) (relativeFamily Q left right c) := by
  simp only [twoHalfCount_eq_matchingCount, relativeFamily]

end Families

end MatrixMultiplication.PermutationMatching

end

end OAI

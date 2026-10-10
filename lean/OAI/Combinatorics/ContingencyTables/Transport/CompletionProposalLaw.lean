import OAI.Combinatorics.ContingencyTables.Transport.CompletionStepApproximation
import Mathlib.Algebra.Order.Field.Basic

namespace OAI

/-! # The literal proposal, completion draw and acceptance test -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq X]

/-- Each feasible neighbor is assigned its prescribed dyadic mass; the
remaining proposal words hold at the present state. -/
def proposalLaw (w : X → ℚ) (hw : ∀ y,0 ≤ w y) (htotal : ∑ y,w y ≤ 1) :
    RationalLaw (Option X) where
  mass := fun y => match y with
    | none => 1-∑ z,w z
    | some z => w z
  nonnegative := fun y => by cases y with
    | none => exact sub_nonneg.mpr htotal
    | some y => exact hw y
  total := by rw [Fintype.sum_option]; dsimp only; ring

omit [Fintype X] in
/-- Only a proposal of y can reach y from a distinct current state x. -/
lemma completionDecision_eq (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (x y : X) (hne : x≠y) (q : Option X) (a : Table (R x) (P x)) :
    completionDecision R P x q a=y ↔
      q=some y ∧ ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j := by
  cases q with
  | none => simp [completionDecision,hne]
  | some z =>
    by_cases hz : z=y
    · subst z
      simp only [completionDecision,true_and]
      split_ifs <;> simp_all
    · simp only [completionDecision,Option.some.injEq,hz,false_and]
      split_ifs <;> simp_all

lemma completionStepLaw_mass_ne (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (w : X → ℚ) (hw : ∀ y,0 ≤ w y) (htotal : ∑ y,w y ≤ 1)
    (μ : (x : X) → RationalLaw (Table (R x) (P x))) (x y : X) (hne : x≠y) :
    (completionStepLaw R P (fun _ => proposalLaw w hw htotal) μ x).mass y=
      w y*∑ a : Table (R x) (P x),
        if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
        then (μ x).mass a else 0 := by
  change (∑ q : Option X,(proposalLaw w hw htotal).mass q *
    ∑ a : Table (R x) (P x),if completionDecision R P x q a=y then (μ x).mass a else 0)=_
  simp_rw [completionDecision_eq R P x y hne]
  rw [Fintype.sum_option]
  simp only [reduceCtorEq,false_and,ite_false,Finset.sum_const_zero,mul_zero,zero_add,Option.some.injEq]
  have hh (z : X) : (∑ a : Table (R x) (P x),
      if z=y ∧ ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
      then (μ x).mass a else 0)=
      if z=y then ∑ a : Table (R x) (P x),
        if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
        then (μ x).mass a else 0 else 0 := by
    by_cases hz : z=y <;> simp [hz]
  simp_rw [hh]
  simp [proposalLaw,mul_ite]

omit [Fintype X] [DecidableEq X] in
/-- The normalized completion indicator is exactly the acceptance count
used in the reversible small kernel. -/
lemma uniformAcceptedMass (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (x y : X) [Nonempty (Table (R x) (P x))] :
    (∑ a : Table (R x) (P x),
      if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
      then (uniformLaw (α := Table (R x) (P x))).mass a else 0)=
      (acceptedCount R P x y:ℚ)/(blockCount R P x:ℚ) := by
  simp only [uniformLaw,uniformMass]
  calc
    _ = (∑ a : Table (R x) (P x),
        if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
        then (1:ℚ) else 0)/(Fintype.card (Table (R x) (P x)):ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_boole,←Fintype.card_subtype]
      rfl

end
end ContingencyTables.CompletionTranslation

end OAI

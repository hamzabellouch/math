import OAI.Combinatorics.ContingencyTables.Transport.BalancedEnumeration
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-!
# Physical indexing of all balanced large-cell pairs

The recursively added pairs are identified with the actual finite cells,
and their assignments with the dependent product of the physical finite
intervals. No extra coordinate or assignment multiplicity is introduced.
-/

namespace ContingencyTables.LargePairEnumeration

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal

universe u

/-- Widths in the explicit order supplied by a finite cell enumeration. -/
def widths : {n : ℕ} → (Fin n → ℕ) → List ℕ
  | 0,_ => []
  | _+1,M => M 0::widths (fun i => M i.succ)

lemma widths_lower {n : ℕ} (M : Fin n → ℕ) (h : ∀ i, 2≤M i) :
    ∀ w ∈ widths M, 2≤w := by
  induction n with
  | zero => intro w hw; exact False.elim (List.not_mem_nil hw)
  | succ n ih =>
    intro w hw
    simp only [widths,List.mem_cons] at hw
    rcases hw with rfl|hw
    · exact h 0
    · exact ih (fun i => M i.succ) (fun i => h i.succ) w hw

private def pairSuccEquiv (n : ℕ) : ((Fin n×Bool)⊕Bool) ≃ Fin (n+1)×Bool where
  toFun
    | .inl (i,b) => (i.succ,b)
    | .inr b => (0,b)
  invFun p := Fin.cases (.inr p.2) (fun i => .inl (i,p.2)) p.1
  left_inv p := by cases p with
    | inl p => rcases p with ⟨i,b⟩; rfl
    | inr b => rfl
  right_inv p := by
    rcases p with ⟨i,b⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The nested coordinate sums contain exactly the retained coordinates
and one doubled coordinate for each physical large cell. -/
def coordinateEquiv (S : Type u) : {n : ℕ} → (M : Fin n → ℕ) →
    Coordinates S (widths M) ≃ S⊕(Fin n×Bool)
  | 0,_ => (Equiv.sumEmpty S (Fin 0×Bool)).symm
  | n+1,M =>
    (Equiv.sumCongr (coordinateEquiv S (fun i => M i.succ)) (Equiv.refl Bool)).trans
      ((Equiv.sumAssoc S (Fin n×Bool) Bool).trans
        (Equiv.sumCongr (Equiv.refl S) (pairSuccEquiv n)))

/-- Balanced choices are the dependent product of the actual intervals. -/
def assignmentEquiv : {n : ℕ} → (M : Fin n → ℕ) →
    Assignments (widths M) ≃ ((i : Fin n) → Fin (M i+1))
  | 0,_ =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := by intro a; cases a; rfl
      right_inv := by intro a; funext i; exact Fin.elim0 i }
  | n+1,M =>
    { toFun := fun a => Fin.cases a.2 (assignmentEquiv (fun i => M i.succ) a.1)
      invFun := fun a => ((assignmentEquiv (fun i => M i.succ)).symm (fun i => a i.succ),a 0)
      left_inv := by intro a; simp only [Fin.cases_zero,Fin.cases_succ,Equiv.symm_apply_apply]; exact Prod.eta a
      right_inv := by
        intro a
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact congrFun ((assignmentEquiv (fun i => M i.succ)).apply_symm_apply
            (fun i => a i.succ)) j }

def joinedProfile {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (a : (i : Fin n) → Fin (M i+1)) : S⊕(Fin n×Bool) → ℕ
  | .inl s => z s
  | .inr (i,b) => if b then M i-(a i).val else (a i).val

lemma embedding_coordinate {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (a : (i : Fin n) → Fin (M i+1)) (c : Coordinates S (widths M)) :
    embedding (widths M) z ((assignmentEquiv M).symm a) c=
      joinedProfile M z a (coordinateEquiv S M c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases c with
    | inl c =>
      change embedding (widths (fun i => M i.succ)) z
        ((assignmentEquiv (fun i => M i.succ)).symm (fun i => a i.succ)) c=_
      rw [ih]
      change joinedProfile (fun i => M i.succ) z (fun i => a i.succ)
        (coordinateEquiv S (fun i => M i.succ) c)=
        joinedProfile M z a (((Equiv.sumAssoc S (Fin n×Bool) Bool).trans
          (Equiv.sumCongr (Equiv.refl S) (pairSuccEquiv n)))
          (.inl (coordinateEquiv S (fun i => M i.succ) c)))
      generalize hc : coordinateEquiv S (fun i => M i.succ) c=q
      cases q with
      | inl s => rfl
      | inr p => rcases p with ⟨i,b⟩; rfl
    | inr b => cases b <;> rfl

/-- The recursively proved marginal is the direct finite sum over the
actual physical intervals. -/
theorem eliminate_eq_physical_sum {S : Type*} {n : ℕ} (M : Fin n → ℕ)
    (F : (S⊕(Fin n×Bool) → ℕ) → ℝ) (z : S → ℕ) :
    eliminate (widths M) (fun q => F (q ∘ (coordinateEquiv S M).symm)) z=
      ∑ a : ((i : Fin n) → Fin (M i+1)), F (joinedProfile M z a) := by
  rw [eliminate_eq_sum]
  apply Fintype.sum_equiv (assignmentEquiv M)
  intro a
  congr 1
  funext c
  have h := embedding_coordinate M z ((assignmentEquiv M) a) ((coordinateEquiv S M).symm c)
  simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,Function.comp_apply] using h

variable {C : Type*}

@[reducible] def SmallView (small : C → Bool) := {c : C // small c=true}×Bool

@[reducible] def LargeCell (small : C → Bool) := {c : C // small c=false}

/-- This is the actual partition of doubled cells into small views and
large pairs. -/
noncomputable def partitionEquiv (small : C → Bool) :
    SmallView small⊕(LargeCell small×Bool) ≃ C×Bool where
  toFun
    | .inl p => (p.1.val,p.2)
    | .inr p => (p.1.val,p.2)
  invFun p := if h : small p.1=true then .inl (⟨p.1,h⟩,p.2)
    else .inr (⟨p.1,Bool.eq_false_iff.mpr h⟩,p.2)
  left_inv p := by
    cases p with
    | inl p => simp only [p.1.property,dite_eq_left]
    | inr p => simp only [p.1.property,Bool.false_eq_true,dite_false]
  right_inv p := by
    dsimp only
    split_ifs <;> rfl

noncomputable def physicalJoinEquiv (small : C → Bool) {n : ℕ}
    (e : Fin n ≃ LargeCell small) : SmallView small⊕(Fin n×Bool) ≃ C×Bool :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr e (Equiv.refl Bool))).trans
    (partitionEquiv small)

/-- Every finite enumeration of the large cells gives the same physical
coordinate space, with each original doubled cell appearing once. -/
noncomputable def physicalCoordinateEquiv (small : C → Bool) {n : ℕ}
    (e : Fin n ≃ LargeCell small) (M : Fin n → ℕ) :
    Coordinates (SmallView small) (widths M) ≃ C×Bool :=
  (coordinateEquiv (SmallView small) M).trans (physicalJoinEquiv small e)

theorem eliminate_eq_actual_cells (small : C → Bool) {n : ℕ}
    (e : Fin n ≃ LargeCell small) (M : Fin n → ℕ)
    (F : (C×Bool → ℕ) → ℝ) (z : SmallView small → ℕ) :
    eliminate (widths M) (fun q => F (q ∘ (physicalCoordinateEquiv small e M).symm)) z=
      ∑ a : ((i : Fin n) → Fin (M i+1)),
        F (joinedProfile M z a ∘ (physicalJoinEquiv small e).symm) := by
  exact eliminate_eq_physical_sum M (fun q => F (q ∘ (physicalJoinEquiv small e).symm)) z

end ContingencyTables.LargePairEnumeration

end OAI

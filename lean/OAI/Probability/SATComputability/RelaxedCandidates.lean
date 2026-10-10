import OAI.Probability.SATComputability.SignLaw

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

abbrev DeletionCandidate (n : ℕ) := Fin n → Option Bool
abbrev SignedLiteral (n : ℕ) := Fin n × Bool

def literalFalse {n : ℕ} (x : DeletionCandidate n) (l : SignedLiteral n) : Prop :=
  x l.1 = some (!l.2)

def frozenLiteral {n : ℕ} (U : Finset (DeletionCandidate n)) (l : SignedLiteral n) : Prop :=
  ∀ x ∈ U, literalFalse x l

noncomputable def frozenFraction {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (SignedLiteral n)).expect
    (fun l => if frozenLiteral U l then 1 else 0)

theorem uniform_prod_expect {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (A × B)).expect f =
      (FiniteLaw.uniform : FiniteLaw A).expect (fun a =>
        (FiniteLaw.uniform : FiniteLaw B).expect (fun b => f (a, b))) := by
  simp only [FiniteLaw.expect, FiniteLaw.uniform, Fintype.sum_prod_type,
    Fintype.card_prod, Nat.cast_mul, mul_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frozenFraction_nonneg {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) : 0 ≤ frozenFraction U := by
  apply FiniteLaw.expect_nonneg
  intro l
  split <;> norm_num

theorem frozenFraction_le_half {n : ℕ} [NeZero n]
    {U : Finset (DeletionCandidate n)} (hU : U.Nonempty) :
    frozenFraction U ≤ (1 : ℝ) / 2 := by
  classical
  obtain ⟨x, hx⟩ := hU
  unfold frozenFraction
  rw [uniform_prod_expect]
  calc
    _ ≤ (FiniteLaw.uniform : FiniteLaw (Fin n)).expect (fun _ => (1 : ℝ) / 2) := by
      apply FiniteLaw.expect_mono
      intro v
      calc
        _ ≤ (FiniteLaw.uniform : FiniteLaw Bool).expect
            (fun s => if literalFalse x (v, s) then 1 else 0) := by
          apply FiniteLaw.expect_mono
          intro s
          by_cases hf : frozenLiteral U (v, s)
          · rw [ite_eq_left hf, ite_eq_left (hf x hx)]
          · rw [ite_eq_right hf]
            split <;> norm_num
        _ ≤ 1 / 2 := by
          cases h : x v with
          | none => norm_num [literalFalse, h, FiniteLaw.expect, FiniteLaw.uniform]
          | some b => cases b <;>
              norm_num [literalFalse, h, FiniteLaw.expect, FiniteLaw.uniform, Fintype.sum_bool]
    _ = _ := FiniteLaw.expect_const _ _

noncomputable def oneTestKill {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect
    (fun c => if ∀ x ∈ U, ∀ l, literalFalse x (c l) then 1 else 0)

theorem oneTestKill_eq {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) :
    oneTestKill U k = frozenFraction U ^ k := by
  classical
  have hi (c : Fin k → SignedLiteral n) :
      (if ∀ x ∈ U, ∀ l, literalFalse x (c l) then (1 : ℝ) else 0) =
        ∏ l, if frozenLiteral U (c l) then 1 else 0 := by
    rw [Fintype.prod_boole]
    congr 1
    simp only [frozenLiteral]
    apply propext
    constructor
    · intro h l x hx
      exact h x hx l
    · intro h x hx l
      exact h l x hx
  unfold oneTestKill
  simp_rw [hi]
  rw [uniformFiniteLaw_pi]
  calc
    _ = ∏ _ : Fin k, (FiniteLaw.uniform : FiniteLaw (SignedLiteral n)).expect
        (fun l => if frozenLiteral U l then 1 else 0) :=
      FiniteLaw.expect_pi_product
        (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (SignedLiteral n)))
        (fun _ l => if frozenLiteral U l then 1 else 0)
    _ = _ := by simp only [frozenFraction, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end FixedClauseThreshold.Computability

end OAI

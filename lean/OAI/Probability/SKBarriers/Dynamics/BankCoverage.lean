import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.FiniteLaw
import OAI.Probability.SKBarriers.SpinGlass.FiniteSampling

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic
namespace FiniteLaw
variable {X I A : Type*} [Fintype X] [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

theorem iid_random_cell_miss (P : FiniteLaw X) (K : ℕ) (u : A → I) (v : Fin K → I)
    (he : Function.Injective (Sum.elim u v))
    (C : (A → X) → X → Prop) (R : X → X → Prop) {a δ : ℝ} (ha : 0≤a)
    (hcov : ∀ w, P.prob (fun x => C w x ∧ P.prob (fun y => C w y ∧ R x y)<a) ≤ δ) :
    (P.iid I).expect (fun z => P.prob (fun x => C (z ∘ u) x ∧
      ∀ k, ¬(C (z ∘ u) (z (v k)) ∧ R x (z (v k))))) ≤ δ+Real.exp (-a*K) := by
  classical
  let F (w : A ⊕ Fin K → X) : ℝ := P.prob (fun x => C (w ∘ Sum.inl) x ∧
    ∀ k, ¬(C (w ∘ Sum.inl) (w (Sum.inr k)) ∧ R x (w (Sum.inr k))))
  have H := P.iid_expect_injective (Sum.elim u v) he F
  change (P.iid I).expect (fun z => F (z ∘ Sum.elim u v)) ≤ _
  rw [H,P.iid_expect_sum F]
  calc
    _ ≤ (P.iid A).expect (fun _ => δ+Real.exp (-a*K)) := by
      apply expect_mono
      intro w
      exact P.iid_cell_miss_bound (C w) R K ha (hcov w)
    _ = _ := expect_const _ _
end FiniteLaw

abbrev BankIndex {p : ℕ} (K : Fin p → ℕ) := (j : Fin p) × Fin (K j)
abbrev BankPrior {p : ℕ} (pred : Fin p → Finset (Fin p)) (j : Fin p) := {i : Fin p // i∈pred j}
abbrev BankTuple {p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p)) (j : Fin p) :=
  (i : BankPrior pred j) → Fin (K i.val)

def bankJointIndex {p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p)) (j : Fin p)
    (T : BankTuple K pred j) : BankPrior pred j ⊕ Fin (K j) → BankIndex K :=
  Sum.elim (fun i => ⟨i.val,T i⟩) (fun a => ⟨j,a⟩)

theorem bankJointIndex_injective {p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p))
    (j : Fin p) (hj : j∉pred j) (T : BankTuple K pred j) :
    Function.Injective (bankJointIndex K pred j T) := by
  intro a b H
  cases a with
  | inl i =>
    cases b with
    | inl k =>
      have he : i.val=k.val := congrArg Sigma.fst H
      exact congrArg Sum.inl (Subtype.ext he)
    | inr k =>
      have he : i.val=j := congrArg Sigma.fst H
      apply False.elim; apply hj; simpa only [he] using i.property
  | inr i =>
    cases b with
    | inl k =>
      have he : j=k.val := congrArg Sigma.fst H
      apply False.elim; apply hj; simpa only [← he] using k.property
    | inr k =>
      have he : HEq i k := (Sigma.mk.inj_iff.mp H).2
      exact congrArg Sum.inr (eq_of_heq he)

def bankCell {n p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p)) (t : ℝ)
    (z : BankIndex K → Config n) (j : Fin p) (T : BankTuple K pred j) (x : Config n) : Prop :=
  ∀ i : BankPrior pred j, |overlap (z ⟨i.val,T i⟩) x|≤3*t

def bankCoverageBad {n p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p)) (t q : ℝ)
    (z : BankIndex K → Config n) (x : Config n) : Prop :=
  ∃ j : Fin p, ∃ T : BankTuple K pred j, bankCell K pred t z j T x ∧
    ∀ a : Fin (K j), ¬(bankCell K pred t z j T (z ⟨j,a⟩) ∧ q≤|overlap x (z ⟨j,a⟩)|)

theorem expected_bank_coverage_bad {n p : ℕ} (P : FiniteLaw (Config n)) (K : Fin p → ℕ)
    (pred : Fin p → Finset (Fin p)) (hpred : ∀ j, j∉pred j) (t q : ℝ) (a δ : Fin p → ℝ)
    (ha : ∀ j,0≤a j)
    (hcov : ∀ j, ∀ w : BankPrior pred j → Config n,
      P.prob (fun x => (∀i,|overlap (w i) x|≤3*t) ∧
        P.prob (fun y => (∀i,|overlap (w i) y|≤3*t) ∧ q≤|overlap x y|)<a j)≤δ j) :
    (P.iid (BankIndex K)).expect (fun z => P.prob (bankCoverageBad K pred t q z)) ≤
      ∑ j, Fintype.card (BankTuple K pred j)*(δ j+Real.exp (-(a j)*(K j))) := by
  classical
  calc
    _ ≤ (P.iid (BankIndex K)).expect (fun z => ∑ j : Fin p, ∑ T : BankTuple K pred j,
        P.prob (fun x => bankCell K pred t z j T x ∧
          ∀ a : Fin (K j), ¬(bankCell K pred t z j T (z ⟨j,a⟩) ∧ q≤|overlap x (z ⟨j,a⟩)|))) := by
      apply FiniteLaw.expect_mono
      intro z
      refine (P.prob_exists _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      exact P.prob_exists _
    _ = ∑ j : Fin p, ∑ T : BankTuple K pred j, (P.iid (BankIndex K)).expect (fun z =>
        P.prob (fun x => bankCell K pred t z j T x ∧
          ∀ a : Fin (K j), ¬(bankCell K pred t z j T (z ⟨j,a⟩) ∧ q≤|overlap x (z ⟨j,a⟩)|))) := by
      rw [FiniteLaw.expect_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact FiniteLaw.expect_sum _ _
    _ ≤ ∑ j : Fin p, ∑ _T : BankTuple K pred j, (δ j+Real.exp (-(a j)*(K j))) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro T _
      exact P.iid_random_cell_miss (I := BankIndex K) (A := BankPrior pred j) (K j) (fun i : BankPrior pred j => (⟨i.val,T i⟩ : BankIndex K)) (fun b => (⟨j,b⟩ : BankIndex K))
        (bankJointIndex_injective K pred j (hpred j) T) (fun w x => ∀i,|overlap (w i) x|≤3*t)
        (fun x y => q≤|overlap x y|) (ha j) (hcov j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

end SK.Analytic

end
end

end OAI

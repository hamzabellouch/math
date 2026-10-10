import OAI.Combinatorics.Ryser.Probability.Product
import OAI.Combinatorics.Ryser.Probability.Variance
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Selection

variable {Ω A : Type*} [Fintype Ω]

theorem prob_exists_mem_le (mu : FiniteLaw Ω) (S : Finset A)
    (P : A → Ω → Prop) :
    mu.prob (fun x => ∃ a ∈ S, P a x) ≤ ∑ a ∈ S, mu.prob (P a) := by
  classical
  calc
    _ ≤ mu.expectation (fun x => ∑ a ∈ S, if P a x then (1 : ℝ) else 0) := by
      apply mu.prob_le_expectation
      · intro x
        exact Finset.sum_nonneg (fun a _ => by by_cases h : P a x <;> simp [h])
      · rintro x ⟨a, ha, hax⟩
        calc
          1 = (if P a x then (1 : ℝ) else 0) := by rw [ite_eq_left hax]
          _ ≤ ∑ b ∈ S, if P b x then (1 : ℝ) else 0 :=
            Finset.single_le_sum (f := fun b => if P b x then (1 : ℝ) else 0) (fun b _ => by by_cases h : P b x <;> simp [h]) ha
    _ = ∑ a ∈ S, mu.prob (P a) := by
      rw [FiniteLaw.expectation_finset_sum]
      simp_rw [← FiniteLaw.prob_eq_expectation]

variable {E : Type*} [Fintype E] [DecidableEq E]
  {X : E → Type*} [∀ e, Fintype (X e)]

theorem prob_pi_forall_mem (mu : ∀ e, FiniteLaw (X e))
    (S : Finset E) (P : ∀ e, X e → Prop) :
    (FiniteLaw.pi mu).prob (fun x => ∀ e ∈ S, P e (x e)) =
      ∏ e ∈ S, (mu e).prob (P e) := by
  classical
  rw [FiniteLaw.prob_pi mu (fun e x => e ∈ S → P e x)]
  have hterm (e : E) : (mu e).prob (fun x => e ∈ S → P e x) =
      if e ∈ S then (mu e).prob (P e) else 1 := by
    by_cases he : e ∈ S <;> simp [he]
  simp_rw [hterm]
  rw [← Finset.prod_filter]
  simp

theorem prob_many_coordinate_events_le (mu : ∀ e, FiniteLaw (X e))
    (S : Finset E) (P : ∀ e, X e → Prop) (r : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hP : ∀ e ∈ S, (mu e).prob (P e) ≤ p) :
    (FiniteLaw.pi mu).prob (fun x => r ≤ (S.filter (fun e => P e (x e))).card) ≤
      (2 : ℝ) ^ S.card * p ^ r := by
  classical
  have hsubset (x : ∀ e, X e)
      (hx : r ≤ (S.filter (fun e => P e (x e))).card) :
      ∃ T ∈ S.powersetCard r, ∀ e ∈ T, P e (x e) := by
    obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hx
    refine ⟨T, Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, ?_⟩
    · exact fun e he => (Finset.mem_filter.mp (hT he)).1
    · exact fun e he => (Finset.mem_filter.mp (hT he)).2
  have hproduct (T : Finset E) (hT : T ∈ S.powersetCard r) :
      (FiniteLaw.pi mu).prob (fun x => ∀ e ∈ T, P e (x e)) ≤ p ^ r := by
    rcases Finset.mem_powersetCard.mp hT with ⟨hTS, hcard⟩
    rw [prob_pi_forall_mem]
    calc
      (∏ e ∈ T, (mu e).prob (P e)) ≤ ∏ _e ∈ T, p := by
        apply Finset.prod_le_prod₀
        · exact fun e _ => (mu e).prob_nonneg (P e)
        · exact fun e he => hP e (hTS he)
      _ = p ^ r := by simp [hcard]
  have hcount : (S.powersetCard r).card ≤ 2 ^ S.card := by
    rw [← Finset.card_powerset]
    apply Finset.card_le_card
    intro T hT
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hT).1
  calc
    _ ≤ (FiniteLaw.pi mu).prob
        (fun x => ∃ T ∈ S.powersetCard r, ∀ e ∈ T, P e (x e)) :=
      (FiniteLaw.pi mu).prob_mono hsubset
    _ ≤ ∑ T ∈ S.powersetCard r,
        (FiniteLaw.pi mu).prob (fun x => ∀ e ∈ T, P e (x e)) :=
      prob_exists_mem_le _ _ _
    _ ≤ ∑ _T ∈ S.powersetCard r, p ^ r := Finset.sum_le_sum hproduct
    _ = ((S.powersetCard r).card : ℝ) * p ^ r := by simp
    _ ≤ (2 : ℝ) ^ S.card * p ^ r :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (pow_nonneg hp _)

end RyserCoveringCounterexample.Selection

end

end OAI

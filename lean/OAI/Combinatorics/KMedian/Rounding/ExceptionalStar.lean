import Mathlib
import OAI.Combinatorics.KMedian.Rounding.TargetSubset

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset MarginalRounding
variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

noncomputable def upperBit (q : ℝ) : ℝ := if 0 < q then 1 else 0

 theorem upperBit_bounds {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q ≤ upperBit q ∧ upperBit q ≤ 1 := by
  unfold upperBit
  split_ifs with h
  · exact ⟨hq1, le_rfl⟩
  · exact ⟨le_of_not_gt h, zero_le_one⟩

omit [DecidableEq E] [Fintype T] [DecidableEq T] in

theorem exceptional_raw_error (D : E → Finset T) (q a : E → ℝ) (S : E → Finset T)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (_ha0 : ∀ e, 0 ≤ a e) (ha1 : ∀ e, a e ≤ 1)
    (hsmall : (fractional q).card ≤ 1)
    (hS : ∀ e, |((S e).card:ℝ)-((D e).card:ℝ)*q e| ≤ 1 ∧
      (q e=0 → S e=∅) ∧ (q e=1 → S e=D e)) :
    (∑ e, (a e*(upperBit (q e)-q e)+((D e).card:ℝ)*q e-((S e).card:ℝ))) ≤ 2 := by
  let v : E → ℝ := fun e => a e*(upperBit (q e)-q e)+((D e).card:ℝ)*q e-((S e).card:ℝ)
  have hv0 : ∀ e, e ∉ fractional q → v e=0 := by
    intro e he
    rcases nonfractional_integral hq0 hq1 he with h | h
    · simp only [v, h, upperBit, lt_self_iff_false, ite_false, sub_self, mul_zero, zero_add,
        (hS e).2.1 h, card_empty, Nat.cast_zero]
    · simp only [v, h, upperBit, zero_lt_one, ite_true, sub_self, mul_zero, mul_one,
        zero_add, (hS e).2.2 h, sub_self]
  have hv : ∀ e, v e ≤ 2 := by
    intro e
    have hu := upperBit_bounds (hq0 e) (hq1 e)
    have hprod := mul_le_mul (ha1 e)
      (show upperBit (q e)-q e ≤ 1 by linarith only [hu.2, hq0 e])
      (sub_nonneg.mpr hu.1) (by norm_num : (0:ℝ) ≤ 1)
    have herr := (abs_le.mp (hS e).1).1
    dsimp only [v]
    nlinarith only [hprod, herr]
  have heq : (∑ e, v e)=∑ e ∈ fractional q, v e := by
    apply (sum_subset (subset_univ _) (fun e _ he => hv0 e he)).symm
  change (∑ e, v e) ≤ 2
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ fractional q, (2:ℝ) := sum_le_sum (fun e _ => hv e)
    _ = ((fractional q).card:ℝ)*2 := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ 2 := by exact_mod_cast (by omega : (fractional q).card*2 ≤ 2)

theorem exceptional_activation_law (D : E → Finset T) (q a : E → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (ha0 : ∀ e, 0 ≤ a e) (ha1 : ∀ e, a e ≤ 1)
    (hsmall : (fractional q).card ≤ 1) :
    ∃ μ : FiniteLaw (E → Finset T),
      (∀ S, 0 < μ.weight S → (∀ e, S e ⊆ D e) ∧
        (∀ e t, WeightedRounding.indicator (S e) t ≤ upperBit (q e)) ∧
        (∑ e, (a e*(upperBit (q e)-q e)+((D e).card:ℝ)*q e-((S e).card:ℝ))) ≤ 2) ∧
      (∀ e t, μ.prob (fun S => t ∈ S e)=if t ∈ D e then q e else 0) ∧
      (∀ e f, e ≠ f → ∀ t u,
        μ.expect (fun S => WeightedRounding.indicator (S e) t*WeightedRounding.indicator (S f) u)=
          (if t ∈ D e then q e else 0)*(if u ∈ D f then q f else 0)) := by
  choose ν hs hm using (fun e => target_subset_law (D e) (hq0 e) (hq1 e))
  refine ⟨FiniteLaw.product ν, ?_, ?_, ?_⟩
  · intro S hS
    have hsup := FiniteLaw.support_product ν S hS
    refine ⟨fun e => (hs e (S e) (hsup e)).1, ?_, ?_⟩
    · intro e t
      by_cases hq : 0 < q e
      · simp only [upperBit, ite_eq_left hq, WeightedRounding.indicator]
        split_ifs <;> norm_num
      · have hzero : q e=0 := le_antisymm (le_of_not_gt hq) (hq0 e)
        rw [(hs e (S e) (hsup e)).2.2.1 hzero]
        simp only [WeightedRounding.indicator, notMem_empty, ite_false, upperBit, ite_eq_right hq]
        exact le_rfl
    · exact exceptional_raw_error D q a S hq0 hq1 ha0 ha1 hsmall
        (fun e => (hs e (S e) (hsup e)).2)
  · intro e t
    calc
      _ = (ν e).prob (fun S => t ∈ S) := FiniteLaw.product_marginal ν e (fun S => if t ∈ S then 1 else 0)
      _ = _ := hm e t
  · intro e f hef t u
    calc
      _ = (ν e).prob (fun S => t ∈ S)*(ν f).prob (fun S => u ∈ S) :=
        FiniteLaw.product_pair ν hef (fun S => WeightedRounding.indicator S t)
          (fun S => WeightedRounding.indicator S u)
      _ = _ := by rw [hm, hm]

end MetricKMedian.Preparation
end
end

end OAI

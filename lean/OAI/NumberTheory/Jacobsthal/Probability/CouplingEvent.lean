import OAI.NumberTheory.Jacobsthal.Sieve.IntegerLaw

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

noncomputable def lowerInteger (E : Finset ℕ) (s : Outcomes E) : ℕ :=
  integerProduct E (fun p => lowerExponent (s p))
noncomputable def upperInteger (E : Finset ℕ) (s : Outcomes E) : ℕ :=
  integerProduct E (fun p => upperExponent (s p))

variable (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
include hE

lemma log_integerProduct (k : E → ℕ) :
    Real.log (integerProduct E k : ℝ) = ∑ p : E, (k p : ℝ) * Real.log (p : ℝ) := by
  rw [integerProduct, Nat.cast_prod]
  rw [Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
  · intro p _; exact_mod_cast pow_ne_zero (k p) (hE p p.property).ne_zero

theorem upper_log_eq_lower_add_excess (s : Outcomes E) :
    Real.log (upperInteger E s : ℝ) = Real.log (lowerInteger E s : ℝ) + excessLog E s := by
  rw [upperInteger, lowerInteger, log_integerProduct E hE, log_integerProduct E hE]
  unfold excessLog
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.cast_sub (lowerExponent_le_upperExponent (s p))]
  ring

theorem source_cutoff_implication {P : ℝ} (hP : 1 < P) (s : Outcomes E)
    (hl : (lowerInteger E s : ℝ) ≤ P ^ (94 / 100 : ℝ))
    (hz : excessLog E s ≤ (1 / 100 : ℝ) * Real.log P) :
    (upperInteger E s : ℝ) ≤ P ^ (95 / 100 : ℝ) := by
  have hu : 0 < (upperInteger E s : ℝ) := by
    exact_mod_cast integerProduct_pos E hE (fun p => upperExponent (s p))
  have hl0 : 0 < (lowerInteger E s : ℝ) := by
    exact_mod_cast integerProduct_pos E hE (fun p => lowerExponent (s p))
  apply (Real.log_le_log_iff hu (Real.rpow_pos_of_pos (by linarith) _)).mp
  rw [upper_log_eq_lower_add_excess E hE]
  have hh := Real.log_le_log hl0 hl
  rw [Real.log_rpow (by linarith : 0 < P)] at hh ⊢
  linarith

theorem small_product_coupling_lower {P : ℝ} (hP : 1 < P) :
    eventMass E (fun s => (lowerInteger E s : ℝ) ≤ P ^ (94 / 100 : ℝ)) -
        100 * uniformMomentBound / Real.log P ≤
      eventMass E (fun s => (upperInteger E s : ℝ) ≤ P ^ (95 / 100 : ℝ)) := by
  have htwo : ∀ p ∈ E, 2 ≤ p := fun p hp => (hE p hp).two_le
  let L : Outcomes E → Prop := fun s => (lowerInteger E s : ℝ) ≤ P ^ (94 / 100 : ℝ)
  let U : Outcomes E → Prop := fun s => (upperInteger E s : ℝ) ≤ P ^ (95 / 100 : ℝ)
  let B : Outcomes E → Prop := fun s => (1 / 100 : ℝ) * Real.log P < excessLog E s
  have hi : eventMass E L ≤ eventMass E U + eventMass E B := by
    rw [eventMass, eventMass, eventMass, ← Summable.tsum_add
      (product_event_summable E htwo U) (product_event_summable E htwo B)]
    apply Summable.tsum_le_tsum _ (product_event_summable E htwo L)
      ((product_event_summable E htwo U).add (product_event_summable E htwo B))
    intro s
    have hw := productMass_nonneg E htwo s
    by_cases hl : L s
    · by_cases hz : B s
      · simp only [ite_eq_left hl, ite_eq_left hz]; split_ifs <;> linarith
      · have hu : U s := source_cutoff_implication E hE hP s hl (le_of_not_gt hz)
        simp only [ite_eq_left hl, ite_eq_left hu, ite_eq_right hz, add_zero, le_refl]
    · simp only [ite_eq_right hl]; split_ifs <;> linarith
  have ht := excess_tail_le E htwo (show 0 < (1 / 100 : ℝ) * Real.log P by
    exact mul_pos (by norm_num) (Real.log_pos hP))
  have he : uniformMomentBound / ((1 / 100 : ℝ) * Real.log P) =
      100 * uniformMomentBound / Real.log P := by ring
  rw [he] at ht
  change eventMass E L - _ ≤ eventMass E U
  change eventMass E B ≤ _ at ht
  linarith

end EulerWeightedLower


end Erdos970

end OAI

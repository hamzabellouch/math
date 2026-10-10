import OAI.NumberTheory.TotientAsymptotic.Arithmetic

namespace OAI

noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma one_sub_prod_le_sum {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i ∧ a i ≤ 1) :
    1-∏ i ∈ S, a i ≤ ∑ i ∈ S, (1-a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have hS : ∀ j ∈ S, 0 ≤ a j ∧ a j ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hp0 : 0 ≤ ∏ j ∈ S, a j := Finset.prod_nonneg (fun j hj => (hS j hj).1)
    have hp1 : ∏ j ∈ S, a j ≤ 1 :=
      Finset.prod_le_one₀ (fun j hj => (hS j hj).1) (fun j hj => (hS j hj).2)
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    have hh := ih hS
    nlinarith [mul_nonneg (sub_nonneg.mpr hai.2) (sub_nonneg.mpr hp1)]

lemma min_one_lipschitz (u v : ℝ) : |min 1 u-min 1 v| ≤ |u-v| := by
  simpa only [sub_self,abs_zero,max_eq_right (abs_nonneg (u-v))] using
    abs_min_sub_min_le_max (1 : ℝ) u 1 v

/-- A bounded additive perturbation is valid even when the original weight
vanishes, including the boundary r=k. -/
lemma fk_reciprocal_lipschitz (k : ℕ) {r q : ℝ} (hr : 1 ≤ r)
    (_hq : 0 < q) (hq1 : q ≤ 1) :
    |fk k (r/q)-fk k r| ≤ (2*(k : ℝ)+1)*(1-q) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hdiff (c : ℝ) (hc : 0 ≤ c) :
      |c/(r/q)-c/r| = c*(1-q)/r := by
    have he : c/(r/q)-c/r=-(c*(1-q)/r) := by field_simp; ring
    rw [he,abs_neg,abs_of_nonneg (by positivity)]
  unfold fk
  calc
    _ = |(min 1 ((k+1 : ℝ)/(r/q))-min 1 ((k+1 : ℝ)/r))-
        (min 1 ((k : ℝ)/(r/q))-min 1 ((k : ℝ)/r))| := by congr 1; ring
    _ ≤ |min 1 ((k+1 : ℝ)/(r/q))-min 1 ((k+1 : ℝ)/r)|+
        |min 1 ((k : ℝ)/(r/q))-min 1 ((k : ℝ)/r)| := abs_sub _ _
    _ ≤ |(k+1 : ℝ)/(r/q)-(k+1 : ℝ)/r|+|(k : ℝ)/(r/q)-(k : ℝ)/r| :=
      add_le_add (min_one_lipschitz _ _) (min_one_lipschitz _ _)
    _ = (2*(k : ℝ)+1)*(1-q)/r := by
      rw [hdiff _ (by positivity),hdiff _ (Nat.cast_nonneg k)]
      ring
    _ ≤ _ := div_le_self (by positivity) hr

end TotientAsymptotic

end

end OAI

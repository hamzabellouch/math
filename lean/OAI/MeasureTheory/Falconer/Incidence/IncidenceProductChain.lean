import OAI.MeasureTheory.Falconer.Recursion.UniformScaleBudgets

namespace OAI

/-! Finite composition of the actual pencil-normalized scale ratios.
The terminal estimate needs only a single nonempty pencil. -/
namespace Falconer
open scoped BigOperators

theorem pencil_union_ratio_one_le {m : ℝ} (hm : 0 < m)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hV : ∀ x ∈ P, m ≤ ((V x).card:ℝ)) :
    1 ≤ ((P.biUnion V).card:ℝ)/m := by
  classical
  obtain ⟨x,hx⟩ := hP
  apply (le_div_iff₀ hm).2
  simpa only [one_mul] using (hV x hx).trans
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_biUnion_of_mem V hx)))

theorem finite_scale_ratio_product (n : ℕ) (R B C : ℕ → ℝ)
    (hB : ∀ i < n, 0 ≤ B i) (hC : ∀ i < n, 0 ≤ C i)
    (hstep : ∀ i < n, B i*R (i+1) ≤ C i*R i) (hend : 1 ≤ R n) :
    (∏ i ∈ Finset.range n, B i) ≤ (∏ i ∈ Finset.range n, C i)*R 0 := by
  induction n generalizing R B C with
  | zero => simpa using hend
  | succ n ih =>
    have htail := ih (fun i => R (i+1)) (fun i => B (i+1)) (fun i => C (i+1))
      (fun i hi => hB _ (by omega)) (fun i hi => hC _ (by omega))
      (fun i hi => hstep _ (by omega)) hend
    rw [Finset.prod_range_succ',Finset.prod_range_succ']
    calc
      _ ≤ ((∏ i ∈ Finset.range n, C (i+1))*R 1)*B 0 :=
        mul_le_mul_of_nonneg_right htail (hB 0 (by omega))
      _ = (∏ i ∈ Finset.range n, C (i+1))*(B 0*R 1) := by ring
      _ ≤ (∏ i ∈ Finset.range n, C (i+1))*(C 0*R 0) :=
        mul_le_mul_of_nonneg_left (hstep 0 (by omega))
          (Finset.prod_nonneg fun i hi => hC (i+1) (by have := Finset.mem_range.mp hi; omega))
      _ = _ := by ring

theorem finite_scale_power_ratio (n : ℕ) (R e C : ℕ → ℝ)
    (hC : ∀ i < n, 0 ≤ C i)
    (hstep : ∀ i < n, (2:ℝ)^(e i)*R (i+1) ≤ C i*R i) (hend : 1 ≤ R n) :
    (2:ℝ)^(∑ i ∈ Finset.range n, e i) ≤ (∏ i ∈ Finset.range n, C i)*R 0 := by
  rw [Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)]
  exact finite_scale_ratio_product n R (fun i => (2:ℝ)^(e i)) C
    (fun _ _ => by positivity) hC hstep hend

theorem finite_scale_power_gain (n : ℕ) (R e C : ℕ → ℝ)
    (hC : ∀ i < n, 0 ≤ C i)
    (hstep : ∀ i < n, (2:ℝ)^(e i)*R (i+1) ≤ C i*R i) (hend : 1 ≤ R n)
    {a loss : ℝ} (hexponent : a+loss ≤ ∑ i ∈ Finset.range n, e i)
    (hcost : (∏ i ∈ Finset.range n, C i) ≤ (2:ℝ)^loss) :
    (2:ℝ)^a ≤ R 0 := by
  have hprod := finite_scale_power_ratio n R e C hC hstep hend
  have hR : 0 ≤ R 0 := by
    by_contra hn
    have hcost0 := Finset.prod_nonneg fun i hi => hC i (Finset.mem_range.mp hi)
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hcost0 (le_of_not_ge hn)
    exact (not_lt_of_ge (hprod.trans hnonpos)) (by positivity)
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < (2:ℝ)^loss)).1
  calc
    (2:ℝ)^loss*(2:ℝ)^a = (2:ℝ)^(a+loss) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    _ ≤ (2:ℝ)^(∑ i ∈ Finset.range n, e i) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ ≤ (∏ i ∈ Finset.range n, C i)*R 0 := hprod
    _ ≤ (2:ℝ)^loss*R 0 := mul_le_mul_of_nonneg_right hcost hR

end Falconer

end OAI

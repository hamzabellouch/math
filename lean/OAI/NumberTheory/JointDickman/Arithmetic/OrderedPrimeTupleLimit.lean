import OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeBoundary
import OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeSubsets

namespace OAI

/-! # Limits of ordered reciprocal-prime sums -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem orderedPrimeLogProduct_box_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (n : ℕ) (a b : Fin (n+1) → ℝ) {v : ℝ → ℝ} {u : ℝ}
    (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun x => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      (orderedPrimeBox (n+1) a b (v x)) : ℝ)) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (orderedPrimeBox (n+1) a b u) : ℝ)) := by
  have hm0 : (logarithmicPrimeMeasure c).mass ≠ 0 := by
    intro h
    have he := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [logarithmicPrimeMeasure_mass hc hc1.le, NNReal.coe_zero] at he
    linarith [Real.log_neg hc hc1]
  have hne : (FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c)) ≠ 0 := by
    apply (FiniteMeasure.mass_nonzero_iff _).mp
    rw [FiniteMeasure.mass_pi]
    exact prod_ne_zero_iff.mpr (fun _ _ => hm0)
  apply moving_monotone_tendsto
    (F := fun x t => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      (orderedPrimeBox (n+1) a b t) : ℝ)) _ _
    (orderedPrimeBox_measure_continuous (c := c) n a b).continuousAt hv
  · intro x s t hst
    apply NNReal.coe_le_coe.mpr
    apply FiniteMeasure.apply_mono
    rintro y ⟨hym,hyb,hys⟩
    exact ⟨hym,hyb,hys.trans hst⟩
  · intro t
    apply NNReal.tendsto_coe.mpr
    apply finiteMeasure_set_tendsto (primeLogProduct_tendsto hc hc1 (n+1)) hne
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact orderedPrimeBox_null_frontier _ n a b t

theorem strictMono_logPrimeTuple_iff {x : ℝ} (hx : 1 < x) {h : ℕ}
    (v : Fin h → ℕ) (hv : ∀ i, 0 < v i) :
    StrictMono (fun i => Real.log (v i)/Real.log x) ↔ StrictMono v := by
  have he (i j : Fin h) : Real.log (v i)/Real.log x < Real.log (v j)/Real.log x ↔ v i < v j := by
    rw [div_lt_div_iff_of_pos_right (Real.log_pos hx),
      Real.log_lt_log_iff (by exact_mod_cast hv i) (by exact_mod_cast hv j)]
    exact_mod_cast (Iff.rfl : v i < v j ↔ v i < v j)
  constructor <;> intro hm i j hij
  · exact (he i j).mp (hm hij)
  · exact (he i j).mpr (hm hij)

open Classical in
theorem orderedPrimeLogProduct_box_apply {c x : ℝ} (hx : 1 < x) (h : ℕ)
    (a b : Fin h → ℝ) (u : ℝ) :
    ((FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) (orderedPrimeBox h a b u) : ℝ) =
      ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^c)) h,
        if (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
            (∏ i, (v i : ℝ)) ≤ x^u then ∏ i, 1/(v i : ℝ) else 0 := by
  rw [primeLogProduct_apply, orderedPrimeTuples, sum_filter]
  apply sum_congr rfl
  intro v hv
  have hp : ∀ i, 0 < v i := by
    intro i
    have hvi := Fintype.mem_piFinset.mp hv i
    exact (Nat.mem_primesLE.mp (mem_filter.mp hvi).1).2.pos
  have hm := strictMono_logPrimeTuple_iff hx v hp
  have hb : (fun i => Real.log (v i)/Real.log x) ∈ primeBoxCutoff h a b u ↔
      (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
        (∏ i, (v i : ℝ)) ≤ x^u := by
    simp only [primeBoxCutoff, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_ofPred_eq, logPrimeLocation_mem_Ioc hx (hp _),
      logPrimeTuple_sum_le hx v hp u]
  simp only [orderedPrimeBox, Set.mem_inter_iff, Set.mem_ofPred_eq, hm, hb]
  split_ifs <;> simp_all

open Classical in
theorem orderedReciprocalPrimeTuple_scaled_box_tendsto {c A : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hA : 0 < A) (n : ℕ) (a b : Fin (n+1) → ℝ) :
    Tendsto (fun x : ℝ =>
      ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^c)) (n+1),
        if (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
            (∏ i, (v i : ℝ)) ≤ A*x then ∏ i, 1/(v i : ℝ) else 0) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (orderedPrimeBox (n+1) a b 1) : ℝ)) := by
  apply (orderedPrimeLogProduct_box_tendsto hc hc1 n a b (log_scaled_ratio_tendsto hA)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [orderedPrimeLogProduct_box_apply hx, rpow_log_ratio hx (mul_pos hA (zero_lt_one.trans hx))]

end JointDickman

end OAI

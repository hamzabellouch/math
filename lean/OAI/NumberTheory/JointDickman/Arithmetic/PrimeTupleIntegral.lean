import OAI.NumberTheory.JointDickman.Amplification.AtomicProductMeasure
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeBoxBoundary

namespace OAI

/-! # Reciprocal prime tuples as finite product-measure integrals -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

open Classical in
theorem primeLogProduct_apply (c x : ℝ) (h : ℕ) (s : Set (Fin h → ℝ)) :
    ((FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) s : ℝ) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin h => largePrimeSet x (x^c)),
        if (fun i => Real.log (v i)/Real.log x) ∈ s then
          ∏ i, 1/(v i : ℝ) else 0 := by
  have he : primeLogMeasure c x = finiteAtomicMeasure (largePrimeSet x (x^c))
      (fun p => Real.toNNReal (1/(p : ℝ))) (fun p => Real.log p/Real.log x) := rfl
  simp only [he, finiteAtomicMeasure_pi, atomicTupleMeasure_apply, NNReal.coe_sum]
  apply sum_congr rfl
  intro v hv
  split_ifs <;> simp

theorem logPrimeTuple_sum_le {x : ℝ} (hx : 1 < x) {h : ℕ}
    (v : Fin h → ℕ) (hv : ∀ i, 0 < v i) (u : ℝ) :
    (∑ i, Real.log (v i)/Real.log x) ≤ u ↔ (∏ i, (v i : ℝ)) ≤ x^u := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp : ∀ i, (0 : ℝ) < v i := fun i => by exact_mod_cast hv i
  have hprod : 0 < ∏ i, (v i : ℝ) := prod_pos (fun i _ => hp i)
  rw [← sum_div, div_le_iff₀ (Real.log_pos hx)]
  rw [← Real.log_prod (fun i _ => (hp i).ne')]
  rw [← Real.log_rpow hx0, Real.log_le_log_iff hprod (Real.rpow_pos_of_pos hx0 u)]

open Classical in
theorem primeLogProduct_box_apply {c x : ℝ} (hx : 1 < x) (h : ℕ)
    (a b : Fin h → ℝ) (u : ℝ) :
    ((FiniteMeasure.pi (fun _ : Fin h => primeLogMeasure c x)) (primeBoxCutoff h a b u) : ℝ) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin h => largePrimeSet x (x^c)),
        if (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
            (∏ i, (v i : ℝ)) ≤ x^u then ∏ i, 1/(v i : ℝ) else 0 := by
  rw [primeLogProduct_apply]
  apply sum_congr rfl
  intro v hv
  have hp : ∀ i, 0 < v i := by
    intro i
    have hvi := Fintype.mem_piFinset.mp hv i
    exact (Nat.mem_primesLE.mp (mem_filter.mp hvi).1).2.pos
  have he : (fun i => Real.log (v i)/Real.log x) ∈ primeBoxCutoff h a b u ↔
      (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
        (∏ i, (v i : ℝ)) ≤ x^u := by
    simp only [primeBoxCutoff, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_ofPred_eq, logPrimeLocation_mem_Ioc hx (hp _),
      logPrimeTuple_sum_le hx v hp u]
  rw [he]
  split_ifs <;> rfl

open Classical in
theorem reciprocalPrimeTuple_box_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (n : ℕ) (a b : Fin (n+1) → ℝ) (u : ℝ) :
    Tendsto (fun x : ℝ =>
      ∑ v ∈ Fintype.piFinset (fun _ : Fin (n+1) => largePrimeSet x (x^c)),
        if (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
            (∏ i, (v i : ℝ)) ≤ x^u then ∏ i, 1/(v i : ℝ) else 0) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (primeBoxCutoff (n+1) a b u) : ℝ)) := by
  apply (primeLogProduct_box_tendsto hc hc1 n a b u).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact primeLogProduct_box_apply hx (n+1) a b u

end JointDickman

end OAI

import OAI.Probability.SLE.SimpleTails
import Mathlib.Analysis.SumIntegralComparisons

namespace OAI

/-! The half-integer row heights have an integrable boundary singularity.
This is the row sum used in the prescribed cover's missed-cell estimate. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge

lemma half_integer_row_sum_bound (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α<1) (N : ℕ) :
    (∑ j∈Finset.range N, ((j:ℝ)+1/2)^(-α)) ≤
      (2:ℝ)^α/(1-α)*(N:ℝ)^(1-α) := by
  have hq : 0<1-α := by linarith
  have hfi : IntegrableOn (fun x : ℝ => x^(-α)) (Icc 0 (N:ℝ)) := by
    have ha := (integrableOn_abs_heightPower α (N:ℝ) hα1).mono_set
      (show Icc (0:ℝ) N ⊆ Icc (-(N:ℝ)) N by
        intro x hx
        exact ⟨(neg_nonpos.mpr (Nat.cast_nonneg N)).trans hx.1,hx.2⟩)
    apply ha.congr_fun _ measurableSet_Icc
    intro x hx
    dsimp only
    rw [abs_of_nonneg hx.1]
  have hanti : AntitoneOn (fun x : ℝ => x^(-α)) (Ioc 0 (N:ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (neg_nonpos.mpr hα0)
  have hsum : (∑ j∈Finset.range N, ((j:ℝ)+1)^(-α)) ≤
      ∫ x in (0:ℝ)..(N:ℝ), x^(-α) := by
    have ha : AntitoneOn (fun x : ℝ => x^(-α)) (Ioc 0 (0+(N:ℝ))) := by
      simpa only [zero_add] using hanti
    simpa only [zero_add,Nat.cast_add,Nat.cast_one] using
      ha.sum_le_integral_of_integrableOn (x₀ := 0) (a := N) (by simpa only [zero_add] using hfi)
  have hint : (∫ x in (0:ℝ)..(N:ℝ), x^(-α)) = (N:ℝ)^(1-α)/(1-α) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < -α))]
    rw [show -α+1=1-α by ring,Real.zero_rpow hq.ne',sub_zero]
  have hhalf (j : ℕ) : ((j:ℝ)+1/2)^(-α) ≤ (2:ℝ)^α*((j:ℝ)+1)^(-α) := by
    have h := Real.rpow_le_rpow_of_nonpos
      (show (0:ℝ)<((j:ℝ)+1)/2 by positivity)
      (show ((j:ℝ)+1)/2 ≤ (j:ℝ)+1/2 by nlinarith [Nat.cast_nonneg (α := ℝ) j])
      (neg_nonpos.mpr hα0)
    refine h.trans_eq ?_
    rw [Real.div_rpow (by positivity) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
    ring
  calc
    _ ≤ ∑ j∈Finset.range N, (2:ℝ)^α*((j:ℝ)+1)^(-α) := Finset.sum_le_sum (fun j _ => hhalf j)
    _ = (2:ℝ)^α*∑ j∈Finset.range N, ((j:ℝ)+1)^(-α) := (Finset.mul_sum ..).symm
    _ ≤ (2:ℝ)^α*(∫ x in (0:ℝ)..(N:ℝ), x^(-α)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by rw [hint]; ring

end SLEExactGauge

end

end OAI

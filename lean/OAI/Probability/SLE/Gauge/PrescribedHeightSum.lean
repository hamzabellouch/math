import OAI.Probability.SLE.Gauge.PrescribedRowSum

namespace OAI

/-! Uniform sums of the actual half-row heights, including a lower strip
of arbitrary height. The bound is independent of the final mesh size. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge

lemma scaled_half_integer_row_sum (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α<1)
    {r : ℝ} (hr : 0<r) (N : ℕ) :
    (∑ j∈Finset.range N, (((j:ℝ)+1/2)*r)^(-α)) ≤
      ((2:ℝ)^α/(1-α))*r⁻¹*((N:ℝ)*r)^(1-α) := by
  have he : r^(-α)=r⁻¹*r^(1-α) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hr]
    congr 1
    ring
  calc
    _ = r^(-α)*∑ j∈Finset.range N, ((j:ℝ)+1/2)^(-α) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.mul_rpow (by positivity) hr.le,mul_comm]
    _ ≤ r^(-α)*(((2:ℝ)^α/(1-α))*(N:ℝ)^(1-α)) :=
      mul_le_mul_of_nonneg_left (half_integer_row_sum_bound α hα0 hα1 N)
        (Real.rpow_nonneg hr.le _)
    _ = _ := by
      rw [Real.mul_rpow (Nat.cast_nonneg N) hr.le,he]
      ring

lemma half_integer_lower_strip_sum (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α<1)
    {r η : ℝ} (hr : 0<r) (hη : 0 ≤ η) (N : ℕ) :
    (∑ j∈(Finset.range N).filter (fun j : ℕ => ((j:ℝ)+1/2)*r<η),
      (((j:ℝ)+1/2)*r)^(-α)) ≤
      ((2:ℝ)^α/(1-α))*r⁻¹*(η+r)^(1-α) := by
  classical
  let M := ⌊η/r⌋₊+1
  have hsub : (Finset.range N).filter (fun j : ℕ => ((j:ℝ)+1/2)*r<η) ⊆ Finset.range M := by
    intro j hj
    have hy := (Finset.mem_filter.mp hj).2
    have hjR : (j:ℝ) ≤ η/r := by
      apply (le_div_iff₀ hr).mpr
      nlinarith
    have hjM : j ≤ ⌊η/r⌋₊ := Nat.le_floor hjR
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hjM)
  have hMr : (M:ℝ)*r ≤ η+r := by
    have hfloor := Nat.floor_le (div_nonneg hη hr.le)
    have h := mul_le_mul_of_nonneg_right hfloor hr.le
    rw [div_mul_cancel₀ _ hr.ne'] at h
    dsimp only [M]
    push_cast
    nlinarith
  calc
    _ ≤ ∑ j∈Finset.range M, (((j:ℝ)+1/2)*r)^(-α) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => Real.rpow_nonneg (by positivity) _)
    _ ≤ ((2:ℝ)^α/(1-α))*r⁻¹*((M:ℝ)*r)^(1-α) := scaled_half_integer_row_sum α hα0 hα1 hr M
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg M) hr.le) hMr (by linarith))
      (by positivity)

end SLEExactGauge

end

end OAI

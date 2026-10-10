import OAI.Probability.SLE.Gauge.PrescribedGridStripSum
import OAI.Probability.SLE.Gauge.PrescribedMissedExpectation

namespace OAI

/-! Summing the interior failure bound and the boundary visit bound over
  the actual shifted mesh cancels the three powers of its scale. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma prescribed_grid_error_sum (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α<1)
    {R r η ε A : ℝ} (hR : 0 ≤ R) (hr : 0<r) (hr1 : r ≤ 1)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (hA : 0 ≤ A) (K : Set ℂ) :
    (∑ ij∈prescribedGridIndex R r K,
      A*r^α*(prescribedGridCenter r ij).im^(-α)*
        (ε + if (prescribedGridCenter r ij).im<η then 1 else 0)) ≤
      A*r^α*(((2*R+5)*((2:ℝ)^α/(1-α)))*r^(-2:ℝ)*
        ((R+3)^(1-α)*ε+(η+r)^(1-α))) := by
  classical
  let I := prescribedGridIndex R r K
  let w := fun ij => (prescribedGridCenter r ij).im^(-α)
  have heq : (∑ ij∈I, A*r^α*w ij*(ε + if (prescribedGridCenter r ij).im<η then 1 else 0)) =
      A*r^α*(ε*(∑ ij∈I,w ij)+
        ∑ ij∈I.filter (fun ij => (prescribedGridCenter r ij).im<η),w ij) := by
    rw [Finset.sum_filter,Finset.mul_sum,← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij _
    split_ifs <;> ring
  rw [heq]
  have hfull := prescribed_grid_height_sum_bound α hα0 hα1 hR hr hr1 K
  have hstrip := prescribed_grid_lower_strip_sum α hα0 hα1 hR hr hr1 hη K
  have hh := add_le_add (mul_le_mul_of_nonneg_left hfull hε) hstrip
  apply (mul_le_mul_of_nonneg_left hh (mul_nonneg hA (Real.rpow_nonneg hr.le _))).trans
  apply le_of_eq
  ring

lemma prescribed_cleanup_power_cancellation (κ : ℝ) {r : ℝ} (hr : 0<r) :
    r^Target.d κ*r^codimension κ*r^(-2:ℝ)=1 := by
  have he : Target.d κ=dimension κ := by
    rw [Target.dimension_eq]
    rfl
  rw [he]
  simpa only [mul_comm,mul_left_comm,mul_assoc] using dense_cover_power_cancellation κ hr

lemma prescribed_cleanup_error_bound (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    {R r η ε A : ℝ} (hR : 0 ≤ R) (hr : 0<r) (hr1 : r ≤ 1)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (hA : 0 ≤ A) (K : Set ℂ) (n : ℕ) :
    (36*(n:ℝ)*r^Target.d κ) *
      (∑ ij∈prescribedGridIndex R r K,
        A*r^codimension κ*(prescribedGridCenter r ij).im^(-codimension κ)*
          (ε + if (prescribedGridCenter r ij).im<η then 1 else 0)) ≤
      (36*A*((2*R+5)*((2:ℝ)^codimension κ/(1-codimension κ))))*
        ((R+3)^(1-codimension κ)*((n:ℝ)*ε)+(n:ℝ)*(η+r)^(1-codimension κ)) := by
  have hα0 : 0 ≤ codimension κ := (codimension_pos κ hκ8).le
  have hα1 : codimension κ<1 := codimension_lt_one κ hκ
  apply (mul_le_mul_of_nonneg_left
    (prescribed_grid_error_sum (codimension κ) hα0 hα1 hR hr hr1 hη hε hA K)
      (by positivity : 0 ≤ 36*(n:ℝ)*r^Target.d κ)).trans
  apply le_of_eq
  have hp := prescribed_cleanup_power_cancellation κ hr
  calc
    _ = (36*A*((2*R+5)*((2:ℝ)^codimension κ/(1-codimension κ))))*
        (r^Target.d κ*r^codimension κ*r^(-2:ℝ))*
        ((R+3)^(1-codimension κ)*((n:ℝ)*ε)+(n:ℝ)*(η+r)^(1-codimension κ)) := by ring
    _ = _ := by rw [hp,mul_one]

end SLEExactGauge

end

end OAI

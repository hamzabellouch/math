import OAI.MeasureTheory.Falconer.Geometry.BinEstimates
import OAI.MeasureTheory.Falconer.Measures.FiniteMeasureProducts

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem ennreal_sq_bound_sqrt {x y F : ℝ≥0∞} (h : x^2 ≤ F*y^2) :
    x ≤ F^(1/2:ℝ)*y := by
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hh
  simp only [← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
  norm_num at hh
  exact hh

theorem bin_cross_from_squares (α β : Measure ℝ) (w : ℝ) {F a b : ℝ≥0∞}
    (ha : (binL2Norm α w)^2 ≤ F*a^2) (hb : (binL2Norm β w)^2 ≤ F*b^2) :
    (∑' k : ℤ, α (realBin w k)*β (realBin w k)) ≤ F*(a*b) := by
  have hcross := ennreal_offset_cauchy (fun k => α (realBin w k))
    (fun k => β (realBin w k)) 0
  simp only [sub_zero] at hcross
  have hh := hcross.trans (mul_le_mul' (ennreal_sq_bound_sqrt ha) (ennreal_sq_bound_sqrt hb))
  have hs : F^(1/2:ℝ)*F^(1/2:ℝ) = F := by
    rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
    norm_num
  apply hh.trans_eq
  calc
    _ = (F^(1/2:ℝ)*F^(1/2:ℝ))*(a*b) := mul_mul_mul_comm _ _ _ _
    _ = _ := by rw [hs]

theorem finite_bin_collision_comparison {ι : Type*} (S : Finset ι)
    (α β : ι → Measure ℝ) [∀ i, IsFiniteMeasure (α i)] [∀ i, IsFiniteMeasure (β i)]
    (w : ℝ) (E : Set (ℝ × ℝ)) (F : ℝ≥0∞)
    (hnorm : ∀ i ∈ S, (binL2Norm (α i) w)^2 ≤ F*((β i) univ)^2)
    (hcoarse : ∀ i ∈ S, ∀ j ∈ S,
      (∃ k : ℤ, α i (realBin w k) ≠ 0 ∧ α j (realBin w k) ≠ 0) →
      ((β i).prod (β j)) E = (β i univ)*(β j univ)) :
    (binL2Norm (∑ i ∈ S, α i) w)^2 ≤
      F*((∑ i ∈ S, β i).prod (∑ i ∈ S, β i)) E := by
  classical
  have hpair (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      (∑' k : ℤ, α i (realBin w k)*α j (realBin w k)) ≤ F*((β i).prod (β j)) E := by
    by_cases hh : ∃ k : ℤ, α i (realBin w k) ≠ 0 ∧ α j (realBin w k) ≠ 0
    · rw [hcoarse i hi j hj hh]
      exact bin_cross_from_squares _ _ w (hnorm i hi) (hnorm j hj)
    · have hz (k : ℤ) : α i (realBin w k)*α j (realBin w k) = 0 := by
        by_cases hi0 : α i (realBin w k) = 0
        · simp [hi0]
        · have hj0 : α j (realBin w k) = 0 := by
            by_contra hj0
            exact hh ⟨k,hi0,hj0⟩
          simp [hj0]
      simp only [hz,tsum_zero,zero_le]
  rw [pow_two,binL2Norm_mul_self]
  simp only [Measure.finsetSum_apply,pow_two,Finset.sum_mul,Finset.mul_sum]
  simp_rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, F*((β i).prod (β j)) E :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ = _ := by
      rw [finite_measure_prod_sum]
      simp only [Measure.finsetSum_apply,Finset.mul_sum]

end PlanarFalconer

end OAI

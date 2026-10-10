import OAI.Geometry.RCD.Metric.ProductPackingGrid

namespace OAI

/-! # Finite separated samples of one geodesic in an extra factor -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

def geodesicSampleTime {m : ℕ} (hm : 0 < m) (i : Fin m) : Time :=
  ⟨(i.val:ℝ)/m,div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast hm)).mpr (by exact_mod_cast i.isLt.le)⟩

theorem geodesicSampleTime_gap {m : ℕ} (hm : 0 < m) {i j : Fin m} (hij : i ≠ j) :
    1/(m:ℝ) ≤ |(geodesicSampleTime hm i:ℝ)-(geodesicSampleTime hm j:ℝ)| := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hgap : (1:ℝ) ≤ |(i.val:ℝ)-(j.val:ℝ)| := by
    rcases lt_or_gt_of_ne hval with h | h
    · have hh : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  change 1/(m:ℝ) ≤ |(i.val:ℝ)/m-(j.val:ℝ)/m|
  rw [← sub_div,abs_div,abs_of_pos hm']
  exact div_le_div_of_nonneg_right hgap hm'.le

theorem IsGeodesic.packing_samples {Z : Type*} [MetricSpace Z]
    {γ : C(Time,Z)} (hγ : IsGeodesic γ) {m : ℕ} (hm : 0 < m) :
    ∃ z : Fin m → Z,
      (∀ i, dist (z i) (γ 0) ≤ dist (γ 0) (γ 1)) ∧
      Pairwise (fun i j => dist (γ 0) (γ 1)/(m:ℝ) ≤ dist (z i) (z j)) := by
  refine ⟨fun i => γ (geodesicSampleTime hm i),?_,?_⟩
  · intro i
    rw [hγ]
    change |(geodesicSampleTime hm i:ℝ)-0| *dist (γ 0) (γ 1) ≤ _
    rw [sub_zero,abs_of_nonneg (geodesicSampleTime hm i).2.1]
    exact mul_le_of_le_one_left dist_nonneg (geodesicSampleTime hm i).2.2
  · intro i j hij
    rw [hγ (geodesicSampleTime hm i) (geodesicSampleTime hm j)]
    have hh := mul_le_mul_of_nonneg_right (geodesicSampleTime_gap hm hij)
      (dist_nonneg : 0 ≤ dist (γ 0) (γ 1))
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hh

end RegularPointCoordinates

end

end OAI

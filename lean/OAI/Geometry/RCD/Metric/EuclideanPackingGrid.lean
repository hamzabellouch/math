import OAI.Geometry.RCD.Metric.ApproximatePacking

namespace OAI

/-! # The finite Euclidean grid for the extra-factor packing obstruction -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

def euclideanPackingGrid {n m : ℕ} (a : ℝ) (j : Fin n → Fin m) : Euclidean n :=
  WithLp.toLp 2 (fun i => a*((j i).val:ℝ))

theorem euclideanPackingGrid_norm_le {n m : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 ≤ a)
    (j : Fin n → Fin m) : ‖euclideanPackingGrid a j‖ ≤ (n:ℝ)*m*a := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hval (i : Fin n) : (j i).val ≤ m := (j i).isLt.le
  have hbound (i : Fin n) : (a*((j i).val:ℝ))^2 ≤ ((m:ℝ)*a)^2 := by
    have hi : ((j i).val:ℝ) ≤ m := by exact_mod_cast hval i
    have hpos : 0 ≤ a*((j i).val:ℝ) := by positivity
    have hle : a*((j i).val:ℝ) ≤ (m:ℝ)*a := by nlinarith
    nlinarith
  have hsq : ‖euclideanPackingGrid a j‖^2 ≤ (n:ℝ)*((m:ℝ)*a)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin n, ((m:ℝ)*a)^2 := Finset.sum_le_sum (fun i _ => hbound i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hnn : 0 ≤ (n:ℝ)^2-n := by nlinarith
  have hh := mul_nonneg hnn (sq_nonneg ((m:ℝ)*a))
  nlinarith [norm_nonneg (euclideanPackingGrid a j),show 0 ≤ (n:ℝ)*m*a by positivity]

theorem euclideanPackingGrid_separated {n m : ℕ} {a : ℝ} (ha : 0 ≤ a)
    {j k : Fin n → Fin m} (hjk : j ≠ k) :
    a ≤ dist (euclideanPackingGrid a j) (euclideanPackingGrid a k) := by
  have hex : ∃ i, j i ≠ k i := Function.ne_iff.mp hjk
  obtain ⟨i,hi⟩ := hex
  have hv : (j i).val ≠ (k i).val := fun h => hi (Fin.ext h)
  have hgap : a ≤ |a*((j i).val:ℝ)-a*((k i).val:ℝ)| := by
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · have hh : ((j i).val:ℝ)+1 ≤ (k i).val := by exact_mod_cast hlt
      have hp : a*((j i).val:ℝ) ≤ a*((k i).val:ℝ) := by nlinarith
      rw [abs_of_nonpos (sub_nonpos.mpr hp)]
      nlinarith
    · have hh : ((k i).val:ℝ)+1 ≤ (j i).val := by exact_mod_cast hgt
      have hp : a*((k i).val:ℝ) ≤ a*((j i).val:ℝ) := by nlinarith
      rw [abs_of_nonneg (sub_nonneg.mpr hp)]
      nlinarith
  have hcoord := PiLp.norm_apply_le (euclideanPackingGrid a j-euclideanPackingGrid a k) i
  have hc : |a*((j i).val:ℝ)-a*((k i).val:ℝ)| ≤
      ‖euclideanPackingGrid a j-euclideanPackingGrid a k‖ := by
    simpa only [euclideanPackingGrid,PiLp.sub_apply,Real.norm_eq_abs] using hcoord
  exact hgap.trans hc

end RegularPointCoordinates

end

end OAI

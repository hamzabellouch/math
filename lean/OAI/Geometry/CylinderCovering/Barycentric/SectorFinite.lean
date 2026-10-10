import OAI.Geometry.CylinderCovering.Barycentric.SectorNeighborhood
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace RadialCoordinates.BarycentricSector
open CylinderCovering.RadialRiemann

theorem equal_cell_intercepted_area_bound {N : ℕ} (hN : 0 < N)
    {k M₀ : ℝ} (hk : 0 ≤ k) (M : Fin N → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hMM : ∀ i, M i ≤ M₀) (S : Fin N → Set Plane)
    (hS : ∀ i, S i ⊆ neighborhood (point 0 1 N i) (point 0 1 N (i+1)) k (M i))
    (W : Fin N → ℝ) (hW0 : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) :
    (∑ i : Fin N, W i * volume.real (S i)) ≤
      (∑ i : Fin N, W i * ((1/(N:ℝ))*(M i)^2/2)) +
        (18*k*M₀+162*k^2)/(N:ℝ) := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNR
  have hM₀ : 0 ≤ M₀ := by
    exact (hM ⟨0,hN⟩).trans (hMM ⟨0,hN⟩)
  let C := 18*k*M₀+162*k^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlocal (i : Fin N) :
      W i * volume.real (S i) ≤ W i*((1/(N:ℝ))*(M i)^2/2)+C*(1/(N:ℝ))^2 := by
    have hl := point_mem (by norm_num : (0:ℝ) < 1) hN i.isLt.le
    have hr := point_mem (by norm_num : (0:ℝ) < 1) hN (Nat.succ_le_of_lt i.isLt)
    have hwidth : point 0 1 N (i+1)-point 0 1 N i = 1/(N:ℝ) := by
      rw [point_succ, step]
      norm_num
    have hlr : point 0 1 N i ≤ point 0 1 N (i+1) := by
      have := one_div_pos.mpr hNR
      linarith
    have hbound := intercepted_area_bound hl.1 hlr hr.2 hk (hM i) (hMM i) (hS i)
    rw [hwidth] at hbound
    change volume.real (S i) ≤ 1/(N:ℝ)*(M i)^2/2+C*(1/(N:ℝ))^2 at hbound
    have hwBound := mul_le_mul_of_nonneg_left hbound (hW0 i)
    have hwError := mul_le_mul_of_nonneg_right (hW1 i)
      (show 0 ≤ C*(1/(N:ℝ))^2 by positivity)
    nlinarith
  calc
    _ ≤ ∑ i : Fin N, (W i*((1/(N:ℝ))*(M i)^2/2)+C*(1/(N:ℝ))^2) :=
      Finset.sum_le_sum (fun i _ => hlocal i)
    _ = (∑ i : Fin N, W i*((1/(N:ℝ))*(M i)^2/2)) + C/(N:ℝ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 1
      field_simp
    _ = _ := rfl

end RadialCoordinates.BarycentricSector

end

end OAI

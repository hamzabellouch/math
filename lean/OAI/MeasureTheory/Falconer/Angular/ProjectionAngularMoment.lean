import OAI.MeasureTheory.Falconer.Recursion.SurfacePotential
import OAI.MeasureTheory.Falconer.Geometry.NormalSeparation

namespace OAI

/-! Subcritical angular moments of the norm of hyperplane projections. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem ennreal_inverse_power_scale_two {a b s : ℝ} (hs : 0 ≤ s)
    (hab : a ≤ 2*b) :
    (ENNReal.ofReal b)^(-s) ≤ (2 : ℝ≥0∞)^s * (ENNReal.ofReal a)^(-s) := by
  have h : (ENNReal.ofReal (2*b))^(-s) ≤ (ENNReal.ofReal a)^(-s) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hab) hs)
  calc
    _ = (2 : ℝ≥0∞)^s * ((2 : ℝ≥0∞)^(-s) * (ENNReal.ofReal b)^(-s)) := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      simp
    _ = (2 : ℝ≥0∞)^s * (ENNReal.ofReal (2*b))^(-s) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ENNReal.mul_rpow_of_ne_top (by norm_num) ENNReal.ofReal_ne_top]
    _ ≤ _ := mul_le_mul_right h _

theorem perpendicular_inverse_power_bound {d : ℕ} {u w : Space d}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {s : ℝ} (hs : 0 ≤ s) :
    (ENNReal.ofReal ‖perpendicularPart w u‖)^(-s) ≤
      (2 : ℝ≥0∞)^s * ((edist u w)^(-s) + (edist (-u) w)^(-s)) := by
  apply (ennreal_inverse_power_scale_two hs (normalDistance_le_perpendicular hw hu)).trans
  apply mul_le_mul_right
  have hd1 : edist u w = ENNReal.ofReal ‖w-u‖ := by
    rw [edist_dist, dist_eq_norm, norm_sub_rev]
  have hd2 : edist (-u) w = ENNReal.ofReal ‖w+u‖ := by
    rw [edist_comm, edist_dist, dist_eq_norm, sub_neg_eq_add]
  rw [hd1, hd2]
  rcases le_total ‖w-u‖ ‖w+u‖ with h | h
  · rw [normalDistance, min_eq_left h]
    exact le_add_right le_rfl
  · rw [normalDistance, min_eq_right h]
    exact le_add_left le_rfl

theorem unit_projection_angular_bound (n : ℕ) {s : ℝ} (hs : 0 < s) (hsn : s < n) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ u : Space (n+1), ‖u‖ = 1 →
      (∫⁻ w : Sphere (n+1),
        (ENNReal.ofReal ‖perpendicularPart (w : Space (n+1)) u‖)^(-s)
          ∂sphereMeasure (n+1)) ≤ C := by
  obtain ⟨B, hB, hb⟩ := surface_potential_uniform_bound n hs hsn
  refine ⟨(2 : ℝ≥0∞)^s * (B+B), ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hs.le (by norm_num)) (ENNReal.add_lt_top.mpr ⟨hB,hB⟩), ?_⟩
  intro u hu
  have hpot (x : Space (n+1)) :
      (∫⁻ w : Sphere (n+1), (edist x (w : Space (n+1)))^(-s)
        ∂sphereMeasure (n+1)) ≤ B := by
    have hm : Measurable (fun y : Space (n+1) => (edist x y)^(-s)) := by fun_prop
    simpa only [surfaceMeasure, lintegral_map hm measurable_subtype_coe] using hb x
  calc
    _ ≤ ∫⁻ w : Sphere (n+1), (2 : ℝ≥0∞)^s *
        ((edist u (w : Space (n+1)))^(-s) + (edist (-u) (w : Space (n+1)))^(-s))
          ∂sphereMeasure (n+1) :=
      lintegral_mono (fun w => perpendicular_inverse_power_bound hu (sphere_norm w) hs.le)
    _ = (2 : ℝ≥0∞)^s *
        ((∫⁻ w : Sphere (n+1), (edist u (w : Space (n+1)))^(-s) ∂sphereMeasure (n+1)) +
         (∫⁻ w : Sphere (n+1), (edist (-u) (w : Space (n+1)))^(-s) ∂sphereMeasure (n+1))) := by
      rw [lintegral_const_mul, lintegral_add_left]
      all_goals fun_prop
    _ ≤ _ := mul_le_mul_right (add_le_add (hpot u) (hpot (-u))) _

end Falconer

end OAI

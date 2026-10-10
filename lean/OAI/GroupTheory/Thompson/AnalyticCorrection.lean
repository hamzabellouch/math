import OAI.GroupTheory.Thompson.CorrectionLocal
import OAI.GroupTheory.Thompson.CorrectionNonzero

namespace OAI

/-!
# Global gluing of the explicit Hilbert correction

The cutoff tails tend to zero at the actual tube boundary. These estimates
give the mixed inside/outside case; a uniform bound on the additive change
handles distant pairs. Together with the local tube estimate, this covers
every pair of points, including the boundary itself.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : RegularCurveData E}

namespace CorrectionData

variable (D : CorrectionData C)

theorem rotated_residual_sub_bound (x : C.tube) :
    ‖D.R (C.parameter x) (C.residual x) - C.residual x‖ ≤ 2 * ‖C.residual x‖ := by
  calc
    _ ≤ ‖D.R (C.parameter x) (C.residual x)‖ + ‖C.residual x‖ := norm_sub_le _ _
    _ = _ := by rw [D.norm_R]; ring

theorem change_bound (x : C.tube) :
    ‖D.change x‖ ≤ beta C.rho ‖C.residual x‖ * (7 / 16) +
      chi C.rho ‖C.residual x‖ * (2 * ‖C.residual x‖) := by
  calc
    _ ≤ ‖(beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) • D.v (C.parameter x)‖ +
        ‖chi C.rho ‖C.residual x‖ •
          (D.R (C.parameter x) (C.residual x) - C.residual x)‖ := norm_add_le _ _
    _ = beta C.rho ‖C.residual x‖ * |D.q (C.parameter x)| +
        chi C.rho ‖C.residual x‖ *
          ‖D.R (C.parameter x) (C.residual x) - C.residual x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg (beta_nonneg _ _),
        abs_of_nonneg (chi_nonneg _ _), D.norm_v, mul_one]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (D.q_bound _) (beta_nonneg _ _))
      (mul_le_mul_of_nonneg_left (D.rotated_residual_sub_bound x) (chi_nonneg _ _))

theorem change_uniform_bound (x : C.tube) :
    ‖D.change x‖ ≤ 7 / 16 + 2 * C.rho := by
  have hb := beta_le_one C.rho ‖C.residual x‖
  have hc := chi_le_one C.rho ‖C.residual x‖
  have hr := (C.residual_norm_lt x).le
  have hchi := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 2 * ‖C.residual x‖ by positivity)
  have hbeta := mul_le_mul_of_nonneg_right hb (show (0 : ℝ) ≤ 7 / 16 by norm_num)
  have h := D.change_bound x
  linarith

theorem change_tail_bound (x : C.tube) :
    ‖D.change x‖ ≤ (7 / (8 * C.rho) + 4) * (C.rho - ‖C.residual x‖) := by
  have hr := (C.residual_norm_lt x).le
  have ht : 0 ≤ 2 * (C.rho - ‖C.residual x‖) / C.rho :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hr)) C.rho_pos.le
  have hb := beta_le_tail C.rho_pos ‖C.residual x‖ (norm_nonneg _) hr
  have hc := chi_le_tail C.rho_pos ‖C.residual x‖ (norm_nonneg _) hr
  calc
    ‖D.change x‖ ≤ beta C.rho ‖C.residual x‖ * (7 / 16) +
        chi C.rho ‖C.residual x‖ * (2 * ‖C.residual x‖) := D.change_bound x
    _ ≤ (2 * (C.rho - ‖C.residual x‖) / C.rho) * (7 / 16) +
        (2 * (C.rho - ‖C.residual x‖) / C.rho) * (2 * C.rho) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hb (by norm_num)
      · exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans
          (mul_le_mul_of_nonneg_left (by linarith : 2 * ‖C.residual x‖ ≤ 2 * C.rho) ht)
    _ = _ := by field_simp [C.rho_pos.ne']; ring

/-- Distance to an outside point controls the remaining radius of the tube. -/
theorem radius_gap_le (x : C.tube) {y : E} (hy : y ∉ C.tube) :
    C.rho - ‖C.residual x‖ ≤ ‖(x : E) - y‖ := by
  have hy' : C.rho ≤ Metric.infDist y (Set.range C.curve) := by
    exact not_lt.mp hy
  have hdist : Metric.infDist y (Set.range C.curve) ≤
      Metric.infDist (x : E) (Set.range C.curve) + ‖(x : E) - y‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      (Metric.infDist_le_infDist_add_dist (x := y) (y := (x : E))
        (s := Set.range C.curve))
  rw [← C.residual_norm] at hdist
  linarith

theorem inside_outside_bound (x : C.tube) {y : E} (hy : y ∉ C.tube) :
    ‖D.inside x - y‖ ≤ (5 + 7 / (8 * C.rho)) * ‖(x : E) - y‖ := by
  have hρ := C.rho_pos
  have hc : 0 ≤ 7 / (8 * C.rho) + 4 := by positivity
  have heq : D.inside x - y = ((x : E) - y) + D.change x := by
    unfold inside
    abel
  calc
    ‖D.inside x - y‖ ≤ ‖(x : E) - y‖ + ‖D.change x‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ ≤ ‖(x : E) - y‖ +
        (7 / (8 * C.rho) + 4) * (C.rho - ‖C.residual x‖) :=
      add_le_add le_rfl (D.change_tail_bound x)
    _ ≤ ‖(x : E) - y‖ + (7 / (8 * C.rho) + 4) * ‖(x : E) - y‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (radius_gap_le (C := C) x hy) hc)
    _ = _ := by ring

theorem G_sub_self_bound (x : E) : ‖D.G x - x‖ ≤ 7 / 16 + 2 * C.rho := by
  by_cases hx : x ∈ C.tube
  · rw [D.G_of_mem ⟨x, hx⟩]
    simpa only [inside, add_sub_cancel_left] using D.change_uniform_bound ⟨x, hx⟩
  · rw [D.G_of_not_mem hx, sub_self, norm_zero]
    have := C.rho_pos
    positivity

/-- The distant-pair estimate uses only the bounded additive change. -/
theorem G_distant_bound (x y : E) (hxy : C.rho ≤ ‖x - y‖) :
    ‖D.G x - D.G y‖ ≤ (5 + 7 / (8 * C.rho)) * ‖x - y‖ := by
  have hρ := C.rho_pos
  have hc : 0 ≤ 7 / (8 * C.rho) + 4 := by positivity
  have hm := mul_le_mul_of_nonneg_left hxy hc
  have he : (7 / (8 * C.rho) + 4) * C.rho = 7 / 8 + 4 * C.rho := by
    field_simp [C.rho_pos.ne']
  rw [he] at hm
  have hdecomp : D.G x - D.G y = (x - y) + ((D.G x - x) - (D.G y - y)) := by abel
  calc
    ‖D.G x - D.G y‖ ≤ ‖x - y‖ + (‖D.G x - x‖ + ‖D.G y - y‖) := by
      rw [hdecomp]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ ‖x - y‖ + ((7 / 16 + 2 * C.rho) + (7 / 16 + 2 * C.rho)) :=
      add_le_add le_rfl (add_le_add (D.G_sub_self_bound x) (D.G_sub_self_bound y))
    _ ≤ (5 + 7 / (8 * C.rho)) * ‖x - y‖ := by nlinarith

/-- A finite positive constant valid for all pairs in the ambient Hilbert space. -/
def lipschitzConstant (_ : CorrectionData C) : ℝ :=
  max 1 (max (30 + 7 / (4 * C.rho) + 3808 * C.rho) (5 + 7 / (8 * C.rho)))

theorem lipschitzConstant_pos : 0 < D.lipschitzConstant :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem G_lipschitz (x y : E) :
    ‖D.G x - D.G y‖ ≤ D.lipschitzConstant * ‖x - y‖ := by
  have hlocal : 30 + 7 / (4 * C.rho) + 3808 * C.rho ≤ D.lipschitzConstant :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hfar : 5 + 7 / (8 * C.rho) ≤ D.lipschitzConstant :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hone : 1 ≤ D.lipschitzConstant := le_max_left _ _
  by_cases hxy : ‖x - y‖ < C.rho
  · by_cases hx : x ∈ C.tube
    · by_cases hy : y ∈ C.tube
      · rw [D.G_of_mem ⟨x, hx⟩, D.G_of_mem ⟨y, hy⟩]
        exact (D.inside_local_bound ⟨x, hx⟩ ⟨y, hy⟩ hxy).trans
          (mul_le_mul_of_nonneg_right hlocal (norm_nonneg _))
      · rw [D.G_of_mem ⟨x, hx⟩, D.G_of_not_mem hy]
        exact (D.inside_outside_bound ⟨x, hx⟩ hy).trans
          (mul_le_mul_of_nonneg_right hfar (norm_nonneg _))
    · by_cases hy : y ∈ C.tube
      · rw [D.G_of_not_mem hx, D.G_of_mem ⟨y, hy⟩, norm_sub_rev]
        have h := D.inside_outside_bound ⟨y, hy⟩ hx
        rw [norm_sub_rev y x] at h
        exact h.trans (mul_le_mul_of_nonneg_right hfar (norm_nonneg _))
      · rw [D.G_of_not_mem hx, D.G_of_not_mem hy]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (norm_nonneg (x - y))
  · exact (D.G_distant_bound x y (not_lt.mp hxy)).trans
      (mul_le_mul_of_nonneg_right hfar (norm_nonneg _))

end CorrectionData

end ThompsonNonamenability.Analytic

end

end OAI

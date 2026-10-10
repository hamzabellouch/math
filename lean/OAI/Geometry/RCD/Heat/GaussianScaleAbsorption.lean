import OAI.Geometry.RCD.Heat.GaussianOffDiagonal

namespace OAI

/-! # Uniform Gaussian bounds when heat time is shorter than a ball scale -/

open Set Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

/-- A fixed Gaussian absorbs every polynomial loss in the heat scale. -/
theorem exists_gaussian_polynomial_bound (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u : ℝ, 1 ≤ u → u ^ n * Real.exp (-c * u ^ 2) ≤ C := by
  have ht : Tendsto (fun u : ℝ => u ^ n * Real.exp (-c * u)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) c hc
  obtain ⟨b, hb⟩ := eventually_atTop.mp (ht.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  have hcont : Continuous (fun u : ℝ => u ^ n * Real.exp (-c * u)) := by fun_prop
  obtain ⟨d, hd⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max b 1))).bddAbove_image hcont.continuousOn
  refine ⟨max d 1, le_max_right _ _, ?_⟩
  intro u hu
  have hpoly : u ^ n * Real.exp (-c * u ^ 2) ≤ u ^ n * Real.exp (-c * u) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) n)
    apply Real.exp_le_exp.mpr
    have hs : u ≤ u ^ 2 := by nlinarith
    nlinarith
  apply hpoly.trans
  by_cases hub : u ≤ max b 1
  · exact (hd ⟨u, ⟨by linarith, hub⟩, rfl⟩).trans (le_max_left _ _)
  · have hbu : b ≤ u := le_trans (le_max_left _ _) (le_of_not_ge hub)
    exact (hb u hbu).trans (le_max_right _ _)

/-- At distance at least one ball radius, a shorter heat scale has a
uniform Gaussian envelope at that ball radius. -/
theorem exists_gaussian_scale_absorption (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u v : ℝ, 1 ≤ u → 1 ≤ v →
      u ^ n * Real.exp (-c * (u * v) ^ 2) ≤ C * Real.exp (-(c / 2) * v ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussian_polynomial_bound n (half_pos hc)
  refine ⟨C, hC, ?_⟩
  intro u v hu hv
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  have hp : 0 ≤ (u ^ 2 - 1) * (v ^ 2 - 1) := mul_nonneg (by linarith) (by linarith)
  have he : -c * (u * v) ^ 2 ≤ -(c / 2) * u ^ 2 + -(c / 2) * v ^ 2 := by
    have hsum : u ^ 2 + v ^ 2 ≤ 2 * u ^ 2 * v ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsum (half_pos hc).le
    nlinarith only [hm]
  calc
    _ ≤ u ^ n * Real.exp (-(c / 2) * u ^ 2 + -(c / 2) * v ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (pow_nonneg (by linarith) n)
    _ = (u ^ n * Real.exp (-(c / 2) * u ^ 2)) * Real.exp (-(c / 2) * v ^ 2) := by
      rw [Real.exp_add, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hb u hu) (Real.exp_pos _).le

/-- The Gaussian at a time below the ball scale is bounded by a fixed
multiple of the Gaussian at that ball scale, away from the ball. -/
theorem exists_gaussian_short_time_bound (n : ℕ) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r t d : ℝ, 0 < r → 0 < t → t ≤ r ^ 2 → r ≤ d →
      (Real.sqrt t)⁻¹ ^ n * Real.exp (-d ^ 2 / (D * t)) ≤
        C * r⁻¹ ^ n * Real.exp (-d ^ 2 / (2 * D * r ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussian_scale_absorption n (inv_pos.mpr hD)
  refine ⟨C, hC, ?_⟩
  intro r t d hr ht htr hrd
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq := Real.sq_sqrt ht.le
  let u := r / Real.sqrt t
  let v := d / r
  have hu : 1 ≤ u := (le_div_iff₀ hs).mpr (by nlinarith [Real.sqrt_nonneg t])
  have hv : 1 ≤ v := (le_div_iff₀ hr).mpr (by simpa using hrd)
  have h := mul_le_mul_of_nonneg_left (hb u v hu hv) (by positivity : 0 ≤ r⁻¹ ^ n)
  have he₁ : -D⁻¹ * (u * v) ^ 2 = -d ^ 2 / (D * t) := by
    dsimp only [u, v]
    field_simp
    nlinarith only [hsq]
  have he₂ : -(D⁻¹ / 2) * v ^ 2 = -d ^ 2 / (2 * D * r ^ 2) := by
    dsimp only [v]
    field_simp
  have hc : r⁻¹ ^ n * u ^ n = (Real.sqrt t)⁻¹ ^ n := by
    rw [← mul_pow]
    dsimp only [u]
    congr 1
    field_simp
  rw [he₁, he₂, ← mul_assoc, hc] at h
  simpa only [mul_assoc, mul_comm C] using h

end RegularPointCoordinates

end

end OAI

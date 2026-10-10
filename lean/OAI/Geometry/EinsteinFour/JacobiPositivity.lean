import OAI.Geometry.EinsteinFour.JacobiNearZero
import Mathlib.Analysis.Normed.Ring.Units

namespace OAI

/-! Positivity of Jacobi ratios close to the initial endpoint. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Topology

noncomputable section

/-- A single neighborhood controls every near-initial mesh ratio. The
inverse is applied to the position divided by time, which tends to one. -/
theorem near_identity_ratio_neighborhood
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ B V : R,
      ‖B - 1‖ < δ → ‖V - 1‖ < δ →
      IsUnit B ∧ ‖V * Ring.inverse B - 1‖ < 1 := by
  have hinv : ContinuousAt (Ring.inverse : R → R) (1 : R) := by
    simpa using (NormedRing.inverse_continuousAt (1 : Rˣ))
  have hc : ContinuousAt (fun z : R × R => z.2 * Ring.inverse z.1) (1, 1) :=
    continuousAt_snd.mul (hinv.comp_of_eq
      (continuousAt_fst : ContinuousAt (Prod.fst : R × R → R) (1, 1)) rfl)
  have hnear : ∀ᶠ z : R × R in 𝓝 (1, 1),
      IsUnit z.1 ∧ ‖z.2 * Ring.inverse z.1 - 1‖ < 1 := by
    have hi0 : {B : R | IsUnit B} ∈ 𝓝 (1 : R) := by
      simpa using (Units.nhds (1 : Rˣ))
    have hi : ∀ᶠ z : R × R in 𝓝 (1, 1), IsUnit z.1 :=
      (continuousAt_fst : ContinuousAt (Prod.fst : R × R → R) (1, 1)) hi0
    have hn : ∀ᶠ z : R × R in 𝓝 (1, 1), ‖z.2 * Ring.inverse z.1 - 1‖ < 1 := by
      have hc' : Tendsto (fun z : R × R => z.2 * Ring.inverse z.1)
          (𝓝 (1, 1)) (𝓝 (1 : R)) := by simpa using hc.tendsto
      filter_upwards [hc' (Metric.ball_mem_nhds (1 : R) zero_lt_one)] with z hz
      change dist (z.2 * Ring.inverse z.1) 1 < 1 at hz
      simpa only [dist_eq_norm] using hz
    exact hi.and hn
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ, hδ, fun B V hB hV => hball (y := (B, V)) ?_⟩
  rw [Prod.dist_eq]
  exact max_lt (by simpa only [dist_eq_norm] using hB)
    (by simpa only [dist_eq_norm] using hV)

/-- A positive multiple of a map within distance one of the identity can
be added to the identity without losing strict positivity. -/
theorem identity_add_ratio_quadratic_pos
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {P : F →L[ℝ] F} {r : ℝ} (hr : 0 ≤ r)
    (hP : ‖P - ContinuousLinearMap.id ℝ F‖ < 1)
    {x : F} (hx : x ≠ 0) :
    0 < inner ℝ ((ContinuousLinearMap.id ℝ F + r • P) x) x := by
  have hp : 0 < inner ℝ (P x) x := by
    apply quadratic_pos_of_norm_error (c := 1) ?_ hx
    simpa only [one_smul] using hP
  change 0 < inner ℝ (x + r • P x) x
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (mul_nonneg hr hp.le)

/-- Split the mesh into a neighborhood of zero and its complement. A
uniform coefficient bound suffices on the complement, while closeness to
the initial coefficient handles all of the first mesh nodes at once. -/
theorem mesh_ratio_quadratic_pos
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {P : F →L[ℝ] F} {h η K : ℝ} {i : ℕ}
    (hi : 0 < i) (hh : 0 < h) (hmesh : h * K < η)
    (hbound : ‖P‖ ≤ K)
    (hnear : (i : ℝ) * h ≤ η → ‖P - ContinuousLinearMap.id ℝ F‖ < 1)
    {x : F} (hx : x ≠ 0) :
    0 < inner ℝ ((ContinuousLinearMap.id ℝ F + ((1 : ℝ) / i) • P) x) x := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  by_cases ht : (i : ℝ) * h ≤ η
  · exact identity_add_ratio_quadratic_pos (by positivity) (hnear ht) hx
  · have hKi : K < (i : ℝ) := by nlinarith [lt_of_not_ge ht]
    apply quadratic_pos_of_norm_error (c := 1) ?_ hx
    simp only [one_smul, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hi')]
    calc
      (1 / (i : ℝ)) * ‖P‖ ≤ (1 / i) * K :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ < 1 := by rw [one_div_mul_eq_div]; exact (div_lt_one hi').mpr hKi

end

end PositiveEinsteinFour.Jacobi

end OAI

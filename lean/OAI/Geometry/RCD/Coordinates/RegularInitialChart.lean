import OAI.Geometry.RCD.Coordinates.RegularOpenCoordinates

namespace OAI

/-! # The actual harmonic coordinates give an initial open chart -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- The metric error in normalized coordinates, returned to physical units. -/
theorem normalized_pair_error {X E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → E) (N : E ≃L[ℝ] E) {x z : X} {r epsilon : ℝ} (hr : 0 < r)
    (hg : IsPointedApproximation x 0 r 4 epsilon
      (fun y => r⁻¹ • N (f y - f x))) (hz : dist z x ≤ 4 * r) :
    |‖N (f z - f x)‖ - dist x z| ≤ epsilon * r := by
  have h := hg.2.1 z x hz (by simp only [dist_self]; positivity)
  have hzero : r⁻¹ • N (f x - f x) = (0 : E) := by simp
  dsimp only at h
  rw [hzero, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at h
  have he : r⁻¹ * ‖N (f z - f x)‖ - dist z x / r =
      (‖N (f z - f x)‖ - dist z x) / r := by ring
  rw [he, abs_div, abs_of_pos hr] at h
  simpa only [dist_comm x z] using (div_le_iff₀ hr).mp h

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The existing harmonic map is a homeomorphism onto an open image on a
fixed smaller neighborhood. Exact preimages come from the quarter-scale
correction construction. -/
theorem regular_initial_chart {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : 0 ≤ zeta) (hzetaSmall : zeta ≤ 1 / 2048)
    (hgramSmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 4 : ℝ) ^ n)⁻¹) * zeta) ≤ 3 / 4) :
    let Ω := ball base (e.heat.radius / 1024)
    IsOpen (Set.range (fun x : Ω => e.heat.values x)) ∧
      ∃ chart : Ω ≃ₜ Set.range (fun x : Ω => e.heat.values x),
        ∀ x, (chart x).val = e.heat.values x := by
  intro Ω
  let d := regular_open_coordinate_data hX e hzeta hzetaSmall hgramSmall
  have hr : 0 < e.heat.radius / 128 := div_pos e.heat.radius_pos (by norm_num)
  have hcont : ContinuousOn e.heat.values Ω := e.heat.splitting.continuous.mono (by
    intro x hx
    apply ball_subset_ball _ hx
    linarith [e.heat.radius_pos])
  apply open_homeomorph_of_normalized_separation d hr (by positivity) isOpen_ball hcont
  intro x hx z hz hne
  have hx' : x ∈ ball base (e.heat.radius / 32) :=
    ball_subset_ball (by linarith [e.heat.radius_pos]) hx
  have ht : 0 < dist x z := dist_pos.mpr hne
  have hdiam : dist x z ≤ e.heat.radius / 128 := by
    have hxv : dist x base < e.heat.radius / 1024 := hx
    have hzv : dist z base < e.heat.radius / 1024 := hz
    have hh := dist_triangle x base z
    rw [dist_comm base z] at hh
    linarith [e.heat.radius_pos]
  obtain ⟨i, hi, hi'⟩ := exists_nat_pow_near_of_lt_one
    (div_pos ht hr) ((div_le_one hr).mpr hdiam)
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
  let r := coordinateQuarterRadius (e.heat.radius / 128) i
  have hr' : 0 < r := mul_pos hr (pow_pos (by norm_num) i)
  have htr : dist x z ≤ r := by
    simpa only [r, coordinateQuarterRadius, mul_comm] using (div_le_iff₀ hr).mp hi'
  have hrt : r < 4 * dist x z := by
    rw [pow_succ] at hi
    have hh := (lt_div_iff₀ hr).mp hi
    dsimp only [r, coordinateQuarterRadius]
    nlinarith
  have hframe : d.normalization i x = coordinateFrame (e.heat.frameAt x hx' (2 * i)) := by
    change e.heat.quarterFrame i x = _
    exact e.heat.quarterFrame_eq i x hx'
  have happ : IsPointedApproximation x 0 r 4 zeta
      (fun y => r⁻¹ • d.normalization i x (e.heat.values y - e.heat.values x)) := by
    rw [hframe]
    have h := e.heat.frameAt_approximation x hx' (2 * i)
    simpa only [r, regular_quarter_radius, coordinateFrame_apply, map_sub] using h
  have he := normalized_pair_error e.heat.values (d.normalization i x) hr' happ
    (by rw [dist_comm]; linarith)
  refine ⟨i, he.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right hzetaSmall hr'.le
  nlinarith

end RegularPointCoordinates

end

end OAI

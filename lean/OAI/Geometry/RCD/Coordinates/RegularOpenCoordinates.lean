import OAI.Geometry.RCD.Coordinates.RegularFrameGeometry
import OAI.Geometry.RCD.Coordinates.OpenCoordinates

namespace OAI

/-! # Constructive openness of the actual harmonic coordinates -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- A centered four-ball approximation restricts to the unit ball when
the error is at most half the new tolerance. -/
theorem pointed_approximation_restrict_four {X E : Type*}
    [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : X} {r epsilon : ℝ} {g : X → E} (hr : 0 < r)
    (hepsilon : epsilon ≤ 1 / 2048) (hzero : g x = 0)
    (hg : IsPointedApproximation x 0 r 4 epsilon g) :
    IsPointedApproximation x 0 r 1 (1 / 1024) g := by
  have he0 : 0 ≤ epsilon := (dist_nonneg (x := g x) (y := 0)).trans hg.1
  refine ⟨by rw [hzero, dist_self]; norm_num, ?_, ?_⟩
  · intro y z hy hz
    exact (hg.2.1 y z (by linarith) (by linarith)).trans (by linarith)
  · intro v hv
    obtain ⟨y, hy, hyv⟩ := hg.2.2 v (by linarith)
    have hmetric := hg.2.1 y x hy (by simp only [dist_self]; positivity)
    rw [hzero, dist_zero_right] at hmetric
    have ht : ‖g y‖ ≤ dist (g y) v + ‖v‖ := by
      simpa only [sub_add_cancel, ← dist_eq_norm] using norm_add_le (g y - v) v
    rw [dist_zero_right] at hv
    have hb : dist y x / r ≤ 1 := by linarith [(abs_le.mp hmetric).1]
    exact ⟨y, by simpa only [one_mul] using (div_le_one hr).mp hb, hyv.trans (by linarith)⟩

theorem regular_quarter_radius (R : ℝ) (i : ℕ) :
    coordinateQuarterRadius (R / 128) i = (R / (2 : ℝ) ^ (2 * i)) / 128 := by
  simp only [coordinateQuarterRadius, pow_mul]
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num,
    show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]
  ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)

/-- Quarter-scale pointwise coordinate changes, extended outside the working
neighborhood only to give the total function required by the open-map API. -/
def quarterFrame (i : ℕ) (q : X) : Euclidean n ≃L[ℝ] Euclidean n := by
  classical
  exact if hq : q ∈ ball base (d.radius / 32) then coordinateFrame (d.frameAt q hq (2 * i))
  else ContinuousLinearEquiv.refl ℝ (Euclidean n)

theorem quarterFrame_eq (i : ℕ) (q : X) (hq : q ∈ ball base (d.radius / 32)) :
    d.quarterFrame i q = coordinateFrame (d.frameAt q hq (2 * i)) := by
  simp only [quarterFrame, dite_eq_left hq]

end RegularBilinearData

/-- The actual regular-neighborhood harmonic coordinates satisfy every
hypothesis of the constructive open-map argument. -/
def regular_open_coordinate_data {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : 0 ≤ zeta) (hzetaSmall : zeta ≤ 1 / 2048)
    (hgramSmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 4 : ℝ) ^ n)⁻¹) * zeta) ≤ 3 / 4) :
    OpenCoordinateData (ball base (e.heat.radius / 1024)) e.heat.values
      (e.heat.radius / 128) (2 * (n : ℝ)) := by
  have hinside {q : X} (hq : q ∈ ball base (e.heat.radius / 1024)) :
      q ∈ ball base (e.heat.radius / 32) := by
    apply ball_subset_ball _ hq
    linarith [e.heat.radius_pos]
  refine OpenCoordinateData.of_pointed_approximation (div_pos e.heat.radius_pos (by norm_num))
    e.heat.quarterFrame ?_ ?_ ?_
  · intro i q hq _hball
    let r := (e.heat.radius / (2 : ℝ) ^ (2 * i)) / 128
    have hr : 0 < r := div_pos (div_pos e.heat.radius_pos (by positivity)) (by norm_num)
    have heq := regular_quarter_radius e.heat.radius i
    let N := e.heat.quarterFrame i q
    let g := fun x => r⁻¹ • N (e.heat.values x - e.heat.values q)
    refine ⟨g, ?_, ?_⟩
    · rw [heq]
      apply pointed_approximation_restrict_four hr hzetaSmall (by simp only [g, sub_self, map_zero, smul_zero])
      have h := e.heat.frameAt_approximation q (hinside hq) (2 * i)
      simpa only [g, N, RegularBilinearData.quarterFrame_eq e.heat i q (hinside hq),
        coordinateFrame_apply, map_sub] using h
    · intro y _hy
      rw [heq]
      change ‖r⁻¹ • N (e.heat.values y - e.heat.values q) -
        r⁻¹ • N (e.heat.values y - e.heat.values q)‖ ≤ 1 / 1024
      simp only [sub_self, norm_zero]
      norm_num
  · intro i x y hx hy hdist w
    rw [regular_quarter_radius] at hdist
    rw [e.heat.quarterFrame_eq i x (hinside hx),
      e.heat.quarterFrame_eq (i + 1) y (hinside hy)]
    apply coordinateFrame_le_of_mean_comparison (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
      (ball x (e.heat.radius / 2 ^ (2 * i)))
      (ball y (e.heat.radius / 2 ^ (2 * (i + 1)))) measurableSet_ball measurableSet_ball
      (e.heat.frameAt x (hinside hx) (2 * i))
      (e.heat.frameAt y (hinside hy) (2 * (i + 1)))
      (e.heat.frameAt_exact x (hinside hx) (2 * i))
      (e.heat.frameAt_exact y (hinside hy) (2 * (i + 1))) ?_ w
    intro v
    have hr : 0 < e.heat.radius / (2 : ℝ) ^ (2 * i) := div_pos e.heat.radius_pos (by positivity)
    have hroom : dist y x + (1 / 4 : ℝ) * (e.heat.radius / (2 : ℝ) ^ (2 * i)) ≤
        e.heat.radius / (2 : ℝ) ^ (2 * i) := by linarith
    have hb := (regular_subball_mean_comparison hX e (hinside hx) (hinside hy) hzeta
      (2 * i) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) hroom v).1
    have heq : (1 / 4 : ℝ) * (e.heat.radius / (2 : ℝ) ^ (2 * i)) =
        e.heat.radius / (2 : ℝ) ^ (2 * (i + 1)) := by
      rw [show 2 * (i + 1) = 2 * i + 2 by omega, pow_add]
      norm_num
      ring
    rw [heq] at hb
    have hnonneg := (sobolevMeanGram_isPositive (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
      (ball x (e.heat.radius / 2 ^ (2 * i))) measurableSet_ball).inner_nonneg_right v
    nlinarith [mul_le_mul_of_nonneg_right hgramSmall hnonneg]
  · intro i q hq w
    rw [e.heat.quarterFrame_eq i q (hinside hq)]
    exact e.heat.coordinateFrame_lower q (hinside hq) (2 * i) w

end RegularPointCoordinates

end

end OAI

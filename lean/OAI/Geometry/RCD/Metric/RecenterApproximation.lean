import OAI.Geometry.RCD.Metric.ExtraFactorObstruction

namespace OAI

/-!
# Centering an unpointed Euclidean ball approximation

The image of the center is forced to be small by the eccentricity of a
Euclidean ball. Translation therefore turns an ordinary ball approximation
into a pointed approximation with an explicit error loss.
-/

open Metric

noncomputable section

namespace RegularPointCoordinates

theorem ballApproximation_center_norm_le {X : Type*} [MetricSpace X] {n : ℕ}
    {p : X} {r R ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hεR : ε < R)
    {f : X → Euclidean n} (hf : IsBallApproximation p 0 r R ε f) : ‖f p‖ ≤ 3 * ε := by
  by_cases hp : f p = 0
  · simp only [hp, norm_zero]
    positivity
  have hp0 : 0 < ‖f p‖ := norm_pos_iff.mpr hp
  let t := (R - ε) / ‖f p‖
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hεR.le) hp0.le
  let y := -(t • f p)
  have hy : dist y 0 = R - ε := by
    dsimp only [y]
    rw [dist_zero_right, norm_neg, norm_smul, Real.norm_of_nonneg ht]
    dsimp only [t]
    field_simp
  obtain ⟨x, hx, hxy⟩ := hf.2 y hy.le
  have hR : 0 < R := hε.trans_lt hεR
  have hpp : dist p p ≤ R * r := by simp only [dist_self]; exact mul_nonneg hR.le hr.le
  have hd := (abs_le.mp (hf.1 p x hpp hx)).2
  have hquot : dist p x / r ≤ R := by
    rw [dist_comm]
    exact (div_le_iff₀ hr).mpr hx
  have hpy : dist (f p) y = ‖f p‖ + R - ε := by
    have hv : f p - y = (1 + t) • f p := by dsimp only [y]; module
    rw [dist_eq_norm, hv, norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 + t)]
    dsimp only [t]
    field_simp
    ring
  have htri := dist_triangle (f p) (f x) y
  rw [hpy] at htri
  linarith

/-- Centering loses only a factor four in the approximation error. -/
theorem IsBallApproximation.recenter {X : Type*} [MetricSpace X] {n : ℕ}
    {p : X} {r R ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hεR : ε < R)
    {f : X → Euclidean n} (hf : IsBallApproximation p 0 r R ε f) :
    IsPointedApproximation p 0 r R (4 * ε) (fun x => f x - f p) := by
  have hcenter := ballApproximation_center_norm_le hr hε hεR hf
  refine ⟨by simp only [sub_self, dist_self]; positivity, ?_, ?_⟩
  · intro x y hx hy
    have hd : dist (f x - f p) (f y - f p) = dist (f x) (f y) := dist_sub_right _ _ _
    rw [hd]
    exact (hf.1 x y hx hy).trans (by linarith)
  · intro y hy
    have hz : dist (y + f p) 0 ≤ R - ε := by
      rw [dist_zero_right]
      have hyn : ‖y‖ ≤ R - 4 * ε := by simpa only [dist_zero_right] using hy
      exact (norm_add_le y (f p)).trans (by linarith)
    obtain ⟨x, hx, hxy⟩ := hf.2 (y + f p) hz
    refine ⟨x, hx, ?_⟩
    have hd : dist (f x - f p) y = dist (f x) (y + f p) := by
      simp only [dist_eq_norm]
      congr 1
      module
    rw [hd]
    exact hxy.trans (by linarith)

/-- The half-ball conclusion at scale 4r is a radius-two conclusion at
scale r. This fixed rescaling is used after volume almost rigidity. -/
theorem IsPointedApproximation.rescale_four {X : Type*} [MetricSpace X] {n : ℕ}
    {p : X} {r ε : ℝ} (hr : 0 < r) {f : X → Euclidean n}
    (hf : IsPointedApproximation p 0 (4 * r) (1 / 2) ε f) :
    IsPointedApproximation p 0 r 2 (4 * ε) (fun x => (4 : ℝ) • f x) := by
  have hdist (v w : Euclidean n) : dist ((4 : ℝ) • v) ((4 : ℝ) • w) = 4 * dist v w := by
    rw [dist_smul₀]
    norm_num
  have hrad : (1 / 2 : ℝ) * (4 * r) = 2 * r := by ring
  refine ⟨?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hf.1 (by norm_num : (0 : ℝ) ≤ 4)
    simpa only [← hdist, smul_zero] using h
  · intro x y hx hy
    have h := mul_le_mul_of_nonneg_left (hf.2.1 x y (by rwa [hrad]) (by rwa [hrad]))
      (by norm_num : (0 : ℝ) ≤ 4)
    have h' : |(4 : ℝ) * (dist (f x) (f y) - dist x y / (4 * r))| ≤ 4 * ε := by
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using h
    have he : (4 : ℝ) * (dist (f x) (f y) - dist x y / (4 * r)) =
        dist ((4 : ℝ) • f x) ((4 : ℝ) • f y) - dist x y / r := by
      rw [hdist]
      field_simp
    rwa [he] at h'
  · intro y hy
    have hy' : dist ((1 / 4 : ℝ) • y) 0 ≤ 1 / 2 - ε := by
      rw [dist_zero_right, norm_smul]
      norm_num
      have h := hy
      rw [dist_zero_right] at h
      linarith
    obtain ⟨x, hx, hxy⟩ := hf.2.2 ((1 / 4 : ℝ) • y) hy'
    refine ⟨x, by rwa [hrad] at hx, ?_⟩
    have h := mul_le_mul_of_nonneg_left hxy (by norm_num : (0 : ℝ) ≤ 4)
    rw [← hdist, smul_smul] at h
    norm_num at h
    exact h

end RegularPointCoordinates

end

end OAI

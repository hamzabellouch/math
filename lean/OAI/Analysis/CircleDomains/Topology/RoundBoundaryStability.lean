import OAI.Analysis.CircleDomains.Topology.RoundDiskDistance
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! Quantitative persistence of the fixed-source boundary integral under
uniform changes of the map and center-radius changes of the target disk. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem infDist_closedBall_eq_max (c z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    infDist z (closedBall c r) = max (dist z c - r) 0 := by
  by_cases hz : dist z c ≤ r
  · rw [infDist_zero_of_mem (mem_closedBall.mpr hz), max_eq_right (sub_nonpos.mpr hz)]
  · rw [infDist_closedBall_of_dist_gt c z hr (lt_of_not_ge hz),
      max_eq_left (sub_nonneg.mpr (le_of_not_ge hz))]

 theorem round_disk_distance_change (c d z w : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |infDist z (closedBall c r) - infDist w (closedBall d s)| ≤
      dist z w + dist c d + |r - s| := by
  rw [infDist_closedBall_eq_max c z hr, infDist_closedBall_eq_max d w hs]
  calc
    _ ≤ max |(dist z c - r) - (dist w d - s)| |(0 : ℝ) - 0| :=
      abs_max_sub_max_le_max _ _ _ _
    _ = |(dist z c - dist w d) - (r - s)| := by
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      congr 1
      ring
    _ ≤ |dist z c - dist w d| + |r - s| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (dist z c - dist w d) (-(r - s))
    _ ≤ dist z w + dist c d + |r - s| := by
      exact add_le_add (by simpa only [Real.dist_eq] using dist_dist_dist_le z c w d) le_rfl

 def roundDiskBoundaryPairing (f : ℝ → ℂ) (c : ℂ) (r : ℝ) (v : ℝ → ℝ) : ℝ :=
   ∫ t in (0 : ℝ)..1, infDist (f t) (closedBall c r) * deriv v t

 theorem roundDiskBoundaryPairing_stability
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (c d : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {e M : ℝ} (he : 0 ≤ e)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, dist (f t) (g t) ≤ e)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, |deriv v t| ≤ M) :
    |roundDiskBoundaryPairing f c r v - roundDiskBoundaryPairing g d s v| ≤
      (e + dist c d + |r - s|) * M := by
  have hdv : Continuous (deriv v) := hv.continuous_deriv (by simp)
  have hfi : IntervalIntegrable (fun t => infDist (f t) (closedBall c r) * deriv v t) volume 0 1 := ((continuous_infDist_pt _).comp hf).mul hdv |>.intervalIntegrable 0 1
  have hgi : IntervalIntegrable (fun t => infDist (g t) (closedBall d s) * deriv v t) volume 0 1 := ((continuous_infDist_pt _).comp hg).mul hdv |>.intervalIntegrable 0 1
  unfold roundDiskBoundaryPairing
  rw [← intervalIntegral.integral_sub hfi hgi]
  have hb : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖infDist (f t) (closedBall c r) * deriv v t -
        infDist (g t) (closedBall d s) * deriv v t‖ ≤
      (e + dist c d + |r - s|) * M := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hweight := (round_disk_distance_change c d (f t) (g t) hr hs).trans
      (add_le_add (add_le_add (hclose t ht') le_rfl) le_rfl)
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right hweight (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hderiv t ht') (by positivity))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun t ht => hb t (by simpa only [uIoc_of_le zero_le_one] using ht))

 theorem tendsto_roundDiskBoundaryPairing
    (f : ℕ → ℝ → ℂ) (f₀ : ℝ → ℂ) (hf : ∀ n, Continuous (f n)) (hf₀ : Continuous f₀)
    (c : ℕ → ℂ) (c₀ : ℂ) (hc : Tendsto c atTop (𝓝 c₀))
    (r : ℕ → ℝ) {r₀ : ℝ} (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hrr : Tendsto r atTop (𝓝 r₀))
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0))
    (hclose : ∀ n, ∀ t ∈ Icc (0 : ℝ) 1, dist (f n t) (f₀ t) ≤ e n) :
    Tendsto (fun n => roundDiskBoundaryPairing (f n) (c n) (r n) v) atTop
      (𝓝 (roundDiskBoundaryPairing f₀ c₀ r₀ v)) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (hv.continuous_deriv (by simp)).continuousOn
  have hd (n : ℕ) : dist (roundDiskBoundaryPairing (f n) (c n) (r n) v)
      (roundDiskBoundaryPairing f₀ c₀ r₀ v) ≤ (e n + dist (c n) c₀ + |r n - r₀|) * M := by
    simpa only [Real.dist_eq] using roundDiskBoundaryPairing_stability (f n) f₀ (hf n) hf₀
      (c n) c₀ (hr n) hr₀ v hv (he n) (hclose n)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hM t ht)
  have ht : Tendsto (fun n => (e n + dist (c n) c₀ + |r n - r₀|) * M) atTop (𝓝 0) := by
    simpa only [dist_self, sub_self, abs_zero, add_zero, zero_add, zero_mul] using
      ((he0.add (hc.dist (tendsto_const_nhds (x := c₀)))).add (hrr.sub (tendsto_const_nhds (x := r₀))).abs).mul_const M
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) hd ht)

end CircleDomainRigidity

end

end OAI

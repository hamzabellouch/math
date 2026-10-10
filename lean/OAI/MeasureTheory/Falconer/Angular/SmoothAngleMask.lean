import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

noncomputable def angleBump (η : ℝ) (hη : 0 < η) : ContDiffBump (0:ℝ) :=
  ⟨η/2,η,half_pos hη,half_lt_self hη⟩

noncomputable def thickenedIndicator (G : Set ℝ) (η : ℝ) : ℝ → ℝ :=
  (thickening (2*η) G).indicator (fun _ => 1)

noncomputable def smoothAngleMask (G : Set ℝ) (η : ℝ) (hη : 0 < η) : ℝ → ℝ :=
  (angleBump η hη).normed volume ⋆[lsmul ℝ ℝ,volume] thickenedIndicator G η

theorem thickenedIndicator_bounds (G : Set ℝ) (η x : ℝ) :
    0 ≤ thickenedIndicator G η x ∧ thickenedIndicator G η x ≤ 1 := by
  classical
  by_cases h : x ∈ thickening (2*η) G <;> simp [thickenedIndicator,h]

theorem thickenedIndicator_locallyIntegrable (G : Set ℝ) (η : ℝ) :
    LocallyIntegrable (thickenedIndicator G η) volume :=
  (continuous_const.locallyIntegrable (μ := volume)).indicator isOpen_thickening.measurableSet

theorem smoothAngleMask_contDiff (G : Set ℝ) (η : ℝ) (hη : 0 < η) :
    ContDiff ℝ ∞ (smoothAngleMask G η hη) :=
  (angleBump η hη).hasCompactSupport_normed.contDiff_convolution_left _
    (angleBump η hη).contDiff_normed (thickenedIndicator_locallyIntegrable G η)

theorem smoothAngleMask_bounds (G : Set ℝ) (η : ℝ) (hη : 0 < η) (x : ℝ) :
    0 ≤ smoothAngleMask G η hη x ∧ smoothAngleMask G η hη x ≤ 1 := by
  have hp := (angleBump η hη).nonneg_normed (μ := volume)
  constructor
  · apply integral_nonneg
    intro t
    exact mul_nonneg (hp t) (thickenedIndicator_bounds G η (x-t)).1
  · have he : (((angleBump η hη).normed volume) ⋆[lsmul ℝ ℝ,volume] (fun _ : ℝ => (1:ℝ))) x = 1 :=
      (angleBump η hη).normed_convolution_eq_right (fun _ _ => rfl)
    rw [← he]
    apply convolution_mono_right_of_nonneg _ hp (fun t => (thickenedIndicator_bounds G η t).2) (fun _ => zero_le_one)
    simpa only [ConvolutionExistsAt,lsmul_apply,smul_eq_mul,mul_one] using
      (angleBump η hη).integrable_normed (μ := volume)

theorem smoothAngleMask_eq_one (G : Set ℝ) (η : ℝ) (hη : 0 < η) {x : ℝ} (hx : x ∈ G) :
    smoothAngleMask G η hη x = 1 := by
  have hi : thickenedIndicator G η x = 1 := by
    apply Set.indicator_of_mem
    exact mem_thickening_iff.mpr ⟨x,hx,by simpa using mul_pos (by norm_num : (0:ℝ)<2) hη⟩
  rw [smoothAngleMask,← hi]
  apply ContDiffBump.normed_convolution_eq_right
  intro y hy
  rw [hi]
  apply Set.indicator_of_mem
  apply mem_thickening_iff.mpr
  refine ⟨x,hx,?_⟩
  change dist y x < η at hy
  linarith

theorem smoothAngleMask_support (G : Set ℝ) (η : ℝ) (hη : 0 < η) :
    Function.support (smoothAngleMask G η hη) ⊆ thickening (3*η) G := by
  intro x hx
  obtain ⟨a,ha,b,hb,hab⟩ := support_convolution_subset (lsmul ℝ ℝ) hx
  rw [(angleBump η hη).support_normed_eq] at ha
  have hb' : b ∈ thickening (2*η) G := by
    by_contra hn
    exact hb (Set.indicator_of_notMem hn (fun _ : ℝ => (1:ℝ)))
  obtain ⟨z,hz,hbz⟩ := mem_thickening_iff.mp hb'
  apply mem_thickening_iff.mpr
  refine ⟨z,hz,?_⟩
  change dist a 0 < η at ha
  rw [← hab]
  have he : dist (a+b) b = dist a 0 := by simp [dist_eq_norm]
  have hd := dist_triangle (a+b) b z
  rw [he] at hd
  linarith

theorem smoothAngleMask_tsupport (G : Set ℝ) (η : ℝ) (hη : 0 < η) :
    tsupport (smoothAngleMask G η hη) ⊆ thickening (4*η) G := by
  exact (closure_mono (smoothAngleMask_support G η hη)).trans
    ((closure_thickening_subset_cthickening (3*η) G).trans
      (cthickening_subset_thickening' (by positivity) (by linarith) G))

end PlanarFalconer

end OAI

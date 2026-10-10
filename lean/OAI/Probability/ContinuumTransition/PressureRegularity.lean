import OAI.Probability.ContinuumTransition.PressureDuality

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem convexOn_physicalPressure {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ConvexOn ℝ pressureDomain (physicalPressure φ t) := by
  have hcD : Convex ℝ pressureDomain :=
    (convexOn_log_grandPartition hφ (by norm_num : (0 : ℝ) < 1) hstable t).1
  refine ⟨hcD, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hcD hx hy ha hb hab
  have hl := physicalPressure_tendsto hφ ht (le_of_lt hz) hstable hcore (h := (a • x+b • y).2)
  have hr := ((physicalPressure_tendsto hφ ht (le_of_lt hx) hstable hcore (h := x.2)).const_mul a).add
    ((physicalPressure_tendsto hφ ht (le_of_lt hy) hstable hcore (h := y.2)).const_mul b)
  simp only [smul_eq_mul]
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hh := (convexOn_log_grandPartition hφ hL hstable t).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh
  have hV : 0 ≤ t*L^3 := mul_nonneg (by linarith) (pow_pos hL 3).le
  have hbound := div_le_div_of_nonneg_right hh hV
  simpa only [add_div, mul_div_assoc] using hbound

theorem isOpen_pressureDomain : IsOpen pressureDomain :=
  isOpen_lt continuous_const continuous_fst

theorem continuousOn_physicalPressure {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ContinuousOn (physicalPressure φ t) pressureDomain :=
  (convexOn_physicalPressure hφ ht hstable hcore).continuousOn isOpen_pressureDomain

theorem monotone_physicalPressure {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B β : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Monotone (fun h => physicalPressure φ t (β,h)) := by
  intro h k hhk
  have ht0 : 0 < t := by linarith
  apply div_le_div_of_nonneg_right _ ht0.le
  unfold canonicalPressure
  apply csSup_le (s := (fun d : ℝ => t*h*d-canonicalDensity φ β d) '' Ici 0)
    ⟨t*h*0-canonicalDensity φ β 0, ⟨0, by simp, rfl⟩⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := t*k))
    (mem_image_of_mem (fun d : ℝ => t*k*d-canonicalDensity φ β d) hd)
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhk ht0.le) hd
  exact (sub_le_sub_right hmul _).trans hh

theorem concaveOn_physicalCanonical {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B d : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    ConcaveOn ℝ (Ioi 0) (fun β => physicalCanonical φ t β d) := by
  have hh := ConcaveOn.smul (show 0 ≤ t⁻¹ by positivity)
    (concaveOn_canonicalDensity hφ ht hstable hcore hd)
  simpa only [physicalCanonical, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh

end ContinuumTemperature
end

end OAI

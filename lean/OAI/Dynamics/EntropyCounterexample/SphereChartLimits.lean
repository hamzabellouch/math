import OAI.Dynamics.EntropyCounterexample.SphereCharts
import OAI.Dynamics.EntropyCounterexample.SphereMainUpdate

namespace OAI

noncomputable section

open Filter Topology
open scoped OnePoint

namespace Problem340.SphereChartLimits

theorem north_eq : chartNorthPole = SphereDoubling.north := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [chartNorthPole, chartNorthVector, SphereDoubling.north]

theorem chart_sphereOfComplex (z : ℂ) :
    SphereTranslation.chart (sphereOfComplex z).1 = z := by
  have hd : ‖z‖ ^ 2 + 1 ≠ 0 := by positivity
  have hden : 1 - (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1) = 2 / (‖z‖ ^ 2 + 1) := by
    field_simp
    ring
  apply Complex.ext
  · change (sphereOfComplex z).1 0 / (1 - (sphereOfComplex z).1 2) = z.re
    rw [sphereOfComplex_val_zero, sphereOfComplex_val_two, hden]
    field_simp
  · change (sphereOfComplex z).1 1 / (1 - (sphereOfComplex z).1 2) = z.im
    rw [sphereOfComplex_val_one, sphereOfComplex_val_two, hden]
    field_simp

theorem sphereToComplex_eq_chart {x : StandardSphere2} (hx : x ≠ chartNorthPole) :
    sphereToComplex x = SphereTranslation.chart x.1 := by
  calc
    sphereToComplex x = SphereTranslation.chart (sphereOfComplex (sphereToComplex x)).1 :=
      (chart_sphereOfComplex _).symm
    _ = SphereTranslation.chart x.1 := by rw [sphereOfComplex_sphereToComplex hx]

theorem sphereOfComplex_chart {x : StandardSphere2} (hx : x ≠ chartNorthPole) :
    sphereOfComplex (SphereTranslation.chart x.1) = x := by
  rw [← sphereToComplex_eq_chart hx]
  exact sphereOfComplex_sphereToComplex hx

theorem update_sphereOfComplex (c z : ℂ) :
    SphereMainUpdate.update c (sphereOfComplex z) = sphereOfComplex (z ^ 2 + c) := by
  have hz : sphereOfComplex z ≠ SphereDoubling.north := by
    simpa only [north_eq] using sphereOfComplex_ne_north z
  have hu : SphereMainUpdate.update c (sphereOfComplex z) ≠ chartNorthPole := by
    rw [north_eq]
    exact SphereMainUpdate.update_ne_north c _ hz
  rw [← sphereOfComplex_chart hu, SphereMainUpdate.chart_update c _ hz,
    chart_sphereOfComplex]

theorem tendsto_sphereOfComplex_north {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) :
    Tendsto (fun a => sphereOfComplex (z a)) l (𝓝 chartNorthPole) := by
  have hz' : Tendsto z l (coclosedCompact ℂ) := by
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.mp hz
  have hcoe : Tendsto (fun a => (z a : OnePoint ℂ)) l (𝓝 (∞ : OnePoint ℂ)) :=
    OnePoint.tendsto_coe_infty.comp hz'
  simpa only [Function.comp_apply, complexSphereHomeomorph_coe,
    complexSphereHomeomorph_infty] using!
    (complexSphereHomeomorph.continuous.tendsto (∞ : OnePoint ℂ)).comp hcoe

theorem tendsto_north_of_chart_norm {α : Type*} {l : Filter α} {x : α → StandardSphere2}
    (hx : ∀ a, x a ≠ SphereDoubling.north)
    (hz : Tendsto (fun a => ‖SphereTranslation.chart (x a).1‖) l atTop) :
    Tendsto x l (𝓝 SphereDoubling.north) := by
  have hx' : ∀ a, x a ≠ chartNorthPole := by simpa only [north_eq] using hx
  have heq : (fun a => sphereOfComplex (SphereTranslation.chart (x a).1)) = x := by
    funext a
    rw [← sphereToComplex_eq_chart (hx' a), sphereOfComplex_sphereToComplex (hx' a)]
  simpa only [heq, north_eq] using tendsto_sphereOfComplex_north hz

theorem tendsto_sphereOfComplex {α : Type*} {l : Filter α} {z : α → ℂ} {w : ℂ}
    (hz : Tendsto z l (𝓝 w)) :
    Tendsto (fun a => sphereOfComplex (z a)) l (𝓝 (sphereOfComplex w)) :=
  (continuous_sphereOfComplex.tendsto w).comp hz

theorem zero_eq_south : sphereOfComplex 0 = SphereDoubling.south := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [SphereDoubling.south]

theorem tendsto_south_of_chart_zero {α : Type*} {l : Filter α} {x : α → StandardSphere2}
    (hx : ∀ a, x a ≠ SphereDoubling.north)
    (hz : Tendsto (fun a => SphereTranslation.chart (x a).1) l (𝓝 0)) :
    Tendsto x l (𝓝 SphereDoubling.south) := by
  have hx' : ∀ a, x a ≠ chartNorthPole := by simpa only [north_eq] using hx
  have heq : (fun a => sphereOfComplex (SphereTranslation.chart (x a).1)) = x := by
    funext a
    rw [← sphereToComplex_eq_chart (hx' a), sphereOfComplex_sphereToComplex (hx' a)]
  simpa only [heq, zero_eq_south] using tendsto_sphereOfComplex hz

end Problem340.SphereChartLimits

end

end OAI

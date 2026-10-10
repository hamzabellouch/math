import OAI.MeasureTheory.Falconer.Graphs.GraphCoordinateInverse
import OAI.MeasureTheory.Falconer.Radial.RadialDensity

namespace OAI

namespace PlanarFalconer
open Set

theorem graphB_parameter_injective {ξ : Plane} (hξ : ξ ≠ 0) :
    Function.Injective (fun z : ℝ => graphB z ξ) := by
  intro z w he
  have hh := congrArg (fun v : Plane => (2:ℝ) • v) he
  simp only [graphB, smul_smul] at hh
  norm_num at hh
  have hq : quarterTurn ξ ≠ 0 := by
    rw [← norm_ne_zero_iff, graph_quarterTurn_norm]
    exact norm_ne_zero_iff.mpr hξ
  exact (smul_left_injective ℝ hq) hh

theorem circle_sign_norm (s : ℝ) (hs : s = 1 ∨ s = -1) (ω : UnitCircle) :
    ‖s • (ω:Plane)‖ = 1 := by
  rcases hs with rfl | rfl <;> simp [ω.property]

theorem actual_sign_chart_inverse (ω₁ ω₂ : UnitCircle) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hchart : 1/2 ≤ ‖(ω₁:Plane)+s • (ω₂:Plane)‖) {r : ℝ} (hr : 0 < r) :
    let ξ := r • ((ω₁:Plane)+s • (ω₂:Plane))
    ∃! z : ℝ, r • (ω₁:Plane) = graphB z ξ ∧
      r • (ω₂:Plane) = s • graphA z ξ ∧
      r = ‖ξ‖*Real.sqrt (1+z^2)/2 ∧ Real.sqrt (1+z^2) ≤ 4 := by
  dsimp only
  have hv := circle_sign_norm s hs ω₂
  have hh := graph_chart_inverse (ω₁:Plane) (s • (ω₂:Plane)) ω₁.property hv hchart hr
  dsimp only at hh
  refine ⟨graphChartZ (ω₁:Plane) (s • (ω₂:Plane)), ⟨hh.1,?_,hh.2.2⟩,?_⟩
  · have h := congrArg (fun v : Plane => s • v) hh.2.1
    rcases hs with rfl | rfl <;> simpa only [one_smul, neg_smul, smul_neg, neg_neg] using h
  · intro z hz
    apply graphB_parameter_injective (ξ := r • ((ω₁:Plane)+s • (ω₂:Plane))) ?_
      (hz.1.symm.trans hh.1)
    exact smul_ne_zero hr.ne' (norm_pos_iff.mp (by linarith))

theorem actual_sign_chart_frequency_bounds (ω₁ ω₂ : UnitCircle) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hchart : 1/2 ≤ ‖(ω₁:Plane)+s • (ω₂:Plane)‖)
    (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {r : ℝ} (hr : Ψ (r/(2:ℝ)^v) ≠ 0) :
    let η := ((2:ℝ)^v)⁻¹ • (r • ((ω₁:Plane)+s • (ω₂:Plane)))
    1/8 ≤ ‖η‖ ∧ ‖η‖ ≤ 8 := by
  dsimp only
  have hA : 0 < (2:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
  have hb := hΨ _ hr
  change 1/4 < r/(2:ℝ)^v ∧ r/(2:ℝ)^v < 4 at hb
  have hrpos : 0 < r := (div_pos_iff_of_pos_right hA).mp (by linarith [hb.1])
  have hv := circle_sign_norm s hs ω₂
  have hup : ‖(ω₁:Plane)+s • (ω₂:Plane)‖ ≤ 2 := by
    simpa only [ω₁.property,hv,one_add_one_eq_two] using norm_add_le (ω₁:Plane) (s • (ω₂:Plane))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hA), abs_of_pos hrpos]
  have he : ((2:ℝ)^v)⁻¹*(r*‖(ω₁:Plane)+s • (ω₂:Plane)‖) =
      (r/(2:ℝ)^v)*‖(ω₁:Plane)+s • (ω₂:Plane)‖ := by ring
  rw [he]
  constructor
  · have hh := mul_le_mul hb.1.le hchart (by norm_num : (0:ℝ) ≤ 1/2) (by linarith : 0 ≤ r/(2:ℝ)^v)
    norm_num at hh
    exact hh
  · have hh := mul_le_mul hb.2.le hup (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
    norm_num at hh
    exact hh

end PlanarFalconer

end OAI

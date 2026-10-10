import OAI.Probability.FirstPassage.SphereCharts
import OAI.Probability.FirstPassage.NormBoundary

namespace OAI

namespace PlanarFPP
open Set MeasureTheory

lemma HasC1CurveChart.preimage_isometry (S : Set Plane) (v : Plane)
    (e : Plane ≃ₗᵢ[ℝ] Plane) (h : HasC1CurveChart S (e v)) :
    HasC1CurveChart (e ⁻¹' S) v := by
  obtain ⟨U,hU,hv,hvS,γ,θ,hγ,hθ,hmem,hleft,hright,hreg⟩ := h
  refine ⟨e ⁻¹' U,hU.preimage e.continuous,hv,hvS,e.symm ∘ γ,θ ∘ e,?_,?_,?_,?_,?_,?_⟩
  · exact e.symm.toContinuousLinearEquiv.contDiff.comp hγ
  · exact hθ.comp e.continuous.continuousOn (fun _ hz => hz)
  · intro t
    simpa only [Function.comp_apply,mem_inter_iff,mem_preimage,e.apply_symm_apply] using hmem t
  · intro t
    simpa only [Function.comp_apply,e.apply_symm_apply] using hleft t
  · intro z hz
    change e.symm (γ (θ (e z)))=z
    rw [hright (e z) hz,e.symm_apply_apply]
  · intro t
    obtain ⟨d,hd,hne⟩ := hreg t
    refine ⟨e.symm d,e.symm.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t hd,?_⟩
    intro hz
    exact hne (e.symm.injective (by simpa using hz))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_sphere_curve_chart (henv : ExponentialEnvironment P τ) (v : Plane)
    (hv : actualSourceTimeConstant v=1) : HasC1CurveChart {z | actualSourceTimeConstant z=1} v := by
  let μ := actualSourceTimeConstant
  have horizontal (z : Plane) (hz : μ z=1) (hx : z 0 ≠ 0) : HasC1CurveChart {w | μ w=1} z := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · exact sphere_horizontal_chart μ actualSourceTimeConstant_norm (actual_profile_contDiff henv) (-1)
        (by norm_num) z hz (by linarith)
    · exact sphere_horizontal_chart μ actualSourceTimeConstant_norm (actual_profile_contDiff henv) 1
        (by norm_num) z hz (by simpa using hpos)
  by_cases hx : v 0 ≠ 0
  · exact horizontal v hv hx
  · have hvne : v ≠ 0 := by
      intro he
      have hz := (actualSourceTimeConstant_norm.zero_iff v).mpr he
      linarith
    have hy : v 1 ≠ 0 := by
      intro hy
      apply hvne
      ext i
      fin_cases i <;> simp_all
    have hsv : μ (swapPlane v)=1 := by dsimp [μ]; rw [actualSourceTimeConstant_swap henv,hv]
    have hs := horizontal (swapPlane v) hsv (by simpa using hy)
    have hh := HasC1CurveChart.preimage_isometry {z | μ z=1} v swapPlane hs
    have he : swapPlane ⁻¹' {z | μ z=1}={z | μ z=1} := by
      ext z
      simp only [mem_preimage,mem_ofPred_eq,μ,actualSourceTimeConstant_swap henv]
    rwa [he] at hh

theorem actual_boundary_curve (henv : ExponentialEnvironment P τ) (v : Plane)
    (hv : v ∈ frontier {z | actualSourceTimeConstant z ≤ 1}) :
    HasC1CurveChart (frontier {z | actualSourceTimeConstant z ≤ 1}) v := by
  rw [norm_ball_frontier _ actualSourceTimeConstant_norm] at hv ⊢
  exact actual_sphere_curve_chart henv v hv

theorem manuscriptMain (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)
    (henv : ExponentialEnvironment P τ) :
    ∃ μ : Plane → ℝ, TimeConstantNorm μ ∧ IsTimeConstant P τ μ ∧
      DifferentiableAwayFromOrigin μ ∧ UniqueNormalizedSupports μ ∧ C1UnitSphere μ ∧
      (∀ v ∈ frontier {z | μ z ≤ 1}, ∃! L : Set Plane,
        ∃ g : Plane →L[ℝ] ℝ, g ≠ 0 ∧ (∀ z, μ z ≤ 1 → g z ≤ g v) ∧ L={z | g z=g v}) ∧
      (∀ v ∈ frontier {z | μ z ≤ 1}, HasC1CurveChart (frontier {z | μ z ≤ 1}) v) := by
  exact ⟨actualSourceTimeConstant,actualSourceTimeConstant_norm,actualSourceTimeConstant_isTimeConstant henv,
    actual_differentiable_away henv,
    unique_supports_of_differentiable _ actualSourceTimeConstant_norm (actual_differentiable_away henv),
    actual_C1_unit_sphere henv,
    norm_supporting_line_unique _ actualSourceTimeConstant_norm (actual_differentiable_away henv),
    actual_boundary_curve henv⟩

end PlanarFPP

end OAI

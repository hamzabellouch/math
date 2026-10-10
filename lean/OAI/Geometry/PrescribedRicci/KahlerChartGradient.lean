import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerEnergy
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral
import OAI.Geometry.PrescribedRicci.KahlerGradientCoercivity
import OAI.Geometry.PrescribedRicci.KahlerLocalL2Comparison

namespace OAI

/-! Kahler Chart Gradient. -/

section

 
noncomputable section
open Matrix Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

omit [T2Space X] [CompactSpace X] in
lemma formEnergy_localized (g : KaehlerMetric A) (ψ : SmoothRealFunction A)
    (i : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    formEnergy (g.matrix i z) (fderiv ℝ (ψ.localized i) z) =
      (g.energy ψ ψ).value ((A.chart i).symm z) := by
  have he : ψ.localized i =ᶠ[𝓝 z] ψ.localExpression i := by
    filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy using ψ.localized_eq hy
  rw [he.fderiv_eq]
  exact (g.energy_local ψ ψ i hz).symm

omit [T2Space X] [CompactSpace X] in
lemma localized_gradient_pointwise (g : KaehlerMetric A) (i : Fin A.count)
    (ψ : SmoothRealFunction A) {K : Set (Coordinates d)}
    (ht : K ⊆ (A.chart i).target) (hqK : tsupport (ψ.localized i) ⊆ K)
    {a v : ℝ} (hv : 0 ≤ v)
    (hgrad : ∀ z ∈ K, ∀ L : Coordinates d →L[ℝ] ℝ,
      a * ‖L‖ ^ 2 ≤ formEnergy (g.matrix i z) L)
    (hvol : ∀ z ∈ K, v ≤ g.volumeCoefficient i z) (z : Coordinates d) :
    (a*v) * ‖fderiv ℝ (ψ.localized i) z‖ ^ 2 ≤
      localizeFunction i (g.energy ψ ψ).value z * g.volumeCoefficient i z := by
  by_cases hz : z ∈ tsupport (ψ.localized i)
  · have hzK := hqK hz
    have hzT := ht hzK
    have hG := hgrad z hzK (fderiv ℝ (ψ.localized i) z)
    rw [g.formEnergy_localized ψ i hzT] at hG
    simp only [localizeFunction, ite_eq_left hzT]
    calc
      _ = v * (a * ‖fderiv ℝ (ψ.localized i) z‖^2) := by ring
      _ ≤ v * (g.energy ψ ψ).value ((A.chart i).symm z) := mul_le_mul_of_nonneg_left hG hv
      _ ≤ g.volumeCoefficient i z * (g.energy ψ ψ).value ((A.chart i).symm z) :=
        mul_le_mul_of_nonneg_right (hvol z hzK) (g.energy_nonneg ψ _)
      _ = _ := mul_comm _ _
  · have hd : fderiv ℝ (ψ.localized i) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hz (tsupport_fderiv_subset ℝ hh))
    rw [hd, norm_zero, zero_pow (by omega : (2:ℕ) ≠ 0), mul_zero]
    by_cases ht : z ∈ (A.chart i).target
    · simp only [localizeFunction, ite_eq_left ht]
      exact mul_nonneg (g.energy_nonneg ψ _) (g.volumeCoefficient_pos i ht).le
    · simp only [localizeFunction, ite_eq_right ht, zero_mul, le_refl]

lemma localized_gradient_integrable (ψ : SmoothRealFunction A) (i : Fin A.count)
    (hψs : tsupport ψ.value ⊆ (A.chart i).source) :
    Integrable (fun z : Coordinates d => ‖fderiv ℝ (ψ.localized i) z‖^2) := by
  obtain ⟨hq,hqc,hqt⟩ := ψ.localized_smooth_compact i hψs
  have hD : Continuous (fun z => ‖fderiv ℝ (ψ.localized i) z‖^2) :=
    (hq.continuous_fderiv (by simp)).norm.pow 2
  have hDc : HasCompactSupport (fun z => ‖fderiv ℝ (ψ.localized i) z‖^2) :=
    HasCompactSupport.comp_left (f := fderiv ℝ (ψ.localized i))
      (g := fun L : Coordinates d →L[ℝ] ℝ => ‖L‖^2) (hqc.fderiv ℝ) (by simp)
  exact hD.integrable_of_hasCompactSupport hDc

lemma localized_gradient_integral_le (g : KaehlerMetric A) (i : Fin A.count)
    (ψ : SmoothRealFunction A) (hψs : tsupport ψ.value ⊆ (A.chart i).source)
    {c : ℝ} (hc : 0 < c)
    (hpoint : ∀ z : Coordinates d, c * ‖fderiv ℝ (ψ.localized i) z‖ ^ 2 ≤
      localizeFunction i (g.energy ψ ψ).value z * g.volumeCoefficient i z) :
    (∫ z : Coordinates d, ‖fderiv ℝ (ψ.localized i) z‖ ^ 2) ≤
      c⁻¹ * g.integral (g.energy ψ ψ).value := by
  have hEs : tsupport (g.energy ψ ψ).value ⊆ (A.chart i).source :=
    (g.energy_support ψ ψ).trans hψs
  have hint := g.chart_weighted_integrable i (g.energy ψ ψ).continuous hEs
  have hDi := localized_gradient_integrable ψ i hψs
  have hh := MeasureTheory.integral_mono (hDi.const_mul c) hint hpoint
  rw [MeasureTheory.integral_const_mul] at hh
  have he : (∫ z, localizeFunction i (g.energy ψ ψ).value z * g.volumeCoefficient i z) =
      g.integral (g.energy ψ ψ).value := by
    rw [g.integral_chart i (g.energy ψ ψ).continuous hEs, g.chartIntegral_eq_localize]
  rw [he] at hh
  calc
    _ = c⁻¹ * (c * ∫ z : Coordinates d, ‖fderiv ℝ (ψ.localized i) z‖ ^ 2) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hc).le

lemma chart_gradient_L2_bound (g : KaehlerMetric A) (i : Fin A.count)
    {K : Set X} (hK : IsCompact K) (hs : K ⊆ (A.chart i).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : SmoothRealFunction A, tsupport ψ.value ⊆ K →
      (∫ z : Coordinates d, ‖fderiv ℝ (ψ.localized i) z‖ ^ 2) ≤
        C * g.integral (g.energy ψ ψ).value := by
  let K' := (A.chart i) '' K
  have hK' : IsCompact K' := hK.image_of_continuousOn ((A.chart i).continuousOn.mono hs)
  have ht : K' ⊆ (A.chart i).target := by rintro z ⟨x,hx,rfl⟩; exact (A.chart i).mapsTo (hs hx)
  obtain ⟨a,ha,hgrad⟩ := g.compact_gradient_coercivity i hK' ht
  obtain ⟨v,b,hv,hb,hvol⟩ := g.compact_volume_bounds i hK' ht
  refine ⟨(a*v)⁻¹, inv_pos.mpr (mul_pos ha hv), fun ψ hψ => ?_⟩
  have hqK : tsupport (ψ.localized i) ⊆ K' :=
    closure_minimal ((ψ.localized_support i).trans (image_mono hψ)) hK'.isClosed
  apply g.localized_gradient_integral_le i ψ (hψ.trans hs) (mul_pos ha hv)
  exact g.localized_gradient_pointwise i ψ ht hqK hv.le hgrad (fun z hz => (hvol z hz).1)

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI

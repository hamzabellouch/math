import Mathlib
import OAI.Geometry.PrescribedRicci.CoordinateVolumeComparison
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral

namespace OAI

/-! Kahler Local L2 Comparison. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma chartIntegral_eq_localize (g : KaehlerMetric A) (i : Fin A.count) (f : X → ℝ) :
    g.chartIntegral i f = ∫ z, localizeFunction i f z * g.volumeCoefficient i z := by
  rw [chartIntegral, ← integral_indicator (A.chart i).open_target.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ (A.chart i).target
  · simp only [Set.indicator_of_mem hz, localizeFunction, ite_eq_left hz]
  · simp only [Set.indicator_of_notMem hz, localizeFunction, ite_eq_right hz, zero_mul]

lemma chart_weighted_integrable [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (i : Fin A.count) {f : X → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ (A.chart i).source) :
    Integrable (fun z => localizeFunction i f z * g.volumeCoefficient i z) := by
  obtain ⟨hl,hc,ht⟩ := localizeFunction_continuous_compact i hf hs
  exact (continuous_real_mul_on_tsupport hl (fun z hz =>
    ((g.volumeCoefficient_smooth i).continuousOn z (ht hz)).continuousAt
      ((A.chart i).open_target.mem_nhds (ht hz)))).integrable_of_hasCompactSupport hc.mul_right

lemma compact_volume_bounds (g : KaehlerMetric A) (i : Fin A.count)
    {K : Set (Coordinates d)} (hK : IsCompact K) (hs : K ⊆ (A.chart i).target) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ z ∈ K, a ≤ g.volumeCoefficient i z ∧ g.volumeCoefficient i z ≤ b := by
  have hc := (g.volumeCoefficient_smooth i).continuousOn.mono hs
  obtain ⟨b,hb⟩ := hK.bddAbove_image hc
  by_cases hn : K.Nonempty
  · obtain ⟨z,hz,hm⟩ := hK.exists_isMinOn hn hc
    refine ⟨g.volumeCoefficient i z, max b 1, g.volumeCoefficient_pos i (hs hz),
      lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _), fun y hy => ⟨hm hy, ?_⟩⟩
    exact (hb (mem_image_of_mem _ hy)).trans (le_max_left _ _)
  · refine ⟨1,1,by norm_num,by norm_num,fun z hz => ?_⟩
    exact (hn ⟨z,hz⟩).elim

end KaehlerMetric
end Anticanonical.SourceSmooth
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

omit [T2Space X] [CompactSpace X] in
lemma square_weight_support (ρ f : Smooth A) :
    tsupport (fun x => ‖ρ x * f x‖ ^ 2) ⊆ tsupport (ρ : X → ℂ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  apply subset_tsupport
  change ρ x ≠ 0
  intro h
  exact hx (by simp [h])

lemma local_weighted_L2_comparison (g : KaehlerMetric A) (i : Fin A.count) (ρ : Smooth A)
    (hs : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ f : Smooth A,
      a * ‖schwartzCoord 0 (localize A i ρ hs f)‖ ^ 2 ≤
        coordinateVolumeFactor d * g.integral (fun x => ‖ρ x * f x‖ ^ 2) ∧
      coordinateVolumeFactor d * g.integral (fun x => ‖ρ x * f x‖ ^ 2) ≤
        b * ‖schwartzCoord 0 (localize A i ρ hs f)‖ ^ 2 := by
  have hs' : tsupport (ρ : X → ℂ) ⊆ (A.chart i).source := by simpa using hs
  let K := (A.chart i) '' tsupport (ρ : X → ℂ)
  have hK : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
    ((A.chart i).continuousOn.mono hs')
  have hKt : K ⊆ (A.chart i).target := by rintro z ⟨x,hx,rfl⟩; exact (A.chart i).mapsTo (hs' hx)
  obtain ⟨a,b,ha,hb,hab⟩ := g.compact_volume_bounds i hK hKt
  refine ⟨a,b,ha,hb,fun f => ?_⟩
  let F (x : X) := ‖ρ x * f x‖ ^ 2
  have hF : Continuous F := (ρ.continuous.fun_mul f.continuous).norm.pow 2
  have hFs : tsupport F ⊆ (A.chart i).source := (square_weight_support ρ f).trans hs'
  have hraw := KaehlerMetric.localizeFunction_continuous_compact i hF hFs
  have hi : Integrable (KaehlerMetric.localizeFunction i F) (volume : Measure (Coordinates d)) :=
    hraw.1.integrable_of_hasCompactSupport hraw.2.1
  have hwi := g.chart_weighted_integrable i hF hFs
  have hsK : Function.support (KaehlerMetric.localizeFunction i F) ⊆ K :=
    (KaehlerMetric.localizeFunction_support i F).trans (image_mono (square_weight_support ρ f))
  have hpos (z : Coordinates d) : 0 ≤ KaehlerMetric.localizeFunction i F z := by
    unfold KaehlerMetric.localizeFunction
    split_ifs <;> positivity
  have hl : a * ∫ z, KaehlerMetric.localizeFunction i F z ≤ g.integral F := by
    rw [g.integral_chart i hF hFs, g.chartIntegral_eq_localize, ← integral_const_mul]
    apply MeasureTheory.integral_mono (hi.const_mul a) hwi
    intro z
    by_cases hz : z ∈ Function.support (KaehlerMetric.localizeFunction i F)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hab z (hsK hz)).1 (hpos z)
    · simp only [Function.notMem_support.mp hz, mul_zero, zero_mul, le_refl]
  have hu : g.integral F ≤ b * ∫ z, KaehlerMetric.localizeFunction i F z := by
    rw [g.integral_chart i hF hFs, g.chartIntegral_eq_localize, ← integral_const_mul]
    apply MeasureTheory.integral_mono hwi (hi.const_mul b)
    intro z
    by_cases hz : z ∈ Function.support (KaehlerMetric.localizeFunction i F)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hab z (hsK hz)).2 (hpos z)
    · simp only [Function.notMem_support.mp hz, mul_zero, zero_mul, le_refl]
  rw [norm_sq_localize_integral]
  constructor
  · calc
      _ = coordinateVolumeFactor d * (a * ∫ z, KaehlerMetric.localizeFunction i F z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (coordinateVolumeFactor_pos d).le
  · calc
      _ ≤ coordinateVolumeFactor d * (b * ∫ z, KaehlerMetric.localizeFunction i F z) :=
        mul_le_mul_of_nonneg_left hu (coordinateVolumeFactor_pos d).le
      _ = _ := by ring

end GlobalElliptic

end
end

end OAI

import OAI.Analysis.RCDHeat.WeightedGradientConvex
import OAI.Analysis.RCDHeat.CompressionIntegral

namespace OAI

/-! # Physical-time mean variation from a reversed subpath -/

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem reverse_subpath_secant (π : Measure C(Time,X)) {g : X → ℝ} (hg : Measurable g)
    (s : Time) (hs : 0 < (s:ℝ)) {h : ℝ} (hh : 0 < h) (hhs : h < (s:ℝ)) :
    -(planInitialSecant (π.map (subpath s 0)) g (h/(s:ℝ)))/(s:ℝ) =
      (∫ γ : C(Time,X), g (γ s)-g (geodesicExtension γ ((s:ℝ)-h)) ∂π)/h := by
  have hq : h/(s:ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨(div_pos hh hs).le,(div_lt_one hs).mpr hhs |>.le⟩
  let q : Time := ⟨h/(s:ℝ),hq⟩
  have hmeas : AEStronglyMeasurable
      (fun γ : C(Time,X) => g (geodesicExtension γ (h/(s:ℝ)))-g (γ 0))
      (π.map (subpath s 0)) := by
    have he (γ : C(Time,X)) : geodesicExtension γ (h/(s:ℝ)) = γ q :=
      geodesicExtension_eq γ q
    simp only [he]
    exact ((hg.comp (measurable_path_eval q)).sub (hg.comp (measurable_path_eval 0))).aestronglyMeasurable
  have he (γ : C(Time,X)) : geodesicExtension (subpath s 0 γ) (h/(s:ℝ)) =
      geodesicExtension γ ((s:ℝ)-h) := by
    rw [subpath_extension s 0 γ hq]
    congr 1
    change (1-h/(s:ℝ))*(s:ℝ)+(h/(s:ℝ))*0 = (s:ℝ)-h
    field_simp [hs.ne']
    ring
  dsimp only [planInitialSecant]
  rw [integral_map (subpath_measurable s 0).aemeasurable hmeas]
  have hi : (fun γ : C(Time,X) => g (geodesicExtension (subpath s 0 γ) (h/(s:ℝ)))-
      g (subpath s 0 γ 0)) = fun γ => -(g (γ s)-g (geodesicExtension γ ((s:ℝ)-h))) := by
    funext γ
    rw [he,subpath_zero]
    ring
  rw [hi,integral_neg]
  field_simp [hs.ne',hh.ne']

theorem reverse_subpath_mean_limit (π : Measure C(Time,X)) {g : X → ℝ} (hg : Measurable g)
    (s : Time) (hs : 0 < (s:ℝ)) {c : ℝ}
    (hv : Tendsto (planInitialSecant (π.map (subpath s 0)) g) (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto (fun h : ℝ =>
      (∫ γ : C(Time,X), g (γ s)-g (geodesicExtension γ ((s:ℝ)-h)) ∂π)/h)
      (𝓝[>] (0:ℝ)) (𝓝 (-c/(s:ℝ))) := by
  have hd : Tendsto (fun h : ℝ => h/(s:ℝ)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [zero_div] using
        ((show Tendsto (fun h : ℝ => h) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) from nhdsWithin_le_nhds).div_const (s:ℝ))
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact div_pos hh hs
  have hl := ((hv.comp hd).neg.div_const (s:ℝ))
  apply hl.congr'
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), h < (s:ℝ) :=
    (gt_mem_nhds hs).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hsmall] with h hh hsmall
  exact reverse_subpath_secant π hg s hs hh hsmall

end RegularPointCoordinates

end

end OAI

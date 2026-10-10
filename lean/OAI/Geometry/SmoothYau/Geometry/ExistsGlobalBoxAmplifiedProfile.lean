import Mathlib
import OAI.Geometry.SmoothYau.NodalMeasure.CompactRegularLevelIntrinsicFinite

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma actualCoordinateHessian_congr_germ (g : SmoothMetric E E)
    {φ ψ : E → ℝ} {x : E} (h : φ =ᶠ[𝓝 x] ψ) :
    actualCoordinateHessian g φ x = actualCoordinateHessian g ψ x := by
  unfold actualCoordinateHessian coordinateCovariantSecond
  rw [h.fderiv_eq, (h.fderiv (𝕜 := ℝ)).fderiv_eq]

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricGradient_congr_germ (g : SmoothMetric E E)
    {φ ψ : E → ℝ} {x : E} (h : φ =ᶠ[𝓝 x] ψ) :
    coordinateMetricGradient g φ x = coordinateMetricGradient g ψ x := by
  unfold coordinateMetricGradient
  rw [h.fderiv_eq]

lemma actualProfileStrict_congr_germ (g : SmoothMetric E E)
    {φ ψ : E → ℝ} {x : E} (h : φ =ᶠ[𝓝 x] ψ) :
    actualProfileStrict g φ x ↔ actualProfileStrict g ψ x := by
  unfold actualProfileStrict actualProfileTraceForm
  rw [h.fderiv_eq, actualCoordinateHessian_congr_germ g h,
    coordinateMetricGradient_congr_germ g h]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma profile_eq_germ_of_not_tsupport {φ ψ : E → ℝ} {x : E}
    (hx : x ∉ tsupport (fun y => ψ y - φ y)) : ψ =ᶠ[𝓝 x] φ := by
  have h := notMem_tsupport_iff_eventuallyEq.mp hx
  filter_upwards [h] with y hy
  exact sub_eq_zero.mp hy

end


open Set Filter MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_global_box_amplified_profile
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (I : Box (Fin 3))
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (hIK : normalWaveEquiv '' Box.Icc I ⊆ K)
    (ha : ∀ x ∈ normalWaveEquiv '' Box.Icc I, coordinateMetricGradient g φ x ≠ 0)
    (T : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ ψ ∧
      HasCompactSupport (fun x => ψ x-φ x) ∧
      tsupport (fun x => ψ x-φ x) ⊆ normalWaveEquiv '' Box.Ioo I ∧
      (∀ x, |ψ x-φ x| < η) ∧
      (∀ x ∈ normalWaveEquiv '' Box.Icc I,
        coordinateMetricGradient g ψ x ≠ 0 ∧ actualProfileStrict g ψ x) ∧
      (∀ x ∈ K, fderiv ℝ ψ x ≠ 0 → actualProfileStrict g ψ x) ∧
      (∀ x ∈ K, fderiv ℝ ψ x = 0 →
        ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
          ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g ψ x v v) ∧
      T < ∫ x in Box.Icc I, profileFrequencyScale g ψ (normalWaveEquiv x) := by
  have hs : ∀ x ∈ normalWaveEquiv '' Box.Icc I, actualProfileStrict g φ x := by
    intro x hx
    apply hnc x (hIK hx)
    intro hz
    apply ha x hx
    simp [coordinateMetricGradient, hz]
  obtain ⟨ψ,hψ,hc,hsp,hclose,hinside,hmass⟩ :=
    exists_box_amplified_profile g I hφ ha hs T hη
  have hgerm : ∀ x, x ∉ normalWaveEquiv '' Box.Icc I → ψ =ᶠ[𝓝 x] φ := by
    intro x hx
    apply profile_eq_germ_of_not_tsupport
    intro hxsp
    apply hx
    obtain ⟨y,hy,rfl⟩ := hsp hxsp
    exact ⟨y, I.Ioo_subset_Icc hy, rfl⟩
  refine ⟨ψ,hψ,hc,hsp,hclose,hinside,?_,?_,hmass⟩
  · intro x hx hdx
    by_cases hxi : x ∈ normalWaveEquiv '' Box.Icc I
    · exact (hinside x hxi).2
    · exact (actualProfileStrict_congr_germ g (hgerm x hxi)).mpr
        (hnc x hx (by simpa only [(hgerm x hxi).fderiv_eq] using hdx))
  · intro x hx hdx
    by_cases hxi : x ∈ normalWaveEquiv '' Box.Icc I
    · have hz : coordinateMetricGradient g ψ x = 0 := by
        simp [coordinateMetricGradient, hdx]
      exact ((hinside x hxi).1 hz).elim
    · have he := hgerm x hxi
      rw [actualCoordinateHessian_congr_germ g he]
      exact hcrit x hx (by simpa only [← he.fderiv_eq] using hdx)


end YauCounterexamples
end

end OAI

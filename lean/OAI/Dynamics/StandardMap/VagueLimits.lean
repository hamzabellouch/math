import OAI.Dynamics.StandardMap.ArrayTestCover

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal CompactlySupported
namespace StandardMapEntropy

lemma exists_vague_limit {X ι : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (l : Ultrafilter ι) (μ : ι → Measure X)
    [∀ i, IsFiniteMeasureOnCompacts (μ i)]
    (hb : ∀ g : C_c(X,ℝ), ∃ C : ℝ, ∀ᶠ i in (l:Filter ι), |∫ x,g x ∂μ i| ≤ C) :
    ∃ ν : Measure X, ν.Regular ∧ IsFiniteMeasureOnCompacts ν ∧ (∀ g : C_c(X,ℝ),
      Tendsto (fun i => ∫ x,g x ∂μ i) (l:Filter ι) (𝓝 (∫ x,g x ∂ν))) := by
  have hl (g : C_c(X,ℝ)) : ∃ x : ℝ, Tendsto (fun i => ∫ x,g x ∂μ i) (l:Filter ι) (𝓝 x) := by
    obtain ⟨C,hC⟩ := hb g
    have hm : ∀ᶠ i in (l:Filter ι), (∫ x,g x ∂μ i)∈Icc (-C) C := by
      filter_upwards [hC] with i hi
      exact abs_le.mp hi
    obtain ⟨x,hx,hh⟩ := isCompact_Icc.ultrafilter_le_nhds' (f := l.map (fun i => ∫ x,g x ∂μ i)) hm
    exact ⟨x,hh⟩
  choose Λ hΛ using hl
  let Λ' : C_c(X,ℝ) →ₚ[ℝ] ℝ := {
    toFun := Λ
    map_add' := by
      intro g h
      have ht : Tendsto (fun i => ∫ x,(g+h) x ∂μ i) (l:Filter ι) (𝓝 (Λ g+Λ h)) := by
        convert! (hΛ g).add (hΛ h) using 1
        funext i
        exact integral_add (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport)
          (h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport)
      exact tendsto_nhds_unique (hΛ (g+h)) ht
    map_smul' := by
      intro c g
      have ht : Tendsto (fun i => ∫ x,(c • g) x ∂μ i) (l:Filter ι) (𝓝 (c • Λ g)) := by
        convert! (hΛ g).const_smul c using 1
        funext i
        exact integral_smul c _
      exact tendsto_nhds_unique (hΛ (c • g)) ht
    monotone' := by
      intro g h hgh
      apply le_of_tendsto_of_tendsto' (hΛ g) (hΛ h)
      intro i
      exact integral_mono (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport)
        (h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport) hgh }
  refine ⟨RealRMK.rieszMeasure Λ',inferInstance,inferInstance,?_⟩
  intro g
  rw [RealRMK.integral_rieszMeasure]
  exact hΛ g
end StandardMapEntropy

end OAI

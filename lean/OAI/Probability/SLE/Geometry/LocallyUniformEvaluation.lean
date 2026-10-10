import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Evaluation at moving interior points of locally uniformly convergent complex maps. -/
noncomputable section
open Set Filter Metric
open scoped Topology

namespace SLEExactGauge

lemma locallyUniform_evaluation_tendsto {D : Set ℂ} (hD : IsOpen D)
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} (hF : ContinuousOn F D)
    (hf : TendstoLocallyUniformlyOn f F atTop D)
    {z : ℕ → ℂ} {a : ℂ} (ha : a∈D) (hz : Tendsto z atTop (𝓝 a)) :
    Tendsto (fun n => f n (z n)) atTop (𝓝 (F a)) := by
  have hFa : Tendsto (fun n => F (z n)) atTop (𝓝 (F a)) :=
    (hF a ha).continuousAt (hD.mem_nhds ha) |>.tendsto.comp hz
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨V,hV,hsmall⟩ := hf _ (dist_mem_uniformity (half_pos hε)) a ha
  rw [hD.nhdsWithin_eq ha] at hV
  filter_upwards [hsmall,hz.eventually hV,
    Metric.tendsto_nhds.mp hFa (ε/2) (half_pos hε)] with n hn hzV hnF
  have hh : dist (F (z n)) (f n (z n))<ε/2 := hn _ hzV
  have htri := dist_triangle (f n (z n)) (F (z n)) (F a)
  rw [dist_comm (f n (z n)) (F (z n))] at htri
  linarith

lemma locallyUniform_reindex {D : Set ℂ} {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : TendstoLocallyUniformlyOn f F atTop D) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => f (φ n)) F atTop D := by
  intro U hU z hz
  obtain ⟨V,hV,hN⟩ := hf U hU z hz
  exact ⟨V,hV,hφ.eventually hN⟩

end SLEExactGauge

end

end OAI

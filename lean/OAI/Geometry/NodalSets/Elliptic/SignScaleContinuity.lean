import Mathlib.Topology.UniformSpace.HeineCantor
import OAI.Geometry.NodalSets.Elliptic.SignScaleSeed

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourceSignScale_continuous (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (sourceSignScale g S) := by
  have hgrad := metricGradient_continuous g hg hp S hS
  exact (((hg.continuous.clm_apply hgrad).clm_apply hgrad).add continuous_const).sqrt

lemma compact_main_scale_comparison (s : Coord → ℝ) {H : Set Coord} (hH : IsCompact H)
    (hs : ContinuousOn s H) (hlo : ∀ x ∈ H, 2 ≤ s x) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ H, ∀ y ∈ H,
      sourceEuclideanNorm (x-y) ≤ (n:ℝ)^(-5/12:ℝ) →
      s x/2 ≤ s y ∧ s y ≤ 2*s x := by
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp
    (hH.uniformContinuousOn_of_continuous hs) 1 (by norm_num)
  have ht : Tendsto (fun n : ℕ ↦ (n:ℝ)^(-5/12:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/12)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn
  intro x hx y hy hnear
  have hh := hd x hx y hy (by
    rw [dist_eq_norm]
    exact ((norm_le_sourceEuclideanNorm _).trans hnear).trans_lt hn)
  rw [Real.dist_eq] at hh
  have h := abs_lt.mp hh
  have hx2 := hlo x hx
  constructor <;> linarith

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma source_sign_scale_eq (x : Coord) (hx : x ∈ a.E) :
    sourceSignScale a.G a.A x = sourceSignScale g S x := by
  obtain ⟨hg,_,hS⟩ := a.germ x hx
  unfold sourceSignScale
  rw [hg.self_of_nhds,(metricGradient_eventuallyEq hg hS).self_of_nhds]

include a in
lemma source_sign_scale_continuousOn {H : Set Coord} (hHD : H ⊆ D) :
    ContinuousOn (sourceSignScale g S) H := by
  apply (sourceSignScale_continuous a.G a.smooth_G a.positive_G a.A a.smooth_A).continuousOn.congr
  intro x hx
  exact (a.source_sign_scale_eq x (a.centers_E (hHD hx))).symm

include a in
lemma source_main_scale_comparison {H : Set Coord} (hH : IsCompact H) (hHD : H ⊆ D) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ H, ∀ y ∈ H,
      sourceEuclideanNorm (x-y) ≤ (n:ℝ)^(-5/12:ℝ) →
      sourceSignScale g S x/2 ≤ sourceSignScale g S y ∧
        sourceSignScale g S y ≤ 2*sourceSignScale g S x :=
  compact_main_scale_comparison _ hH (a.source_sign_scale_continuousOn hHD)
    (fun x hx ↦ a.source_sign_scale_lower x (hHD hx))

lemma original_direction_length (t : a.cover.Parameter) (j : Fin 3) :
    g (coverSourceCenter a.cover t) (a.cover.triple.q t j) (a.cover.triple.q t j) =
      (sourceSignScale g S (coverSourceCenter a.cover t))^2 := by
  have he := a.cover.triple.length t j
  have hp := a.positive_G (coverSourceCenter a.cover t) _ (a.nonzero_gradient _ (a.cover.center t).property)
  change 0 < a.G (coverSourceCenter a.cover t)
    (metricGradient a.G a.A (coverSourceCenter a.cover t))
    (metricGradient a.G a.A (coverSourceCenter a.cover t)) at hp
  change a.G (coverSourceCenter a.cover t) (a.cover.triple.q t j) (a.cover.triple.q t j) =
    a.G (coverSourceCenter a.cover t) (metricGradient a.G a.A (coverSourceCenter a.cover t))
      (metricGradient a.G a.A (coverSourceCenter a.cover t))+4 at he
  have hh : (sourceSignScale a.G a.A (coverSourceCenter a.cover t))^2 =
      a.G (coverSourceCenter a.cover t) (metricGradient a.G a.A (coverSourceCenter a.cover t))
        (metricGradient a.G a.A (coverSourceCenter a.cover t))+4 :=
    Real.sq_sqrt (by linarith)
  rw [← hh,a.source_sign_scale_eq (coverSourceCenter a.cover t)
      (a.centers_E (a.cover.center t).property),
    (a.center_identifications t).1] at he
  exact he

end LocalCompactWaveData
end
end Yau.Geometry

end OAI

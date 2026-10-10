import OAI.Geometry.NodalSets.Charts.MetricFrequencyBounds
import OAI.Geometry.NodalSets.Elliptic.SignScaleContinuity
import OAI.Geometry.NodalSets.Waves.LatticeFrequencyAnnulus

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_main_frequency_annulus_fixed_domain
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ κ > 0, ∃ B > 0, ∀ (w S : Coord → ℝ) (D U : Set Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
      U ⊆ H → ∀ᶠ n : ℕ in atTop, ∀ x ∈ D, ∀ i : SourceGrid U n × Fin 3,
      sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      κ ≤ sourceEuclideanNorm (sourceFrequency (g (scaledLatticePoint n i.1))
        (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2) (sourceSignScale g S x)) ∧
      sourceEuclideanNorm (sourceFrequency (g (scaledLatticePoint n i.1))
        (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2) (sourceSignScale g S x)) ≤ B := by
  obtain ⟨κ,hκ,B,hB,hmetric⟩ := compact_metric_frequency_bounds g hH hg hp
  refine ⟨κ,hκ,B,hB,?_⟩
  intro w S D U m J K k0 a hD hDH hUD hUH
  filter_upwards [a.source_main_scale_comparison hD Subset.rfl] with n hn
  intro x hx i hi
  have hy : scaledLatticePoint n i.1 ∈ D := hUD i.1.property
  have hr := hn x hx _ hy hi
  have hx0 : 0 < sourceSignScale g S x := by linarith [a.source_sign_scale_lower x hx]
  have hy0 : 0 < sourceSignScale g S (scaledLatticePoint n i.1) := by
    linarith [a.source_sign_scale_lower _ (hUD i.1.property)]
  apply hmetric _ (hDH hy) _ _ _ hx0 hy0 _ hr.1 hr.2
  simpa only [latticeFrame_center] using a.original_direction_length (latticeFrame a.cover hUD n i.1) i.2

end
end Yau.Geometry

end OAI

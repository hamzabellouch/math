import OAI.Geometry.NodalSets.Waves.FixedDomainLatticeFrequencyAnnulus
import OAI.Geometry.NodalSets.Waves.LatticeNormalizedWeights
import OAI.Geometry.NodalSets.Waves.PlaneWaveSecondMoment

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

theorem lattice_main_coordinate_moment_fixed_domain
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ c > 0, ∀ (w S : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0), IsCompact D → D ⊆ H → ∀ (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∃ j : Fin 4,
        c ≤ ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)),
          ‖a.latticeAlpha hUD n x i‖^2 *
            (sourceFrequency (g (scaledLatticePoint n i.1))
              (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)
              (sourceSignScale g S x) j)^2 := by
  classical
  obtain ⟨κ,hκ,B,hB,hann⟩ := lattice_main_frequency_annulus_fixed_domain g hH hg hp
  refine ⟨κ^2/8,by positivity,?_⟩
  intro w S D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
  have hm := a.latticeAlpha_main_mass hUD hU hUb hQ hQU (1/2) (by norm_num)
  filter_upwards [hann w S D U m J K k0 a hD hDH hUD hUH,hm] with n hn hmass
  obtain ⟨hfin,hmass⟩ := hmass
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx
  apply coordinate_second_moment _ _ _ κ hκ.le
  · linarith [(hmass x hx).2]
  · intro i hi
    exact (hn x (hUD (hQU hx)) i (Finset.mem_filter.mp hi).2).1

end
end Yau.Geometry

end OAI

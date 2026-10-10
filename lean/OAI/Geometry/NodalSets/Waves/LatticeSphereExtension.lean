import OAI.Geometry.NodalSets.Charts.SeedChartScalarExtension
import OAI.Geometry.NodalSets.Coefficients.LatticeResidualSupport

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Yau.Jets.Coord → Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ}
variable {w S : Yau.Jets.Coord → ℝ} {D U : Set Yau.Jets.Coord} {m J K k0 : ℕ}
variable (b : LocalCompactWaveData g w S D m J K k0)

theorem literal_lattice_sphere_extension (hD : IsCompact D) (hUD : U ⊆ D)
    (hUb : Bornology.IsBounded U) {Ω : Set Yau.Jets.Coord} (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ Q : Set Yau.Jets.Coord, IsCompact Q ∧ Q ⊆ Ω ∧
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
        letI := hfin
        ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
          let v := gaussianWaveField
            (fun i : SourceGrid U n × Fin 3 ↦ latticeWave b.cover b.beams hUD n i.1 i.2) coeff
          ContDiff ℝ ∞ (fun x ↦ seedCoordinateField n x+v x) →
          ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧
            tsupport (u-sphericalSeed n) ⊆ seedSphereFromCoord '' Q ∧
            ∀ x, u (seedSphereFromCoord x) = seedCoordinateField n x+v x := by
  obtain ⟨Q,hQ,hQΩ,hDQ,hbound⟩ := b.lattice_residual_support hD hUD hUb hΩ hDΩ
  refine ⟨Q,hQ,hQΩ,?_⟩
  filter_upwards [hbound] with n hn
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff v hu
  have hv : ContDiff ℝ ∞ v := by
    have he : v = fun x ↦ (seedCoordinateField n x+v x)-seedCoordinateField n x := by
      funext x; ring
    rw [he]
    exact hu.sub (seedCoordinateField_smooth n)
  have hs := (hb coeff).1
  obtain ⟨u,hus,hup,hval⟩ := seed_plus_compact_sphere_field v hv
    (hQ.of_isClosed_subset isClosed_closure hs) n
  exact ⟨u,hus,hup.trans (image_mono hs),hval⟩

end
end Yau.Target

end OAI

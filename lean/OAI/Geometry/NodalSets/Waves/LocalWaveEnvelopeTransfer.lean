import OAI.Geometry.NodalSets.Waves.LatticeSourceWaves
import OAI.Geometry.NodalSets.Waves.LocalCompactWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D : Set Coord} {m J K k0 : ℕ}

def LocalCompactWaveData.withEnvelope (b : LocalCompactWaveData g w S D m J K k0)
    (S' : Coord → ℝ) {O : Set Coord} (hO : IsOpen O) (hDO : D ⊆ O)
    (he : ∀ x ∈ O, S' =ᶠ[𝓝 x] S) : LocalCompactWaveData g w S' D m J K k0 where
  G := b.G
  W := b.W
  A := b.A
  E := b.E ∩ O
  smooth_G := b.smooth_G
  smooth_W := b.smooth_W
  smooth_A := b.smooth_A
  symmetric_G := b.symmetric_G
  positive_G := b.positive_G
  open_E := b.open_E.inter hO
  centers_E := fun _ hx ↦ ⟨b.centers_E hx,hDO hx⟩
  germ := fun x hx ↦ ⟨(b.germ x hx.1).1,(b.germ x hx.1).2.1,
    (b.germ x hx.1).2.2.trans (he x hx.2).symm⟩
  nonzero_gradient := b.nonzero_gradient
  cover := b.cover
  beams := b.beams
  estimates := local_source_wave_transfer g b.G w b.W S' b.A
    (fun t : b.cover.Parameter × Fin 3 ↦ coverSourceCenter b.cover t.1)
    ((continuous_coverSourceCenter b.cover).comp continuous_fst)
    (b.open_E.inter hO)
    (fun t ↦ ⟨b.centers_E (b.cover.center t.1).property,hDO (b.cover.center t.1).property⟩)
    (fun x hx ↦ ⟨(b.germ x hx.1).1,(b.germ x hx.1).2.1,
      (b.germ x hx.1).2.2.eq_of_nhds.trans (he x hx.2).eq_of_nhds.symm⟩)
    (fun n t ↦ b.beams.wave (n:ℝ) t) k0 K b.beams.c b.beams.Cw b.beams.Cr b.beams.R
    b.beams.Cw_pos b.beams.Cr_pos b.beams.estimates

lemma LocalCompactWaveData.withEnvelope_wave (b : LocalCompactWaveData g w S D m J K k0)
    (S' : Coord → ℝ) {O : Set Coord} (hO : IsOpen O) (hDO : D ⊆ O)
    (he : ∀ x ∈ O, S' =ᶠ[𝓝 x] S) {U : Set Coord} (hUD : U ⊆ D)
    (n : ℕ) (z : SourceGrid U n) (j : Fin 3) :
    latticeWave (b.withEnvelope S' hO hDO he).cover
      (b.withEnvelope S' hO hDO he).beams hUD n z j =
      latticeWave b.cover b.beams hUD n z j := rfl

lemma envelope_germ_open (S S' : Coord → ℝ) :
    IsOpen {x | S' =ᶠ[𝓝 x] S} := by
  change IsOpen {x | {z | S' z = S z} ∈ 𝓝 x}
  simpa only [← mem_interior_iff_mem_nhds, ofPred_mem_eq] using
    (isOpen_interior : IsOpen (interior {z | S' z = S z}))

end
end Yau.Geometry

end OAI

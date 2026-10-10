import OAI.Analysis.CircleDomains.Sobolev.SobolevHeightLevelNull
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! Fubini for the compact image of a pair of continuous coordinates. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem null_pair_image_of_null_level_images
    {F : Set ℂ} (hF : IsCompact F) {u v : ℂ → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hlevel : ∀ᵐ t ∂volume, volume (u '' (F ∩ {z | v z = t})) = 0) :
    volume ((fun z => (u z, v z)) '' F) = 0 := by
  have hcompact : IsCompact ((fun z => (u z, v z)) '' F) := hF.image (hu.prodMk hv)
  change (volume.prod volume) ((fun z => (u z, v z)) '' F) = 0
  rw [Measure.prod_apply_symm hcompact.measurableSet]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hlevel] with t ht
  have he : (fun x : ℝ => (x, t)) ⁻¹' ((fun z => (u z, v z)) '' F) =
      u '' (F ∩ {z | v z = t}) := by
    ext x
    constructor
    · rintro ⟨z, hz, he⟩
      exact ⟨z, ⟨hz, congrArg Prod.snd he⟩, congrArg Prod.fst he⟩
    · rintro ⟨z, ⟨hz, hvz⟩, huz⟩
      exact ⟨z, hz, Prod.ext huz hvz⟩
  change volume ((fun x : ℝ => (x, t)) ⁻¹' ((fun z => (u z, v z)) '' F)) = 0
  rwa [he]


 theorem sobolev_height_pair_null_image
    (hcoarea : PlanarSobolevCoarea)
    (ψ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (ψ n z).im) v atTop)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), V p = 0)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U univ) :
    volume ((fun z => (U (complexPlaneCoordinates.symm z), v z)) '' F) = 0 := by
  apply null_pair_image_of_null_level_images hF (hU.comp complexPlaneCoordinates.symm.continuous) hv
  exact sobolev_height_level_null_image hcoarea ψ hv hlim hw hLp hF hQ hFQ hz hU W

end CircleDomainRigidity

end

end OAI

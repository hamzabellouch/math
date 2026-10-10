import OAI.MeasureTheory.Falconer.Radial.PlanarAETubeGain
import OAI.MeasureTheory.Falconer.Angular.CappedActiveCover
import OAI.MeasureTheory.Falconer.Slicing.SliceIncidence

namespace OAI

/-! # Applying the published planar consequence to a selected original-label slice -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal Topology
variable {d h : ℕ} {κ : Type*}

def selectedActiveRelation (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
    (R T : ℝ) : Set (Space d × Sphere d) :=
  {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} ∩
    (gaussianPointBand A z δ ×ˢ gaussianDirectionBand A δ)

theorem selectedActiveRelation_measurable [Fintype κ] [DecidableEq κ]
    (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space d) (R T : ℝ) :
    MeasurableSet (selectedActiveRelation A z δ E J a R T) := by
  have hs := (gaussianActiveRelation_measurable E hE J hJ a R (ENNReal.ofReal T) true).preimage
    (show Measurable (fun u : Space d × Sphere d => ((A,z),u)) from by fun_prop)
  exact hs.inter ((gaussianPointBand_measurable A z δ).prod (gaussianDirectionBand_measurable A δ))

theorem planar_selected_slice_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (d h : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (A : Fin h → Space d) (z : Space h) (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2)
      (α : ProbabilityMeasure (Space d)) (β : ProbabilityMeasure (Sphere d))
      (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
      (M K T : ℝ),
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    0 ≤ M → 0 ≤ K → 0 ≤ T → T ≤ δ^(-b-η) →
    (∀ i, ‖A i‖ ≤ M) →
    (∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖) →
    K*((h:ℝ)*δ) < 1 →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ C*δ) →
    (∀ᵐ x ∂(α : Measure (Space d)), ‖x‖ ≤ 1/4) →
    (∀ᵐ w : Sphere d ∂(β : Measure (Sphere d)),
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
    (∀ c r, δ ≤ r → (α : Measure (Space d)).real
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ r} ≤ δ^(-η)*r^f) →
    (∀ c r, δ ≤ r → (β : Measure (Sphere d)).real
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ 2*r}
        ≤ δ^(-η)*r^b) →
    ((α : Measure (Space d)).prod (β : Measure (Sphere d))).real
      (selectedActiveRelation A z δ E J a (δ+(2*(1/4))*δ+(C*δ)*M) T) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_ae_tube_gain hpublished hb hb' hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall d h κ _ _ A z e α β E J a M K T hE hJ hM hK hT hTbound
    hA hbound hsmall hbounded hanchors hcover hα hβ hpball hqball
  let R := δ+(2*(1/4))*δ+(C*δ)*M
  let F := selectedActiveRelation A z δ E J a R T
  have hF : MeasurableSet F := selectedActiveRelation_measurable A z δ E hE J hJ a R T
  rw [← slice_iterated_incidence (α : Measure (Space d)) (β : Measure (Sphere d)) F hF]
  refine hgain δ hδ hδsmall (Space d) (Sphere d) α β
    (fun x => e ((gaussianRowMap A).ker.orthogonalProjectionOnto x))
    (fun w : Sphere d => normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
    (fun x w => (x,w) ∈ F) (by fun_prop)
    (by unfold NormedSpace.normalize; fun_prop) hF ?_ hβ hpball hqball κ
    (fun w => cappedActiveAnchors A z (J w) a R T)
    (fun i => e ((gaussianRowMap A).ker.orthogonalProjectionOnto (a i))) ?_ ?_
  · filter_upwards [hα] with x hx
    rw [e.norm_map]
    exact ((gaussianRowMap A).ker.norm_starProjection_apply_le x).trans hx
  · intro w
    exact (cappedActiveAnchors_card A z (J w) a R hT).trans hTbound
  · intro x w hx
    exact gaussian_capped_coordinate_cover A z e E J a hM hK hT hA hbound hsmall
      hbounded hanchors hcover hx.2.1 hx.2.2 hx.1

end Falconer

end OAI

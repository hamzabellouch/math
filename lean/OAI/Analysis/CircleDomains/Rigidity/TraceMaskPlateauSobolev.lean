import OAI.Analysis.CircleDomains.Rigidity.TraceMaskRectangle
import OAI.Analysis.CircleDomains.Sobolev.SobolevRepresentative

namespace OAI

/-! On a zero-cutoff neighborhood the primitive has a fixed endpoint.
Consequently its local Sobolev regularity does not require regularity of
the raw scalar, including point-to-disk component matches. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem fixed_endpoint_mask_rectangle_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {P : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p)
    {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (hP2 : MemLp P 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)))
    (hdom : ∀ n, ∀ᵐ p ∂volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂),
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    (a β : ℝ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p β) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
      ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
        |W.weakGrad z i| ≤ P (euclideanPlaneCoordinates z) := by
  simpa only [fderiv_const_apply,norm_zero,zero_add] using
    smooth_masked_scalar_rectangle_sobolev hs hc hI hIf
      (b := fun _ => β) contDiff_const hPm hP0 ha hb hP2 hdom a

 theorem plateau_mask_rectangle_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {P b : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p)
    {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (hP2 : MemLp P 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)))
    (hdom : ∀ n, ∀ᵐ p ∂volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂),
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    {j : ℕ} (hconv : OrdConnected (I j)) {β : ℝ} (hβ : β ∈ I j)
    (hlocal : ∀ p ∈ Ioo a₁ a₂ ×ˢ Ioo b₁ b₂, cutoff j p = 0 ∧ b p ∈ I j)
    (a : ℝ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
      ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
        |W.weakGrad z i| ≤ P (euclideanPlaneCoordinates z) := by
  obtain ⟨W,hW⟩ := fixed_endpoint_mask_rectangle_sobolev hs hc hI hIf hPm hP0 ha hb hP2 hdom a β
  have he : ((fun p => infiniteTracePrimitive cutoff I a p β) ∘ euclideanPlaneCoordinates) =ᵐ[
      volume.restrict (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂))]
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates) := by
    filter_upwards [ae_restrict_mem ((isOpen_Ioo.prod isOpen_Ioo).preimage
      euclideanPlaneCoordinates.continuous).measurableSet] with z hz
    exact (infiniteTracePrimitive_plateau hc hI hconv (hlocal _ hz).1 (hlocal _ hz).2 hβ a).symm
  exact ⟨W.congr_ae he,hW⟩

end CircleDomainRigidity

end

end OAI

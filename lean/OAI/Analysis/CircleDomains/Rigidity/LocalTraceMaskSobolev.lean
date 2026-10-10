import OAI.Analysis.CircleDomains.Sobolev.SmoothRectangleExtension
import OAI.Analysis.CircleDomains.Sobolev.SobolevRepresentative

namespace OAI

/-! The local mask witness uses only smoothness of the raw scalar on the
actual source open set; a compact cutoff constructs the auxiliary global
extension and its differential agrees on the requested rectangle. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_masked_scalar_rectangle_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {b : ℝ × ℝ → ℝ} (hb : ContDiffOn ℝ 1 b Ω)
    {P : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p)
    {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb' : b₁ ≤ b₂)
    (hbox : Icc a₁ a₂ ×ˢ Icc b₁ b₂ ⊆ Ω)
    (hP2 : MemLp P 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)))
    (hdom : ∀ n, ∀ᵐ p ∂volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂),
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    (a : ℝ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
      ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
        |W.weakGrad z i| ≤ ‖fderiv ℝ b (euclideanPlaneCoordinates z)‖+P (euclideanPlaneCoordinates z) := by
  obtain ⟨g,V,hg,_,hV,hKV,he,hde⟩ := exists_smooth_rectangle_extension hΩ
    (isCompact_Icc.prod isCompact_Icc) hbox hb
  obtain ⟨W,hW⟩ := smooth_masked_scalar_rectangle_sobolev hs hc hI hIf hg hPm hP0 ha hb' hP2 hdom a
  have hOV : Ioo a₁ a₂ ×ˢ Ioo b₁ b₂ ⊆ V :=
    (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans hKV
  have hmeas : MeasurableSet (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)) :=
    ((isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous).measurableSet
  have hE : ((fun p => infiniteTracePrimitive cutoff I a p (g p)) ∘ euclideanPlaneCoordinates) =ᵐ[
      volume.restrict (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂))]
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates) := by
    filter_upwards [ae_restrict_mem hmeas] with z hz
    simp only [Function.comp_apply,he (hOV hz)]
  refine ⟨W.congr_ae hE,?_⟩
  intro i
  filter_upwards [hW i,ae_restrict_mem hmeas] with z hz hzV
  simpa only [DeGiorgi.MemW1pWitness.congr_ae,hde (hOV hzV)] using hz

end CircleDomainRigidity

end

end OAI

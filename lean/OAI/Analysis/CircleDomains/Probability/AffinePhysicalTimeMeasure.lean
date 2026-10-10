import OAI.Analysis.CircleDomains.Modulus.AffinePhysicalArclength

namespace OAI

/-! Exact physical-domain time measure of a restricted path. The proof
identifies local arclength and the support in the open domain. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

def affineFinitePhysicalPath (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) : FinitePhysicalPath e y₀ :=
  ⟨affineRestrictedPath a b γ.val, physicalDomainLength_affine_finite e hU y₀ γ hab⟩

theorem physicalTimeLength_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    physicalTimeLength e y₀ (affineFinitePhysicalPath e hU y₀ γ hab) =
      ((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (rescalePathTime a b) := by
  symm
  apply physicalTimeLength_unique e hU y₀ (affineFinitePhysicalPath e hU y₀ γ hab)
  · change (((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (rescalePathTime a b))
      ((affineRestrictedPath a b γ.val) ⁻¹' U)ᶜ = 0
    have hmeas : MeasurableSet ((affineRestrictedPath a b γ.val) ⁻¹' U)ᶜ :=
      (hU.preimage (affineRestrictedPath a b γ.val).continuous).measurableSet.compl
    rw [Measure.map_apply (rescalePathTime a b).continuous.measurable hmeas,
      Measure.restrict_apply ((rescalePathTime a b).continuous.measurable hmeas)]
    apply measure_mono_null _ (physicalTimeLength_compl e hU y₀ γ)
    rintro t ⟨ht, htab⟩ hmem
    apply ht
    change γ.val (affinePathTime a b (rescalePathTime a b t)) ∈ U
    rwa [affine_rescalePathTime hab htab]
  · intro c d hcd hγ
    rw [Measure.restrict_map (rescalePathTime a b).continuous.measurable measurableSet_Icc,
      Measure.restrict_restrict ((rescalePathTime a b).continuous.measurable measurableSet_Icc),
      preimage_rescale_Icc hab,
      physicalTimeLength_restrict_compact e hU y₀ γ
        ((affinePathTime_strictMono hab).monotone hcd)
        (pathsInsideOn_affine_image hab γ.val hγ)]
    exact (physicalSubpath_affine_lengthCode e hU y₀ γ hab hcd hγ).symm

theorem physicalDomainLength_affine_eq (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    physicalDomainLength e y₀ (affineRestrictedPath a b γ.val) =
      physicalTimeLength e y₀ γ (Icc a b) := by
  change physicalDomainLength e y₀ (affineFinitePhysicalPath e hU y₀ γ hab).val = _
  rw [← physicalTimeLength_univ e y₀ (affineFinitePhysicalPath e hU y₀ γ hab),
    physicalTimeLength_affine e hU y₀ γ hab,
    Measure.map_apply (rescalePathTime a b).continuous.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

end CircleDomainRigidity

end

end OAI

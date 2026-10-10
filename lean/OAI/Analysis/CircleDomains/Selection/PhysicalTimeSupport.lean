import OAI.Analysis.CircleDomains.Modulus.DyadicTimeLength

namespace OAI

/-! The time arclength measure gives no mass to times outside the physical domain. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalStageTimeLength_compl (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    physicalStageTimeLength e y₀ n γ.val (γ.val ⁻¹' U)ᶜ = 0 := by
  classical
  have hm := (hU.preimage γ.val.continuous).measurableSet.compl
  simp only [physicalStageTimeLength, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hr := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hr ⊢
    rw [physicalSubpath_timeLength_portion e (dyadicLeft_le_right n i) _ hr,
      Measure.restrict_apply hm]
    have he : (γ.val ⁻¹' U)ᶜ ∩ Icc (dyadicLeft n i) (dyadicRight n i) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro t ⟨ht, hcell⟩
      exact ht (hi hcell)
    rw [he, measure_empty]
  · simp [physicalDyadicPath, totalPhysicalSubpath, hi, rectifiableLengthCode_const]

theorem physicalTimeLength_compl (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    physicalTimeLength e y₀ γ (γ.val ⁻¹' U)ᶜ = 0 := by
  rw [physicalTimeLength_apply _ _ _ (hU.preimage γ.val.continuous).measurableSet.compl]
  simp [physicalStageTimeLength_compl e hU y₀ γ]

theorem physicalTimeLength_ae_mem (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    ∀ᵐ t ∂physicalTimeLength e y₀ γ, γ.val t ∈ U := by
  rw [ae_iff]
  exact physicalTimeLength_compl e hU y₀ γ

end CircleDomainRigidity

end

end OAI

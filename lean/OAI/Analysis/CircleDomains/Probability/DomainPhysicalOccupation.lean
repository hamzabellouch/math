import OAI.Analysis.CircleDomains.Topology.DomainPhysicalPaths

namespace OAI

/-! On a path contained in the physical domain, the dyadic occupation
kernel is exactly ordinary arclength occupation, with multiplicity. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem physicalStageOccupation_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) (n : ℕ) :
    physicalStageOccupation e y₀ n (projectDomainPath e β.val hβ) = pathOccupation β := by
  have he (i : Fin (2 ^ n)) :
      rectifiableOccupationCode (physicalDyadicPath e y₀ n i (projectDomainPath e β.val hβ)) =
        pathPortionOccupation β (dyadicLeft n i) (dyadicRight n i) := by
    rw [physicalDyadicPath_project]
    change rectifiableOccupationCode (clippedPath β (dyadicLeft_le_right n i)).val = _
    rw [rectifiableOccupationCode_eq (clippedPath β (dyadicLeft_le_right n i)).property]
    exact pathOccupation_clipped β (dyadicLeft_le_right n i)
  ext E hE
  have hsum := congrArg (fun ν : Measure PathTime => ν (β.val ⁻¹' E))
    (sum_dyadic_restrict (pathLengthMeasure β) n)
  simp only [Measure.coe_finsetSum, Finset.sum_apply] at hsum
  simpa only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply, he,
    pathPortionOccupation, Measure.map_apply β.val.continuous.measurable hE,
    pathOccupation_apply β hE] using hsum

def finiteProjectedPhysicalPath (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) : FinitePhysicalPath e y₀ :=
  ⟨projectDomainPath e β.val hβ, by
    rw [physicalDomainLength_project]
    exact lt_top_iff_ne_top.mpr β.property⟩

theorem dyadicPhysicalOccupation_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) :
    dyadicPhysicalOccupation e y₀ (finiteProjectedPhysicalPath e y₀ β hβ) = pathOccupation β := by
  ext E hE
  rw [dyadicPhysicalOccupation_apply e y₀ _ hE]
  change (⨆ n, physicalStageOccupation e y₀ n (projectDomainPath e β.val hβ) E) = _
  simp only [physicalStageOccupation_project, iSup_const]

theorem lintegral_projectedPhysicalOccupation (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) {g : Y → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (finiteProjectedPhysicalPath e y₀ β hβ)) =
      ∫⁻ t, g (β.val t) ∂pathLengthMeasure β := by
  rw [dyadicPhysicalOccupation_project]
  exact lintegral_pathOccupation β hg

end CircleDomainRigidity

end

end OAI

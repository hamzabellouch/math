import OAI.Analysis.CircleDomains.Modulus.ReversedArclength
import OAI.Analysis.CircleDomains.Topology.AllowedPathReversal
import OAI.Analysis.CircleDomains.Topology.ReversedBoundaryTolls
import OAI.Analysis.CircleDomains.Modulus.InterleavedCollarCost

namespace OAI

/-! Time reversal preserves the actual dyadic physical occupation measure
and its weighted cost, including the endpoint conventions used in splicing. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem rectifiableOccupationCode_reversed (γ : C(PathTime, Y)) :
    rectifiableOccupationCode (reversedPath γ) = rectifiableOccupationCode γ := by
  have hiff : BoundedVariationOn (reversedPath γ) univ ↔ BoundedVariationOn γ univ := by
    change eVariationOn (reversedPath γ) univ ≠ ∞ ↔ eVariationOn γ univ ≠ ∞
    rw [variation_reversedPath]
  by_cases hγ : BoundedVariationOn γ univ
  · rw [rectifiableOccupationCode_eq (hiff.mpr hγ), rectifiableOccupationCode_eq hγ]
    exact pathOccupation_reversed ⟨γ, hγ⟩
  · simp only [rectifiableOccupationCode, dite_eq_right hγ, dite_eq_right (hiff.not.mpr hγ)]

def reversedFinitePhysicalPath {G : Set Y} {U : Set X} (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) : FinitePhysicalPath e y₀ :=
  ⟨reversedPath γ.val, by rw [physicalDomainLength_reversed]; exact γ.property⟩

theorem physicalStageOccupation_reversed {G : Set Y} {U : Set X} (e : G ≃ₜ U) (y₀ : Y)
    (γ : C(PathTime, X)) (n : ℕ) :
    physicalStageOccupation e y₀ n (reversedPath γ) = physicalStageOccupation e y₀ n γ := by
  unfold physicalStageOccupation
  simp_rw [physicalDyadicPath_reversed, rectifiableOccupationCode_reversed]
  exact Equiv.sum_comp (Fin.revPerm (n := 2 ^ n))
    (fun i => rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ))

theorem dyadicPhysicalOccupation_reversed {G : Set Y} {U : Set X} (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) :
    dyadicPhysicalOccupation e y₀ (reversedFinitePhysicalPath e y₀ γ) =
      dyadicPhysicalOccupation e y₀ γ := by
  ext S hS
  rw [dyadicPhysicalOccupation_apply e y₀ _ hS, dyadicPhysicalOccupation_apply e y₀ _ hS]
  simp only [reversedFinitePhysicalPath, physicalStageOccupation_reversed]

variable [MeasurableSpace C(PathTime, X)]

def reversedTaggedPhysicalPath (d : PathCodeData X Y) (Γ : TaggedPhysicalPath d) :
    TaggedPhysicalPath d :=
  (reversedFinitePhysicalPath d.domainEquiv d.basePoint Γ.1, fun k => reversedTag (Γ.2 k))

theorem physicalTollCost_reversed (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (γ : FinitePhysicalPath d.domainEquiv d.basePoint) :
    physicalTollCost d g m (reversedFinitePhysicalPath d.domainEquiv d.basePoint γ) =
      physicalTollCost d g m γ := by
  unfold physicalTollCost
  rw [dyadicPhysicalOccupation_reversed]
  exact congrArg _ (boundaryToll_reversed γ.val m)

end CircleDomainRigidity

end

end OAI

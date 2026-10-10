import OAI.Analysis.CircleDomains.Topology.DomainPathAdmissibility
import OAI.Analysis.CircleDomains.Probability.DyadicMeasurePartition

namespace OAI

/-! A rectifiable physical path entirely in the original domain projects
to an allowed quotient path, with exactly its original physical length. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

def projectDomainPath (e : G ≃ₜ U) (β : C(PathTime, Y)) (hβ : ∀ t, β t ∈ G) :
    C(PathTime, X) where
  toFun t := (e ⟨β t, hβ t⟩).val
  continuous_toFun := continuous_subtype_val.comp (e.continuous.comp (β.continuous.subtype_mk _))

theorem projectDomainPath_mem (e : G ≃ₜ U) (β : C(PathTime, Y)) (hβ : ∀ t, β t ∈ G)
    (t : PathTime) : projectDomainPath e β hβ t ∈ U := (e _).property

theorem physicalDyadicPath_project (e : G ≃ₜ U) (y₀ : Y)
    (β : C(PathTime, Y)) (hβ : ∀ t, β t ∈ G) (n : ℕ) (i : Fin (2 ^ n)) :
    physicalDyadicPath e y₀ n i (projectDomainPath e β hβ) =
      β.comp (timeClip (dyadicLeft n i) (dyadicRight n i)) := by
  have hi : projectDomainPath e β hβ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i) :=
    fun t _ => projectDomainPath_mem e β hβ t
  rw [physicalDyadicPath_of_mem e y₀ n i _ hi]
  ext t
  change (e.symm ⟨(e ⟨β (timeClip _ _ t), hβ _⟩).val, _⟩).val = β (timeClip _ _ t)
  exact congrArg Subtype.val (e.symm_apply_apply _)

theorem physicalStageLength_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) (n : ℕ) :
    physicalStageLength e y₀ n (projectDomainPath e β.val hβ) = eVariationOn β.val univ := by
  have he (i : Fin (2 ^ n)) :
      physicalDyadicLength e y₀ n i (projectDomainPath e β.val hβ) =
        pathLengthMeasure β (Icc (dyadicLeft n i) (dyadicRight n i)) := by
    rw [physicalDyadicLength, physicalDyadicPath_project, variation_timeClip _ (dyadicLeft_le_right n i),
      pathLengthMeasure_Icc β (dyadicLeft_le_right n i)]
  have hsum := congrArg (fun μ : Measure PathTime => μ univ) (sum_dyadic_restrict (pathLengthMeasure β) n)
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.restrict_apply_univ,
    pathLengthMeasure_univ] at hsum
  simpa only [physicalStageLength, he] using hsum

theorem physicalDomainLength_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) :
    physicalDomainLength e y₀ (projectDomainPath e β.val hβ) = eVariationOn β.val univ := by
  simp only [physicalDomainLength, physicalStageLength_project, iSup_const]

variable [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem projected_physical_path_allowed (d : PathCodeData X Y)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ d.physicalDomain) :
    AllowedTaggedPath d ν N (projectDomainPath d.domainEquiv β.val hβ, fun _ => inactiveTag) := by
  apply domainPath_allowed d hdisj ν N _ _ (projectDomainPath_mem d.domainEquiv β.val hβ)
  rw [physicalDomainLength_project]
  exact lt_top_iff_ne_top.mpr β.property

end CircleDomainRigidity

end

end OAI

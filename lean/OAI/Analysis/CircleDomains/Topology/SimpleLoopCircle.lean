import OAI.Analysis.CircleDomains.Topology.DiskCrossingInput
import OAI.Analysis.CircleDomains.Topology.JordanContours
import OAI.Analysis.CircleDomains.Probability.PathHitLaws

namespace OAI

/-! A closed path injective before its terminal time is a planar circle
embedding, to which the existing Schoenflies input applies. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def circleOfClosedPath {a : ℂ} (p : Path a a) : C(UnitAddCircle, ℂ) :=
  ⟨AddCircle.liftIco 1 0 p.extend,
    AddCircle.liftIco_zero_continuous (by simp) p.continuous_extend.continuousOn⟩

theorem circleOfClosedPath_apply {a : ℂ} (p : Path a a) (θ : UnitAddCircle) :
    circleOfClosedPath p θ = p ⟨unitCircleCut θ,
      (unitCircleCut_mem θ).1, (unitCircleCut_mem θ).2.le⟩ := by
  exact p.extend_apply ⟨(unitCircleCut_mem θ).1, (unitCircleCut_mem θ).2.le⟩

theorem circleOfClosedPath_injective {a : ℂ} (p : Path a a)
    (hp : ∀ s t : PathTime, s < 1 → t < 1 → p s = p t → s = t) :
    Injective (circleOfClosedPath p) := by
  intro θ φ h
  rw [circleOfClosedPath_apply, circleOfClosedPath_apply] at h
  have he := hp _ _ (unitCircleCut_mem θ).2 (unitCircleCut_mem φ).2 h
  apply unitCircleCut_injective
  exact congrArg (fun t : PathTime => (t : ℝ)) he

theorem circleOfClosedPath_range {a : ℂ} (p : Path a a) :
    range (circleOfClosedPath p) = range p := by
  apply Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    rw [circleOfClosedPath_apply]
    exact mem_range_self _
  · rintro _ ⟨t, rfl⟩
    by_cases ht : t < 1
    · refine ⟨((t : ℝ) : UnitAddCircle), ?_⟩
      rw [circleOfClosedPath_apply]
      congr 1
      apply Subtype.ext
      change unitCircleCut ((t : ℝ) : UnitAddCircle) = (t : ℝ)
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
        (show (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) from ⟨t.property.1, by simpa using ht⟩))
    · have ht1 : t = 1 := le_antisymm le_top (not_lt.mp ht)
      refine ⟨0, ?_⟩
      rw [ht1, p.target, circleOfClosedPath_apply]
      have hc : unitCircleCut (0 : UnitAddCircle) = 0 := by
        exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
          (show (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by constructor <;> norm_num))
      have he : (⟨unitCircleCut (0 : UnitAddCircle),
          (unitCircleCut_mem 0).1, (unitCircleCut_mem 0).2.le⟩ : PathTime) = 0 :=
        Subtype.ext hc
      rw [he, p.source]

theorem exists_schoenflies_of_simple_closed_path (hsch : PlanarSchoenflies)
    {a : ℂ} (p : Path a a)
    (hp : ∀ s t : PathTime, s < 1 → t < 1 → p s = p t → s = t) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : Circle,
      H z = circleOfClosedPath p ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z) := by
  exact hsch _ ((circleOfClosedPath p).continuous.comp
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous)
    ((circleOfClosedPath_injective p hp).comp
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.injective)

end CircleDomainRigidity

end

end OAI

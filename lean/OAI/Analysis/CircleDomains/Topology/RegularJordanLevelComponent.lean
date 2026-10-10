import OAI.Analysis.CircleDomains.Topology.CircleRealCharts
import OAI.Analysis.CircleDomains.Selection.OuterContours

namespace OAI

/-! A Jordan boundary lying in a regular scalar level is an open compact
connected component of that level, even if the rest of the level is unbounded. -/
open Set Function Filter
open scoped Topology Manifold ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_boundary_open_in_level (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    IsOpen {z : {w : ℂ // f w = t} | z.val ∈ frontier (jordanInterior H)} := by
  let := regularLevelChartedSpace hf ht
  let g : Circle → {w : ℂ // f w = t} := fun z =>
    ⟨H z, hlevel (by rw [frontier_jordanInterior]; exact mem_image_of_mem H z.property)⟩
  have hg : Continuous g := (H.continuous.comp continuous_subtype_val).subtype_mk _
  have hgi : Injective g := by
    intro z w he
    exact Subtype.val_injective (H.injective (congrArg Subtype.val he))
  have ho := (isOpenMap_circle_to_real_manifold hg hgi).isOpen_range
  have he : range g = {z : {w : ℂ // f w = t} | z.val ∈ frontier (jordanInterior H)} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [mem_ofPred_eq, frontier_jordanInterior]
      exact mem_image_of_mem H w.property
    · intro hz
      rw [mem_ofPred_eq, frontier_jordanInterior] at hz
      obtain ⟨w, hw, he⟩ := hz
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩
  rwa [he] at ho

end CircleDomainRigidity

end

end OAI

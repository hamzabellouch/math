import OAI.Analysis.CircleDomains.Probability.ClippedArcOccupation
import OAI.Analysis.CircleDomains.Modulus.PartialSimpleArcLength

namespace OAI

/-! A compact domain portion of an injective quotient path has exactly
the Hausdorff occupation of its physical lift. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem physical_simple_arc_portion_occupation
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) {a b : PathTime} (hab : a < b)
    (hγ : γ.val ∈ pathsInsideOn U a b) :
    rectifiableOccupationCode (physicalSubpath e hab.le ⟨γ.val, hγ⟩) =
      (μH[1] : Measure Y).restrict ((physicalValue e y₀ ∘ γ.val) '' Icc a b) := by
  let β : RectifiablePath Y := ⟨physicalSubpath e hab.le ⟨γ.val, hγ⟩,
    physicalSubpath_rectifiable e hU hab.le γ.val hγ y₀ γ.property⟩
  have hβ : InjOn β.val (Icc a b) := by
    intro s hs t ht heq
    apply physicalValue_path_injOn e y₀ γ.val hinj (hγ hs) (hγ ht)
    exact (physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ hs).trans
      (heq.trans (physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ ht).symm)
  have hclip : clippedPath β hab.le = β := by
    apply Subtype.ext
    exact physicalSubpath_comp_clip e hab.le ⟨γ.val, hγ⟩
  have himage : β.val '' Icc a b = (physicalValue e y₀ ∘ γ.val) '' Icc a b := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ ht⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, (physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ ht).symm⟩
  rw [rectifiableOccupationCode_eq β.property]
  change pathOccupation β = _
  rw [← hclip, clipped_simple_arc_occupation β hab hβ, himage]

end CircleDomainRigidity

end

end OAI

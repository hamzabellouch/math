import OAI.Analysis.CircleDomains.Modulus.AffineRectifiableLength
import OAI.Analysis.CircleDomains.Selection.AffinePhysicalRestriction

namespace OAI

/-! Exact arclength of a physical compact subpath after affine restriction.
Constant extension outside the subpath adds no endpoint mass. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalSubpath_affine_lengthCode (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    {c d : PathTime} (hcd : c ≤ d)
    (hγ : affineRestrictedPath a b γ.val ∈ pathsInsideOn U c d) :
    rectifiableLengthCode (physicalSubpath e hcd ⟨affineRestrictedPath a b γ.val, hγ⟩) =
      (rectifiableLengthCode (physicalSubpath e ((affinePathTime_strictMono hab).monotone hcd)
        ⟨γ.val, pathsInsideOn_affine_image hab γ.val hγ⟩)).map (rescalePathTime a b) := by
  let β : RectifiablePath Y :=
    ⟨physicalSubpath e ((affinePathTime_strictMono hab).monotone hcd)
      ⟨γ.val, pathsInsideOn_affine_image hab γ.val hγ⟩,
      physicalSubpath_rectifiable e hU _ γ.val _ y₀ γ.property⟩
  have hfun : physicalSubpath e hcd ⟨affineRestrictedPath a b γ.val, hγ⟩ =
      (affineRectifiablePath β hab).val := physicalSubpath_affine e hab γ.val hcd hγ
  have hportion : pathLengthMeasure β =
      (pathLengthMeasure β).restrict
        (Icc (affinePathTime a b c) (affinePathTime a b d)) := by
    have h := physicalSubpath_timeLength_portion e
      ((affinePathTime_strictMono hab).monotone hcd)
      ⟨γ.val, pathsInsideOn_affine_image hab γ.val hγ⟩ β.property
    rw [rectifiableLengthCode_eq β.property] at h
    exact h
  have hsub : Icc (affinePathTime a b c) (affinePathTime a b d) ⊆ Icc a b := by
    intro t ht
    exact ⟨(affinePathTime_mem_Icc hab.le c).1.trans ht.1,
      ht.2.trans (affinePathTime_mem_Icc hab.le d).2⟩
  have hsupport : (pathLengthMeasure β).restrict (Icc a b) = pathLengthMeasure β := by
    nth_rw 1 [hportion]
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_right.mpr hsub, ← hportion]
  rw [hfun, rectifiableLengthCode_eq (affineRectifiablePath β hab).property,
    pathLengthMeasure_affine, hsupport, rectifiableLengthCode_eq β.property]

end CircleDomainRigidity

end

end OAI

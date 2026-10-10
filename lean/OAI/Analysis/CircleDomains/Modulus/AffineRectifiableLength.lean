import OAI.Analysis.CircleDomains.Probability.AffineTimeMeasure
import OAI.Analysis.CircleDomains.Selection.AffineTagRestriction
import OAI.Analysis.CircleDomains.Modulus.PathLengthLocality

namespace OAI

/-! Exact arclength transformation of an affine restriction of a
rectifiable metric path. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def affineRectifiablePath (γ : RectifiablePath X) {a b : PathTime} (hab : a < b) :
    RectifiablePath X :=
  ⟨affineRestrictedPath a b γ.val,
    lt_top_iff_ne_top.mp ((eVariationOn.comp_le_of_monotoneOn γ.val (affinePathTime a b)
      ((affinePathTime_strictMono hab).monotone.monotoneOn _) (fun _ _ => mem_univ _)).trans_lt
        (lt_top_iff_ne_top.mpr γ.property))⟩

theorem pathLengthMeasure_affine_Icc (γ : RectifiablePath X) {a b : PathTime}
    (hab : a < b) {c d : PathTime} (hcd : c ≤ d) :
    pathLengthMeasure (affineRectifiablePath γ hab) (Icc c d) =
      pathLengthMeasure γ (Icc (affinePathTime a b c) (affinePathTime a b d)) := by
  rw [pathLengthMeasure_Icc _ hcd,
    pathLengthMeasure_Icc _ ((affinePathTime_strictMono hab).monotone hcd)]
  change eVariationOn (γ.val ∘ affinePathTime a b) (Icc c d) = _
  rw [eVariationOn.comp_eq_of_monotoneOn γ.val (affinePathTime a b)
    ((affinePathTime_strictMono hab).monotone.monotoneOn _),
    (affinePathTime a b).continuous.image_Icc_of_strictMono (affinePathTime_strictMono hab)]

theorem pathLengthMeasure_affine (γ : RectifiablePath X) {a b : PathTime} (hab : a < b) :
    pathLengthMeasure (affineRectifiablePath γ hab) =
      ((pathLengthMeasure γ).restrict (Icc a b)).map (rescalePathTime a b) := by
  apply Measure.ext_of_Icc
  intro c d hcd
  rw [pathLengthMeasure_affine_Icc γ hab hcd, map_rescale_restrict_Icc _ hab]

end CircleDomainRigidity

end

end OAI

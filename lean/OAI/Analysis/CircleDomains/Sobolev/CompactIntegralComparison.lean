import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! A finite measurable slice density is controlled almost everywhere
when all of its compact-set integrals are controlled. -/

open Set Filter MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

 theorem ae_le_of_compact_setLIntegral_le {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hfin : (∫⁻ x, f x) < ∞)
    (h : ∀ K : Set ℝ, IsCompact K → (∫⁻ x in K, f x) ≤ ∫⁻ x in K, g x) :
    f ≤ᵐ[volume] g := by
  let ν : Measure ℝ := volume.withDensity f
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin.ne
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf
  intro S hS _
  rw [← withDensity_apply f hS]
  change ν S ≤ _
  rw [hS.measure_eq_iSup_isCompact ν]
  apply iSup_le
  intro K
  apply iSup_le
  intro hKS
  apply iSup_le
  intro hK
  change (volume.withDensity f) K ≤ _
  rw [withDensity_apply f hK.measurableSet]
  exact (h K hK).trans (lintegral_mono_set hKS)

end CircleDomainRigidity

end OAI

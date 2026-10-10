import OAI.Analysis.ModularTheory.CovariantSlices
import OAI.Analysis.OperatorAlgebra.ScalarSliceContinuity
import OAI.Analysis.ModularTheory.CoreIntegrals

namespace OAI

/-! The bounded continuous operator kernel obtained by scalar convolution
of a modular fixed point. Its translation covariance is proved from the
actual right-action commutation relation. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularSliceKernel (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (s t : ℝ) : H →L[ℂ] H :=
  scalarOperatorSlice volume T (modularLpTranslate volume s f) (modularLpTranslate volume t g)

lemma modularSliceKernel_continuous
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous (fun p : ℝ × ℝ => modularSliceKernel T f g p.1 p.2) := by
  have hp : Continuous (fun p : ℝ × ℝ =>
      (modularLpTranslate volume p.1 f, modularLpTranslate volume p.2 g)) :=
    ((continuous_modularLpTranslate f).comp continuous_fst).prodMk
      ((continuous_modularLpTranslate g).comp continuous_snd)
  change Continuous ((fun p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ) =>
    scalarOperatorSlice volume T p.1 p.2) ∘
    (fun p : ℝ × ℝ => (modularLpTranslate volume p.1 f, modularLpTranslate volume p.2 g)))
  exact (scalarOperatorSlice_continuous volume T).comp hp

lemma modularSliceKernel_norm_le
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (s t : ℝ) :
    ‖modularSliceKernel T f g s t‖ ≤ ‖f‖ * ‖T‖ * ‖g‖ := by
  change ‖scalarOperatorSlice volume T (modularLpTranslate volume s f)
    (modularLpTranslate volume t g)‖ ≤ _
  have h := scalarOperatorSlice_norm_le volume T
    (modularLpTranslate volume s f) (modularLpTranslate volume t g)
  simpa only [LinearIsometry.norm_map] using h

lemma modularSliceKernel_mem (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ amplifiedModularAlgebra volume S)
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (s t : ℝ) :
    modularSliceKernel T f g s t ∈ S.M :=
  scalarOperatorSlice_mem_modular volume S T hT _ _

theorem modularSliceKernel_covariance (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : ∀ s f, T (modularRightTranslation volume S.D s f) =
      modularRightTranslation volume S.D s (T f))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (s t : ℝ) :
    modularSliceKernel T f g s t =
      S.sigma (-s) (modularSliceKernel T f g 0 (t - s)) := by
  have h := scalarOperatorSlice_modular_covariance volume S T hT f
    (modularLpTranslate volume (t - s) g) (-s)
  rw [neg_neg, modularLpTranslate_comp, show s + (t - s) = t by ring] at h
  simpa only [modularSliceKernel, modularLpTranslate_zero] using h

end WeakPureInfiniteness

end

end OAI

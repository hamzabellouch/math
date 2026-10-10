import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # Restricting L² vectors to a measurable stratum

The measure on a stratum is the comap of the restricted ambient measure.
The restriction operator uses the original representative and is contractive.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H]
  (μ : Measure X) (s : Set X) (hs : MeasurableSet s)

include hs

theorem l2RestrictMemLp (f : Lp H 2 μ) :
    MemLp (fun x : s => f x.val) 2 (Measure.comap ((↑) : s → X) μ) := by
  exact ((Lp.memLp f).mono_measure Measure.restrict_le_self).comp_measurePreserving
    (measurePreserving_subtype_coe hs)

def l2Restrict (f : Lp H 2 μ) : Lp H 2 (Measure.comap ((↑) : s → X) μ) :=
  (l2RestrictMemLp μ s hs f).toLp (fun x : s => f x.val)

theorem l2Restrict_apply_ae (f : Lp H 2 μ) :
    l2Restrict μ s hs f =ᵐ[Measure.comap ((↑) : s → X) μ] fun x : s => f x.val :=
  MemLp.coeFn_toLp (l2RestrictMemLp μ s hs f)

theorem l2Restrict_norm_le (f : Lp H 2 μ) : ‖l2Restrict μ s hs f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  rw [eLpNorm_congr_ae (l2Restrict_apply_ae μ s hs f)]
  calc
    _ = eLpNorm f 2 (μ.restrict s) :=
      eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f).restrict
        (measurePreserving_subtype_coe hs)
    _ ≤ eLpNorm f 2 μ := eLpNorm_mono_measure f Measure.restrict_le_self

 theorem l2Restrict_add (f g : Lp H 2 μ) :
    l2Restrict μ s hs (f + g) = l2Restrict μ s hs f + l2Restrict μ s hs g := by
  apply Lp.ext
  have ha := (measurePreserving_subtype_coe (μa := μ) hs).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (Lp.coeFn_add f g))
  filter_upwards [l2Restrict_apply_ae μ s hs (f + g), l2Restrict_apply_ae μ s hs f,
    l2Restrict_apply_ae μ s hs g,
    Lp.coeFn_add (l2Restrict μ s hs f) (l2Restrict μ s hs g), ha] with x hsum hf hg hr ha
  simp only [Pi.add_apply] at hr ha
  rw [hsum, hr, hf, hg]
  exact ha

variable [NormedSpace ℂ H]

 theorem l2Restrict_smul (c : ℂ) (f : Lp H 2 μ) :
    l2Restrict μ s hs (c • f) = c • l2Restrict μ s hs f := by
  apply Lp.ext
  have ha := (measurePreserving_subtype_coe (μa := μ) hs).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (Lp.coeFn_smul c f))
  filter_upwards [l2Restrict_apply_ae μ s hs (c • f), l2Restrict_apply_ae μ s hs f,
    Lp.coeFn_smul c (l2Restrict μ s hs f), ha] with x hsmul hf hr ha
  simp only [Pi.smul_apply] at hr ha
  rw [hsmul, hr, hf]
  exact ha

/-- The contractive linear restriction map to a measurable stratum. -/
def l2Restriction : Lp H 2 μ →L[ℂ] Lp H 2 (Measure.comap ((↑) : s → X) μ) :=
  LinearMap.mkContinuous {
    toFun := l2Restrict μ s hs
    map_add' := l2Restrict_add μ s hs
    map_smul' := l2Restrict_smul μ s hs } 1 (by
      intro f
      change ‖l2Restrict μ s hs f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using l2Restrict_norm_le μ s hs f)

end

end KadisonKastler

end OAI

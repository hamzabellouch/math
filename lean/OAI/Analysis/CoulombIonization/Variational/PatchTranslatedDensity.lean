import Mathlib
import OAI.Analysis.CoulombIonization.Variational.PatchBounded

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis

def translatedPatchDensity (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R))
    (x : TFSpace) : ℝ := boundedPatchRepresentative R B f (-y+x)

lemma translatedPatchDensity_measurable (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R)) :
    Measurable (translatedPatchDensity y R B f) :=
  (boundedPatchRepresentative_measurable R B f).comp (measurable_const.add measurable_id)

lemma translatedPatchDensity_nonneg (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    0 ≤ translatedPatchDensity y R B f x := boundedPatchRepresentative_nonneg R B f _

lemma translatedPatchDensity_le (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    translatedPatchDensity y R B f x ≤ max B 0 := boundedPatchRepresentative_le R B f _

lemma translatedPatchDensity_support (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R)) :
    Function.support (translatedPatchDensity y R B f) ⊆ closedBall y R := by
  intro x hx
  have hh := boundedPatchRepresentative_support R B f hx
  simpa only [mem_closedBall,dist_eq_norm,sub_zero,neg_add_eq_sub] using hh

lemma translatedPatchDensity_mass (y : TFSpace) {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ x, translatedPatchDensity y R B f x) = ∫ x, f x ∂ballMeasure R := by
  rw [←boundedPatchRepresentative_mass hf hb]
  exact (measurePreserving_add_left (volume : Measure TFSpace) (-y)).integral_comp
    (Homeomorph.addLeft (-y)).measurableEmbedding _

lemma translatedPatchDensity_kinetic (y : TFSpace) {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ x, (translatedPatchDensity y R B f x)^(5/3:ℝ)) = ‖f‖^(5/3:ℝ) := by
  rw [←boundedPatchRepresentative_kinetic hf hb]
  exact (measurePreserving_add_left (volume : Measure TFSpace) (-y)).integral_comp
    (Homeomorph.addLeft (-y)).measurableEmbedding (fun x => (boundedPatchRepresentative R B f x)^(5/3:ℝ))

lemma translatedPatchDensity_coulomb (y : TFSpace) {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ p : TFSpace × TFSpace, translatedPatchDensity y R B f p.1 *
      translatedPatchDensity y R B f p.2 / ‖p.1-p.2‖) = tfCoulombL R f f := by
  rw [←boundedPatchRepresentative_coulomb hf hb]
  have he := ((measurePreserving_add_left (volume : Measure TFSpace) (-y)).prod
    (measurePreserving_add_left (volume : Measure TFSpace) (-y))).integral_comp
    ((Homeomorph.addLeft (-y)).measurableEmbedding.prodMap (Homeomorph.addLeft (-y)).measurableEmbedding)
    (fun p : TFSpace × TFSpace => boundedPatchRepresentative R B f p.1 *
      boundedPatchRepresentative R B f p.2 / ‖p.1-p.2‖)
  simpa only [Measure.volume_eq_prod,Prod.map,translatedPatchDensity,
    add_sub_add_left_eq_sub] using he

lemma translatedPatchDensity_field (y : TFSpace) {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) (Φ : TFSpace → ℝ) :
    (∫ x, Φ x*translatedPatchDensity y R B f x) = ∫ x, Φ (y+x)*f x ∂ballMeasure R := by
  have he := (measurePreserving_add_left (volume : Measure TFSpace) y).integral_comp
    (Homeomorph.addLeft y).measurableEmbedding (fun x => Φ x*translatedPatchDensity y R B f x)
  simp only [translatedPatchDensity,neg_add_cancel_left] at he
  change (∫ x, Φ x * boundedPatchRepresentative R B f (-y+x)) = _
  rw [←he]
  exact boundedPatchRepresentative_field hf hb (fun x => Φ (y+x))

def physicalPatchMinimizer (y : TFSpace) (R T : ℝ) (hT : 0 < T)
    (Φ : Lp ℝ (5/2) (patchMeasure y R)) : TFLp (patchMeasure y R) :=
  patchPush y R (tfPatchMinimizer R T hT (patchPull y R Φ))

lemma physicalPatchMinimizer_nonneg (y : TFSpace) (R T : ℝ) (hT : 0 < T)
    (Φ : Lp ℝ (5/2) (patchMeasure y R)) : NonnegDensity (physicalPatchMinimizer y R T hT Φ) :=
  patchPush_nonneg y R (tfPatchMinimizer_nonneg R T hT _)

lemma physicalPatchMinimizer_min (y : TFSpace) (R T : ℝ) (hT : 0 < T)
    (Φ : Lp ℝ (5/2) (patchMeasure y R)) {g : TFLp (patchMeasure y R)} (hg : NonnegDensity g) :
    patchFunctional y R T Φ (physicalPatchMinimizer y R T hT Φ) ≤ patchFunctional y R T Φ g := by
  rw [←patchFunctional_pull,←patchFunctional_pull]
  simp only [physicalPatchMinimizer,patchPull_push]
  exact tfPatchMinimizer_min R T hT _ (patchPull_nonneg y R hg)

end CoulombAnalysis

end

end OAI

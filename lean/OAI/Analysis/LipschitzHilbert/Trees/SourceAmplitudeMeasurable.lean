import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceAmplitude
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionValues
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

/-! Measurability of the actual finite source packet amplitudes. The
angular cells and packet stopping levels are fixed; only the spatial
weights and packet values vary. Vanishing masses are allowed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem measurable_mass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (level : ℕ) (cell : ℤ) :
    Measurable (g.mass tops slope precision cutoff weight level cell) :=
  Finset.measurable_sum _ (fun t _ => hw t)

theorem measurable_boundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (base level : ℕ) (gap s : ℝ) :
    Measurable (g.boundaryMass tops slope precision cutoff weight base level gap s) :=
  Finset.measurable_sum _ (fun t _ => hw t)

theorem measurable_sourceBoundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (level : ℕ) (cell : ℤ) :
    Measurable (g.sourceBoundaryMass tops slope precision cutoff weight K gap level cell) :=
  g.measurable_boundaryMass tops slope precision cutoff weight hw _ _ _ _

theorem measurable_sourceTransition (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (phase : ℕ → ℂ) (level : ℕ) (cell : ℤ) :
    Measurable (fun x =>
      g.sourceTransition tops slope precision cutoff weight K gap phase x level cell) := by
  unfold sourceTransition analyticTransition
  exact (measurable_const.mul (Complex.measurable_ofReal.comp
    ((g.measurable_mass tops slope precision cutoff weight hw (level+1) cell).div
      (g.measurable_sourceBoundaryMass tops slope precision cutoff weight hw K gap level cell)).log)).cexp

theorem measurable_packetPathProduct (g : AngularGrid) (transition : X → ℕ → ℤ → ℂ)
    (ht : ∀ level cell, Measurable (fun x => transition x level cell))
    (lower upper : ℕ) (slope : ℝ) :
    Measurable (fun x => g.packetPathProduct (transition x) lower upper slope) :=
  Finset.measurable_prod _ (fun j _ => ht j _)

theorem measurable_sourcePacketBase (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (assigned : σ → ι) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (a : ℝ) (s : σ) :
    Measurable (fun x => g.sourcePacketBase tops slope precision cutoff weight assigned stop
      (value x) a x s) := by
  unfold sourcePacketBase
  exact (Complex.measurable_ofReal.comp
    ((g.measurable_mass tops slope precision cutoff weight hw _ _).pow_const (-a))).smul (hv s)

theorem measurable_sourcePacketAmplitude (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (phase : ℕ → ℂ)
    (a : ℝ) (level : ℕ) (cell : ℤ) :
    Measurable (fun x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x level cell) := by
  unfold sourcePacketAmplitude packetAmplitude
  apply Finset.measurable_sum
  intro s _
  exact (g.measurable_packetPathProduct _
    (g.measurable_sourceTransition tops slope precision cutoff weight hw K gap phase) _ _ _).smul
    (g.measurable_sourcePacketBase tops slope precision cutoff weight hw assigned stop value hv a s)

end AngularGrid

theorem measurable_sourcePredictionValue {X : Type*} {ι κ : Type} [MeasurableSpace X]
    [Fintype ι] [Fintype κ] (p μ : ℝ) (n : X → ℝ) (c : X → ι → ℝ)
    (A : X → ι → EuclideanSpace ℂ κ) (lam : X → ι → ℂ)
    (hn : Measurable n) (hc : ∀ i, Measurable (fun x => c x i))
    (hA : ∀ i, Measurable (fun x => A x i)) (hlam : ∀ i, Measurable (fun x => lam x i)) :
    Measurable (fun x => sourcePredictionValue p μ (n x) (c x) (A x) (lam x)) := by
  unfold sourcePredictionValue energyRatio
  fun_prop

end LipschitzHilbert

end

end OAI

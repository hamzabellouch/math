import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrials2
import OAI.Combinatorics.BalancedRyser.Probability.SlotProbability2

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace Balanced.FiniteUniform

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem measure_eq_product :
    (PMF.uniformOfFintype (I → A)).toMeasure = Slots.law (fun _ : I => A) := by
  rw [Slots.law_eq_uniformOn]
  apply Measure.ext_of_singleton
  intro f
  simp [uniformOn_univ]

theorem bounded_differences (Y : (I → A) → ℝ) (c : I → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hosc : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |Y x - Y y| ≤ c i)
    {L u : ℝ} (hI : 1 ≤ Fintype.card I) (hL : 0 < L)
    (hcL : ∀ i, c i ≤ L) (hu : 0 < u) :
    (PMF.uniformOfFintype (I → A)).toMeasure.real
      {f | u ≤ |Y f - ∫ g, Y g ∂(PMF.uniformOfFintype (I → A)).toMeasure|} ≤
      2 * Real.exp (-(u ^ 2) / (8 * (Fintype.card I : ℝ) * L ^ 2)) := by
  classical
  let e := Fintype.equivFin I
  let μ := (PMF.uniformOfFintype (I → A)).toMeasure
  let ξ : Fin (Fintype.card I) → (I → A) → A := fun i f => f (e.symm i)
  let Z : (Fin (Fintype.card I) → A) → ℝ := fun x => Y (fun i => x (e i))
  have hξ : ∀ i, Measurable (ξ i) := fun i => measurable_pi_apply _
  have hind : iIndepFun ξ μ := by
    dsimp [μ]
    rw [measure_eq_product]
    exact (Slots.independent_coordinates (V := fun _ : I => A)).precomp e.symm.injective
  have hosc' : IndependentTrials.CoordinateOscillation Z (fun i => c (e.symm i)) := by
    intro i x y hxy
    apply hosc (e.symm i)
    intro j hj
    apply hxy (e j)
    intro heq
    apply hj
    exact e.injective (by simpa using heq)
  have hZ (f : I → A) : Z (IndependentTrials.trialVector ξ f) = Y f := by
    simp [Z, IndependentTrials.trialVector, ξ]
  have ht := independentTrialJumps_proof (Fintype.card I) (I → A) inferInstance μ
    (fun _ => A) (fun _ => inferInstance) ξ hξ Z (measurable_of_countable Z)
    hind Integrable.of_finite (fun i => c (e.symm i)) (fun i => hc _) hosc'
  have htail := ht.2.2.2 L u hI hL (fun i => hcL _) hu
  simpa only [hZ] using htail

end Balanced.FiniteUniform

end

end OAI

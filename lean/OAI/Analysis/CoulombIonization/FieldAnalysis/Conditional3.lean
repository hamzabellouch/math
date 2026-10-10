import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.Conditional2
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierForgottenInvariantBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialInvariantBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis
section Conditional
variable {Ω D : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable [MeasurableSpace D] (P : Measure Ω) [IsProbabilityMeasure P]
variable (X : Ω → D) (hX : Measurable X)

lemma conditionalField_plus_const {u : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (c : ℝ) (d : D) (x : TFSpace) :
    c+conditionalField P X u d x = ∫ sample, c+u sample x ∂condDistrib id X P d := by
  rw [integral_add (integrable_const c) (deterministicBound_integrable_section hm hb x)]
  simp [conditionalField]

lemma conditionalField_le {u : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (c b : ℝ) (d : D) (x : TFSpace) (h : ∀ sample, c+u sample x ≤ b) :
    c+conditionalField P X u d x ≤ b := by
  rw [conditionalField_plus_const P X hm hb c d x]
  calc
    _ ≤ ∫ _ : Ω, b ∂condDistrib id X P d := integral_mono
      ((integrable_const c).add (deterministicBound_integrable_section hm hb x)) (integrable_const b) h
    _ = b := by simp

lemma le_conditionalField {u : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (c b : ℝ) (d : D) (x : TFSpace) (h : ∀ sample, b ≤ c+u sample x) :
    b ≤ c+conditionalField P X u d x := by
  rw [conditionalField_plus_const P X hm hb c d x]
  calc
    b = ∫ _ : Ω, b ∂condDistrib id X P d := by simp
    _ ≤ _ := integral_mono (integrable_const b)
      ((integrable_const c).add (deterministicBound_integrable_section hm hb x)) h

include hX

theorem IsNuclearBarrier.forget {μ a p : Ω → TFSpace → ℝ} {Z κ B C R T η : ℝ}
    (old : IsNuclearBarrier P μ Z κ B C R T η a p) (hR : 0 < R) (hκ : 0 ≤ κ)
    (hμm : Measurable (Function.uncurry μ)) (hμb : DeterministicLocalBound μ) :
    IsNuclearBarrier P (fun sample => conditionalField P X μ (X sample)) Z κ B C R T η
      (fun sample => conditionalField P X a (X sample)) (fun sample => conditionalField P X p (X sample)) := by
  obtain ⟨L,hpL⟩ := old.bounded_error
  have hpb := nonneg_bounded_deterministicBound old.nonneg_error hpL
  have hpm := old.measurable_error
  have ham := old.measurable_offset
  have hab := old.bound_offset
  refine ⟨(conditionalField_measurable P X ham).comp ((hX.comp measurable_fst).prodMk measurable_snd),
    (conditionalField_deterministicLip P X ham hab old.uniform_lipschitz_offset).comp X,
    (conditionalField_bound P X hab).comp X,
    (conditionalField_measurable P X hpm).comp ((hX.comp measurable_fst).prodMk measurable_snd),
    (fun sample x => conditionalField_nonneg P X old.nonneg_error (X sample) x),⟨L,?_⟩,
    (fun sample x hx => conditionalField_support P X old.support_error (X sample) x hx),?_,?_,?_,?_,?_⟩
  · intro sample x
    simpa only [zero_add] using conditionalField_le P X hpm hpb 0 L (X sample) x (fun t => by simpa using hpL t x)
  · have hw := weak_nuclear_conditional P X hX Z (g := fun sample => innerSource R (μ sample) (p sample)) ham hab
      (ae_of_all _ (fun sample => (old.locallyLipschitz_offset sample).continuous))
      (innerSource_measurable hμm hpm R) (innerSource_bound hμb hpb R)
      (outerCoefficient_measurable R) (outerCoefficient_bound R) (outerCoefficient_nonneg R)
      hR hκ (outerCoefficient_zero R) old.weak
    filter_upwards [ae_of_ae_map hX.aemeasurable hw] with sample hω
    apply hω.congr_source
    intro x _
    rw [conditionalField_innerSource P X hμm hμb hpm hpb R]
  · intro sample x hx
    exact le_conditionalField P X ham hab _ _ (X sample) x (fun t => old.lower t x hx)
  · intro sample x hx
    exact conditionalField_le P X ham hab _ _ (X sample) x (fun t => old.upper t x hx)
  · intro sample x hx
    apply le_antisymm
    · exact conditionalField_le P X ham hab _ _ (X sample) x (fun t => (old.tail t x hx).le)
    · exact le_conditionalField P X ham hab _ _ (X sample) x (fun t => (old.tail t x hx).ge)
  · rw [conditionalField_totalMass P X hX hpm hpb old.support_error]
    exact old.mass

end Conditional

lemma IsNuclearBarrier.congr_density {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ ν a p : Ω → TFSpace → ℝ} {Z κ B C R T η : ℝ}
    (old : IsNuclearBarrier P μ Z κ B C R T η a p) (he : ∀ᵐ sample ∂P, ∀ x, μ sample x = ν sample x) :
    IsNuclearBarrier P ν Z κ B C R T η a p := by
  refine ⟨old.measurable_offset,old.uniform_lipschitz_offset,old.bound_offset,
    old.measurable_error,old.nonneg_error,old.bounded_error,old.support_error,?_,
    old.lower,old.upper,old.tail,old.mass⟩
  filter_upwards [old.weak,he] with sample hw he
  apply hw.congr_source
  intro x _
  simp only [innerSource,he x]

end CoulombBarrier

end

end OAI

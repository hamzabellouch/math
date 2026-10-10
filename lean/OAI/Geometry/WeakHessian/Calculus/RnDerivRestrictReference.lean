import Mathlib
import OAI.Geometry.WeakHessian.Entropy.FiniteEntropy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

lemma rnDeriv_restrict_reference {m μ : Measure X} [SigmaFinite m] [SigmaFinite μ]
    {Q : Set X} (hQ : MeasurableSet Q) :
    μ.rnDeriv m =ᵐ[m.restrict Q] μ.rnDeriv (m.restrict Q) := by
  have hs : m.restrict Q ⟂ₘ m.restrict Qᶜ := by
    refine ⟨Qᶜ,hQ.compl,?_,?_⟩ <;> simp [Measure.restrict_apply,hQ,hQ.compl]
  have H := Measure.rnDeriv_add_right_of_mutuallySingular (μ := μ) hs
  simpa only [Measure.restrict_add_restrict_compl hQ] using H

lemma rnDeriv_restrict_reference_ae {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hac : μ ≪ m) (hs : ∀ᵐ x ∂μ, x ∈ Q) :
    μ.rnDeriv m =ᵐ[μ] μ.rnDeriv (m.restrict Q) :=
  (absolutelyContinuous_restrict_of_ae_mem hac hs).ae_eq (rnDeriv_restrict_reference hQ)

lemma renyiIntegral_restrict_reference {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hs : ∀ᵐ x ∂μ, x ∈ Q) {N : ℝ} (hN : 1 < N) :
    renyiIntegral m μ N = renyiIntegral (m.restrict Q) μ N := by
  have hp : 0 < 1-1/N := by rw [sub_pos,div_lt_one (by linarith : 0<N)]; exact hN
  have hz : μ.rnDeriv m =ᵐ[m.restrict Qᶜ] 0 := by
    apply (lintegral_eq_zero_iff (Measure.measurable_rnDeriv μ m)).mp
    exact le_antisymm ((Measure.setLIntegral_rnDeriv_le Qᶜ).trans_eq
      (ae_iff.mp hs)) bot_le
  have Hzero : (∫⁻ x in Qᶜ, (μ.rnDeriv m x)^(1-1/N) ∂m) = 0 := by
    apply (lintegral_eq_zero_iff ((Measure.measurable_rnDeriv μ m).pow_const _)).mpr
    filter_upwards [hz] with x hx
    simp only [hx,Pi.zero_apply,ENNReal.zero_rpow_of_pos hp]
  unfold renyiIntegral
  rw [← lintegral_add_compl _ hQ,Hzero,add_zero]
  exact lintegral_congr_ae ((rnDeriv_restrict_reference (μ := μ) hQ).mono fun x hx => congrArg (fun z : ℝ≥0∞ => z^(1-1/N)) hx)

lemma finiteEntropy_restrict_reference_iff {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hs : ∀ᵐ x ∂μ, x ∈ Q) :
    FiniteEntropy (m.restrict Q) μ ↔ FiniteEntropy m μ := by
  constructor
  · rintro ⟨hac,hi⟩
    have hac' : μ ≪ m := hac.trans (Measure.restrict_le_self.absolutelyContinuous)
    exact ⟨hac',hi.congr (llr_restrict_right_of_ae_mem hQ hac' hs)⟩
  · rintro ⟨hac,hi⟩
    exact ⟨absolutelyContinuous_restrict_of_ae_mem hac hs,
      hi.congr (llr_restrict_right_of_ae_mem hQ hac hs).symm⟩

lemma entropyReal_restrict_reference {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hac : μ ≪ m) (hs : ∀ᵐ x ∂μ, x ∈ Q) :
    entropyReal (m.restrict Q) μ = entropyReal m μ :=
  integral_congr_ae (llr_restrict_right_of_ae_mem hQ hac hs)
end WeakHessian

end
end InlinedFile0

end OAI

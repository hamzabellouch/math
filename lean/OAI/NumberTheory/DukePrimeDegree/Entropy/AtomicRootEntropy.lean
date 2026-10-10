import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingAtomicProduct
import OAI.NumberTheory.DukePrimeDegree.Entropy.ObservationInformation

namespace OAI

/-! # Vanishing transverse conditional entropy for atomic root products -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationEntropy_dirac_eq_zero {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype α] (y : Y) (Q : Y → α) :
    observationEntropy (Measure.dirac y) Q = 0 := by
  classical
  unfold observationEntropy finiteShannon
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : Q y=a <;> simp [Measure.dirac_real_apply,ha]

theorem conditionalSigmaEntropy_nonneg {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (P : Y → α) (m : MeasurableSpace Y) :
    0 ≤ conditionalSigmaEntropy (mY := mY) μ P m := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_all_iff.mpr (fun a =>
    conditionalProbability_unit_bounds (mY := mY) μ {z | P z=a} m)] with z hz
  exact Finset.sum_nonneg fun a _ => Real.negMulLog_nonneg (hz a).1 (hz a).2

namespace RootPrefixBox
variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) P₀ T} {g : G (d+1)}

theorem conditionalEntropy_fst_eq_zero_of_atomic_roots
    (A : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (h : ∀ p : ↥(allPositiveRoots (d+1) \ P₀), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0)
    {α : Type*} [Fintype α]
    (Q : (UpperRootTransverse (d+1) × T) × c.Time → α)
    (hQ : ∀ a, MeasurableSet {z | Q z=a}) :
    conditionalSigmaEntropy (A.coordinateMeasure μ) Q
      (MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace (UpperRootTransverse (d+1) × T))) = 0 := by
  rw [conditionalSigmaEntropy_fst (A.coordinateMeasure μ) Q hQ]
  have he := integral_map (μ := A.coordinateMeasure μ) measurable_fst.aemeasurable
    (measurable_fiber_observationEntropy (A.conditionalKernel μ) Q hQ).aestronglyMeasurable
  calc
    _ = ∫ z, observationEntropy (A.conditionalKernel μ z.1) (fun t => Q (z.1,t))
        ∂A.coordinateMeasure μ := he
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [A.ae_conditionalKernel_eq_dirac_of_atomic_roots R hAR μ h] with z hz
      simp only [hz,observationEntropy_dirac_eq_zero,Pi.zero_apply]

theorem conditionalEntropy_eq_zero_of_atomic_roots
    (A : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (h : ∀ p : ↥(allPositiveRoots (d+1) \ P₀), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0)
    {α : Type*} [Fintype α]
    (Q : (UpperRootTransverse (d+1) × T) × c.Time → α)
    (hQ : ∀ a, MeasurableSet {z | Q z=a})
    (m : MeasurableSpace ((UpperRootTransverse (d+1) × T) × c.Time))
    (hm : m ≤ Prod.instMeasurableSpace)
    (hfst : MeasurableSpace.comap Prod.fst
      (inferInstance : MeasurableSpace (UpperRootTransverse (d+1) × T)) ≤ m) :
    conditionalSigmaEntropy (mY := Prod.instMeasurableSpace) (A.coordinateMeasure μ) Q m = 0 := by
  apply le_antisymm
  · exact (conditionalSigmaEntropy_antitone (mY := Prod.instMeasurableSpace)
      (A.coordinateMeasure μ) Q hQ hfst hm).trans_eq
        (A.conditionalEntropy_fst_eq_zero_of_atomic_roots R hAR μ h Q hQ)
  · exact conditionalSigmaEntropy_nonneg (mY := Prod.instMeasurableSpace)
      (A.coordinateMeasure μ) Q m

end RootPrefixBox
end DukePrimeDegree

end

end OAI

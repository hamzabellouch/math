import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-! # Volume lower bounds from a controlled finite injective cover

This is the change-of-variables step for measurable polynomial parameters.
The parameter set itself need not contain an open set. When it is compact,
the image used below is a compact witness for inner volume.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem volume_image_lower_of_finite_injective_cover
    {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (f : V → V) (df : V → V →L[ℝ] V)
    {K : Set V} (hK : MeasurableSet K) (s : Finset I) (U : I → Set V)
    (hU : ∀ i ∈ s, MeasurableSet (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i)
    (hdf : ∀ x ∈ K, HasFDerivAt f (df x) x)
    (hinj : ∀ i ∈ s, Set.InjOn f (K ∩ U i))
    (η : ℝ≥0) (hdet : ∀ x ∈ K, (η : ℝ) ≤ |(df x).det|) :
    (η : ℝ≥0∞) * μ K ≤ (s.card : ℝ≥0∞) * μ (f '' K) := by
  classical
  have hcover' : K ⊆ ⋃ i ∈ s, K ∩ U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨i, hi, hx, hxi⟩
  have hmass : μ K ≤ ∑ i ∈ s, μ (K ∩ U i) :=
    (measure_mono hcover').trans (measure_biUnion_finset_le s (fun i => K ∩ U i))
  calc
    (η : ℝ≥0∞) * μ K ≤ η * ∑ i ∈ s, μ (K ∩ U i) := mul_le_mul' le_rfl hmass
    _ = ∑ i ∈ s, (η : ℝ≥0∞) * μ (K ∩ U i) := by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ s, μ (f '' K) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (η : ℝ≥0∞) * μ (K ∩ U i) = ∫⁻ _x in K ∩ U i, (η : ℝ≥0∞) ∂μ := by simp
        _ ≤ ∫⁻ x in K ∩ U i, ENNReal.ofReal |(df x).det| ∂μ := by
          apply setLIntegral_mono' (hK.inter (hU i hi))
          intro x hx
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (hdet x hx.1)
        _ = μ (f '' (K ∩ U i)) :=
          lintegral_abs_det_fderiv_eq_addHaar_image μ (hK.inter (hU i hi))
            (fun x hx => (hdf x hx.1).hasFDerivWithinAt) (hinj i hi)
        _ ≤ μ (f '' K) := measure_mono (image_mono inter_subset_left)
    _ = (s.card : ℝ≥0∞) * μ (f '' K) := by simp

end PolycyclicRecognition

end

end OAI

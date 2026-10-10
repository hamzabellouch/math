import OAI.Probability.InvariantIsing.Magnetic.RestrictedEndpointTest
import OAI.Probability.InvariantIsing.Magnetic.RestrictedBlockOverlap

namespace OAI

/-! Root averaging for the constrained published endpoint law, preserving
its actual shared-prefix spin means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_common_level_root_integral {N : ℕ} (h : FieldStep)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (a : Fin (h.depth + 1) → (Fin N → ℝ) → ℝ)
    (ha : ∀ i, Measurable (a i)) {C : ℝ} (hb : ∀ i z, |a i z| ≤ C) :
    (∫ z, ∫ α, a (fieldCommonLevel h α) z
      ∂cascadeReplicaLaw h.depth (chainExponent h.cut) ∂μ) =
      ∫ s, ∫ z, a (fieldLevelIndex h s) z ∂μ ∂pathMeasure := by
  let ν := cascadeReplicaLaw h.depth (chainExponent h.cut)
  have ham' : Measurable (fun p : Fin (h.depth + 1) × (Fin N → ℝ) => a p.1 p.2) :=
    measurable_from_prod_countable_right ha
  have hp : Measurable (fun p : (Fin N → ℝ) × (ℕ → LabeledLeaf h.depth) =>
      (fieldCommonLevel h p.2, p.1)) :=
    ((measurable_fieldCommonLevel h).comp measurable_snd).prodMk measurable_fst
  have hai : Integrable (fun p : (Fin N → ℝ) × (ℕ → LabeledLeaf h.depth) =>
      a (fieldCommonLevel h p.2) p.1) (μ.prod ν) := by
    apply Integrable.of_bound (ham'.comp hp).aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hb (fieldCommonLevel h p.2) p.1)
  rw [integral_integral_swap hai]
  exact fieldCommonLevel_integral h (fun i => ∫ z, a i z ∂μ)

theorem restricted_field_published_rooted_coordinate_test
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    (∫ z, restrictedFieldTiltedPairMean S h z (restrictedEndpointCoordinateTest S h q Φ j)
      ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) =
      ∫ s, Φ (q (fieldLevelIndex h s)) *
        (∫ z, restrictedPairCoordinateMean hN S hS h.depth (chainExponent h.cut)
          (fieldStepVariance h)
          (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1)
          (fieldLevelIndex h s) j z
          ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)))
        ∂pathMeasure := by
  let a := fun i z => Φ (q i) * restrictedPairCoordinateMean hN S hS h.depth
    (chainExponent h.cut) (fieldStepVariance h)
    (fun l hl => ((chainExponent_admissible h.ordered_cut h.first h.last).1 l hl).1) i j z
  have ha : ∀ i, Measurable (a i) := fun i =>
    (measurable_restrictedPairCoordinateMean hN S hS _ _ _ _ i j).const_mul _
  have hb : ∀ i z, |a i z| ≤ C := by
    intro i z
    rw [show a i z = Φ (q i) * _ from rfl, abs_mul]
    exact (mul_le_mul_of_nonneg_left (restrictedPairCoordinateMean_bound hN S hS _ _ _ _ i j z)
      (abs_nonneg _)).trans (by simpa only [mul_one] using hΦ _)
  simp_rw [restricted_field_published_coordinate_test hpub hN S hS h q Φ j hΦ]
  rw [field_common_level_root_integral h _ a ha hb]
  simp only [a, integral_const_mul]

end InvariantIsing

end

end OAI

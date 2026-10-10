import OAI.Probability.InvariantIsing.Fields.SpinPriorFieldRecursion
import OAI.Probability.InvariantIsing.Fields.SpinPriorProfileVariance
import OAI.Probability.InvariantIsing.Fields.SpinPriorContactMinimum
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldLogNormalizer
import OAI.Probability.InvariantIsing.Fields.FieldLogMean

namespace OAI

/-! Exact zero-temperature constrained field value, including the finite
constraint's probability normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma spinPriorMeanPressure_field (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m k : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (r : Fin k → ℕ)
    (h : FieldStep) :
    spinPriorMeanPressure (n := h.depth) μ π (fun _ => 0) (fun _ => 0) I degree 0
      (chainExponent h.cut) r (heightSequence h) =
      (N : ℝ)⁻¹ * (∫ z, cascadeRecursion h.depth (chainExponent h.cut)
        (fun i => vectorGaussianLaw N (fieldStepVariance h i)) (fun _ p => p.1+p.2)
        (fun y => finiteLogIntegral π (fieldEnergy y)) z
        ∂(vectorGaussianLaw N ⟨h.height 0,h.nonneg 0⟩ : Measure (Fin N → ℝ))) -
      h.height (Fin.last h.depth)/2 := by
  let b := chainExponent h.cut
  let v := fun i => tensorPathProfile I degree h.depth r (heightSequence h) i
  let P := (μ.prod (labeledCascadeLaw h.depth b : Measure (LabeledTree h.depth))).prod gaussianCoordinates
  let F := spinPriorJointFlatLog (n := h.depth) π (fun _ => 0) (fun _ => 0) I degree 0 (fun i => v i)
  have hb := chainExponent_admissible h.ordered_cut h.first h.last
  obtain ⟨C,hC,hvar⟩ := spinPriorJointFlatLog_variance hhaar hgauss
  have hi : Integrable F P := (hvar N hN μ inferInstance hμ π inferInstance m k h.depth
    (fun _ => 0) (fun _ => 0) 1 (by norm_num) (by intro i; norm_num) I degree 0 b hb
    (fun i => varianceIncrement (heightSequence h) i)
    (fun i j => varianceIncrement (monomialPath h.depth (r j)) i)).1.integrable (by norm_num)
  have hl := (spinPriorProfileLog_law (n := h.depth) μ π (fun _ => 0) (fun _ => 0) I degree 0 b (fun i => v i)).integral_eq
  have hmap : (∫ x : ℝ, x ∂P.map F) = ∫ p, F p ∂P := integral_map (μ := P) (φ := F)
    (measurable_spinPriorJointFlatLog (n := h.depth) π (fun _ => 0) (fun _ => 0)
      I degree 0 (fun i => v i)).aemeasurable aestronglyMeasurable_id
  have hl' := hl.trans hmap
  change (∫ p, spinPriorNamespacedLog π (fun _ => 0) (fun _ => 0) I degree 0 r
    (heightSequence h) p ∂P)=∫ p, F p ∂P at hl'
  unfold spinPriorMeanPressure
  rw [hl', integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  have hsec U : Integrable (spinPriorFlatLog π (fun _ => 0) (specialRotation U)
      (fun _ => 0) I degree 0 h.depth v)
      ((labeledCascadeLaw h.depth b : Measure (LabeledTree h.depth)).prod gaussianCoordinates) :=
    (spinPriorFlatLog_variance hgauss (by omega) π (fun _ => 0) (specialRotation U) (fun _ => 0)
      I degree 0 h.depth b (fun i => varianceIncrement (heightSequence h) i)
      (fun i j => varianceIncrement (monomialPath h.depth (r j)) i) hb).1.integrable (by norm_num)
  have he U := spinPriorFlatLog_field_integral hgauss (by omega) π (specialRotation U)
    I degree h.depth b hb r (heightSequence h)
  have hm : (∫ U, ∫ T, ∫ z, F ((U,T),z) ∂gaussianCoordinates
      ∂(labeledCascadeLaw h.depth b : Measure (LabeledTree h.depth)) ∂μ) =
      ∫ z, cascadeRecursion h.depth b (fun i => vectorGaussianLaw N (varianceIncrement (heightSequence h) (i+1)))
        (fun _ p => p.1+p.2) (fun y => finiteLogIntegral π (fieldEnergy y)) z
        ∂(vectorGaussianLaw N (varianceIncrement (heightSequence h) 0) : Measure (Fin N → ℝ)) := by
    have he' U : (∫ T, ∫ z, F ((U,T),z) ∂gaussianCoordinates
        ∂(labeledCascadeLaw h.depth b : Measure (LabeledTree h.depth))) = _ :=
      (integral_prod _ (hsec U)).symm.trans (he U)
    simp_rw [he']
    simp
  rw [hm]
  simp_rw [varianceIncrement_heightSequence, varianceIncrement_heightSequence_zero,
    ← fieldStepVariance_eq_fieldCascadeVariance]
  have he : (⟨h.height 0,h.nonneg 0⟩ : ℝ≥0)=NNReal.mk (h.height 0) (h.nonneg 0) := by
    apply Subtype.ext
    rfl
  rw [he, heightSequence_eq h h.depth le_rfl]
  rfl

lemma spinPriorMeanPressure_restricted_field (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m k : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (r : Fin k → ℕ)
    (h : FieldStep) :
    spinPriorMeanPressure (n := h.depth) μ (restrictedSpinPrior S hS : Measure (Spin N))
      (fun _ => 0) (fun _ => 0) I degree 0 (chainExponent h.cut) r (heightSequence h) =
      constrainedBlockValue S h-(N : ℝ)⁻¹*(Real.log S.card-N*Real.log 2) := by
  rw [spinPriorMeanPressure_field hhaar hgauss hN μ hμ]
  rw [restricted_normalized_root_integral (by omega) S hS h ⟨h.height 0,h.nonneg 0⟩]
  unfold constrainedBlockValue
  have he : (⟨h.height 0,h.nonneg 0⟩ : ℝ≥0)=NNReal.mk (h.height 0) (h.nonneg 0) := by
    apply Subtype.ext
    rfl
  rw [he]
  ring

end InvariantIsing

end

end OAI

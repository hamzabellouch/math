import OAI.Probability.InvariantIsing.Fields.SpinPriorFlatVariance
import OAI.Probability.InvariantIsing.Arrays.TensorZeroAmplitude

namespace OAI

/-! Removing the unused tensor marks from the field recursion preserves any
finite probability spin prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma tensorEnergyMarkLaw_zero_amplitude {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (v : SpinTensorIndex I degree → ℝ≥0) (site : ℝ≥0)
    (hv : ∀ i, v (Sum.inl i)=site) :
    tensorEnergyMarkLaw U I degree 0 v=fieldEnergyMarkLaw N site := by
  apply Subtype.ext
  change (tensorGaussianLaw I degree v : Measure _).map
      (fun z => spinTensorEnergy U I degree 0 z) =
    (vectorGaussianLaw N site : Measure _).map (fieldEnergy (N := N))
  have hp := tensorSiteProjection_measurePreserving I degree v site hv
  rw [← hp.map_eq, Measure.map_map (measurable_fieldEnergy_map N) hp.measurable]
  congr 1
  funext z
  funext σ
  exact spinTensorEnergy_zero_amplitude U I degree z σ

lemma spinPriorCascadeValue_field {N m k : ℕ} (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (z : SpinTensorIndex I degree → ℝ) :
    spinPriorCascadeValue π (fun _ => 0) U (fun _ => 0) I degree 0 n b
        (fun i => tensorPathProfile I degree n r h (i+1)) z =
      cascadeRecursion n b (fun i => vectorGaussianLaw N (varianceIncrement h (i+1)))
        (fun _ p => p.1+p.2) (fun y => finiteLogIntegral π (fieldEnergy y))
        (tensorSiteProjection I degree z) := by
  have he : tensorSpinBaseEnergy (fun _ => 0) U (fun _ => 0) I degree 0 z =
      fieldEnergy (tensorSiteProjection I degree z) := by
    funext σ
    simp only [tensorSpinBaseEnergy, rotatedEnergy, zero_mul, Finset.sum_const_zero,
      mul_zero, fieldEnergy, zero_add]
    exact spinTensorEnergy_zero_amplitude U I degree z σ
  have hm i : tensorEnergyMarkLaw U I degree 0 (tensorPathProfile I degree n r h (i+1)) =
      fieldEnergyMarkLaw N (varianceIncrement h (i+1)) :=
    tensorEnergyMarkLaw_zero_amplitude U I degree _ _ (fun _ => rfl)
  unfold spinPriorCascadeValue
  simp_rw [hm]
  rw [he]
  exact prior_field_energy_recursion N n π b (fun i => varianceIncrement h (i+1)) _

lemma spinPriorFlatLog_field_integral (hgauss : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0<N) (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    (∫ p, spinPriorFlatLog π (fun _ => 0) U (fun _ => 0) I degree 0 n
      (fun i => tensorPathProfile I degree n r h i) p
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
    ∫ z, cascadeRecursion n b (fun i => vectorGaussianLaw N (varianceIncrement h (i+1)))
      (fun _ p => p.1+p.2) (fun y => finiteLogIntegral π (fieldEnergy y)) z
      ∂(vectorGaussianLaw N (varianceIncrement h 0) : Measure (Fin N → ℝ)) := by
  let v := fun i => tensorPathProfile I degree n r h i
  let G := fun q : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n =>
    spinPriorLabeledLog π (fun _ => 0) U (fun _ => 0) I degree 0 n q.1 q.2
  have hp := tensorFlatToLabeled_measurePreserving U I degree 0 n b v
  have hm := measurable_spinPriorLabeledLog_root π (fun _ => 0) U (fun _ => 0) I degree 0 n
  have hi := (spinPriorLabeledLog_root_variance hgauss hN π (fun _ => 0) U (fun _ => 0)
    I degree 0 n b (fun i => v (i+1)) hb (varianceIncrement h 0)
    (fun j => varianceIncrement (monomialPath n (r j)) 0)).1.integrable (by norm_num)
  change Integrable G ((tensorGaussianLaw I degree (v 0) : Measure _).prod
    (tensorLabeledLaw U I degree 0 n b (fun i => v (i+1)))) at hi
  have he := hp.hasLaw.integral_comp hm.aestronglyMeasurable
  change (∫ p, G (tensorFlatToLabeled U I degree 0 n v p) ∂_) = ∫ q, G q ∂_ at he
  simp_rw [spinPriorFlatLog_eq_labeled]
  rw [he, integral_prod _ hi]
  dsimp only [G]
  simp_rw [(spinPriorLabeledLog_conditional hN π (fun _ => 0) U (fun _ => 0)
    I degree 0 n b (fun i => v (i+1)) hb _).2.1]
  dsimp only [v]
  simp_rw [spinPriorCascadeValue_field]
  exact (tensorSiteProjection_measurePreserving I degree (v 0) (varianceIncrement h 0)
    (fun _ => rfl)).hasLaw.integral_comp
      (measurable_cascadeRecursion n b _ (fun _ => measurable_fst.add measurable_snd)
        ((measurable_finiteLogIntegral π).comp (measurable_fieldEnergy_map N))).aestronglyMeasurable

end InvariantIsing

end

end OAI

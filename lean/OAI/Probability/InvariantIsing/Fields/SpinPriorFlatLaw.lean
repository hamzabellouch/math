import OAI.Probability.InvariantIsing.Fields.SpinPriorFlatVariance
import OAI.Probability.InvariantIsing.Fields.SpinPriorCascadePressure

namespace OAI

/-! Gaussian namespace changes preserve the constrained, quenched cascade
logarithm, including its full probability law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorJointFlatLog {N m k n : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) (p : TensorFlatDisorder N n) : ℝ :=
  priorTensorLog (labeledSpinReference n π p.1.2) eig c I degree amp v (p.1.1,p.2)

def spinPriorProfileLog {N m k n : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) (p : TensorFlatDisorder N n) : ℝ :=
  priorNamespacedLog (labeledSpinReference n π p.1.2) eig c I degree amp v (p.1.1,p.2)

lemma measurable_spinPriorJointFlatLog {N m k n : ℕ} (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (spinPriorJointFlatLog π eig c I degree amp v) := by
  have : ∀ p : TensorFlatDisorder N n,
      IsProbabilityMeasure ((labeledSpinReference n π ∘ fun p => p.1.2) p) := fun p => by
        change IsProbabilityMeasure (labeledSpinReference n π p.1.2)
        infer_instance
  have hν := (measurable_labeledSpinReference_general n π).comp
    (show Measurable (fun p : TensorFlatDisorder N n => p.1.2) from by fun_prop)
  have hH : Measurable (fun p : TensorFlatDisorder N n × (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1.1.1) p.2.1+fieldEnergy c p.2.1+
        cylinderField (tensorLeafCoefficients (specialRotation p.1.1.1) I degree amp n v p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hbase : Measurable (fun U : SpecialOrthogonal N =>
        rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1) := by
      exact ((Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul
          (eig i)).const_mul (1/2 : ℝ)).add_const _
    apply (hbase.comp measurable_fst.fst).add
    simp only [tensorLeafCoefficients, cylinderField_feature]
    apply Finset.measurable_sum
    intro i _
    exact (((measurable_spinTensorFeature I degree amp x.1 i.2).comp
      measurable_fst.fst).const_mul _).mul
      ((measurable_pi_apply (treeFeatureTag n x.2 i)).comp measurable_snd)
  exact (measurable_random_referencePartition hν hH).log

lemma measurable_spinPriorProfileLog {N m k n : ℕ} (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (spinPriorProfileLog π eig c I degree amp v) := by
  have : ∀ p : TensorFlatDisorder N n,
      IsProbabilityMeasure ((labeledSpinReference n π ∘ fun p => p.1.2) p) := fun p => by
        change IsProbabilityMeasure (labeledSpinReference n π p.1.2)
        infer_instance
  have hν := (measurable_labeledSpinReference_general n π).comp
    (show Measurable (fun p : TensorFlatDisorder N n => p.1.2) from by fun_prop)
  have hH := (measurable_priorNamespacedHamiltonian eig c I degree amp v).comp
    (show Measurable (fun p : TensorFlatDisorder N n × (Spin N × LabeledLeaf n) =>
      ((p.1.1.1,p.1.2),p.2)) from by fun_prop)
  exact (measurable_random_referencePartition hν hH).log

theorem spinPriorProfileLog_law {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    let P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
    HasLaw (spinPriorProfileLog π eig c I degree amp v)
      (P.map (spinPriorJointFlatLog π eig c I degree amp v)) P := by
  intro P
  have hl := measurable_spinPriorJointFlatLog π eig c I degree amp v
  have hr := measurable_spinPriorProfileLog π eig c I degree amp v
  refine ⟨hr.aemeasurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hr hs, Measure.map_apply hl hs,
    Measure.prod_apply (hr hs), Measure.prod_apply (hl hs)]
  apply lintegral_congr_ae
  apply ae_of_all
  intro q
  have he := congrArg (fun Q : Measure ℝ => Q s)
    (priorNamespacedLog_conditional_law (labeledSpinReference n π q.2) eig c q.1 I degree amp v)
  have hlq : Measurable (fun z => spinPriorJointFlatLog π eig c I degree amp v (q,z)) := hl.comp (show Measurable (fun z => (q,z)) from measurable_const.prodMk measurable_id)
  have hrq : Measurable (fun z => spinPriorProfileLog π eig c I degree amp v (q,z)) := hr.comp (show Measurable (fun z => (q,z)) from measurable_const.prodMk measurable_id)
  change (gaussianCoordinates.map (fun z => spinPriorJointFlatLog π eig c I degree amp v (q,z))) s =
    (gaussianCoordinates.map (fun z => spinPriorProfileLog π eig c I degree amp v (q,z))) s at he
  rw [Measure.map_apply hlq hs, Measure.map_apply hrq hs] at he
  exact he.symm

end InvariantIsing

end

end OAI

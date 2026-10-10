import OAI.Probability.InvariantIsing.Fields.SpinPriorContactField
import OAI.Probability.InvariantIsing.Fields.SpinPriorArrayLaw
import OAI.Probability.InvariantIsing.Arrays.TensorFieldTailBridge

namespace OAI

/-! The constrained field-direction test is a continuous spectral-array test. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma spinPriorArrayLaw_field_tail {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (b h : ℕ → ℝ)
    (r : Fin k → ℕ) (j : Fin (n + 1)) :
    (∫ x, spectralSpinDepthTail n j x
      ∂(spinPriorArrayLaw μ π eig c I degree amp n b r h : Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amp n b r h
        (fun _ => tensorFieldPairObservable (finiteFieldPath (Pi.single j 1))) := by
  classical
  refine spinPriorArrayLaw_test μ π eig c I degree amp n b r h _
    (continuous_spectralSpinDepthTail n j) _ ![1,0] ?_ ?_
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro U σ
    simp only [spectralSpinDepthTail, spectralSpinArray_joint (specialRotation U) I hdis hcover,
      spectralJointEntry_tree, tensorFieldPairObservable, spinPairOverlap,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [treeOverlap, depthTail_level, finiteFieldPath_single]


end InvariantIsing

end

end OAI

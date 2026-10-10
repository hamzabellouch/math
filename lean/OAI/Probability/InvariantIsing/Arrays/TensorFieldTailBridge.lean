import OAI.Probability.InvariantIsing.Arrays.TensorContactField
import OAI.Probability.InvariantIsing.Arrays.TensorArrayWard
import OAI.Probability.InvariantIsing.Spectral.SpectralTreeTail

namespace OAI

/-! The contact field directions are bounded continuous tests of the actual
spectral array, so their expectations pass to the synchronized limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def spectralSpinDepthTail {m : ℕ} (n j : ℕ) (x : SpectralArray (m + 1)) : ℝ :=
  spectralSpinArray x 0 1 * depthTail n j (x (0,1) (Fin.last m) : ℝ)

lemma continuous_spectralSpinDepthTail {m : ℕ} (n j : ℕ) :
    Continuous (spectralSpinDepthTail (m := m) n j) := by
  unfold spectralSpinDepthTail
  exact (show Continuous (fun x : SpectralArray (m + 1) => spectralSpinArray x 0 1) by
    unfold spectralSpinArray; fun_prop).mul
      ((continuous_depthTail n j).comp (by fun_prop))

lemma tensorNamespacedArrayLaw_field_tail {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (b h : ℕ → ℝ)
    (r : Fin k → ℕ) (j : Fin (n + 1)) :
    (∫ x, spectralSpinDepthTail n j x
      ∂(tensorNamespacedArrayLaw μ eig c I degree amp n b r h : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amp n b r h
        (fun _ => tensorFieldPairObservable (finiteFieldPath (Pi.single j 1))) := by
  classical
  refine tensorNamespacedArrayLaw_test μ eig c I degree amp n b r h _
    (continuous_spectralSpinDepthTail n j) _ ![1,0] ?_ ?_
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro U σ
    simp only [spectralSpinDepthTail, spectralSpinArray_joint (specialRotation U) I hdis hcover,
      spectralJointEntry_tree, tensorFieldPairObservable, spinPairOverlap,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [treeOverlap, depthTail_level, finiteFieldPath_single]

lemma spectralSpinDepthTail_weak_limit {m n : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q)) (j : ℕ) :
    Tendsto (fun k => ∫ x, spectralSpinDepthTail n j x ∂(L k : Measure (SpectralArray (m + 1)))) atTop
      (𝓝 (∫ x, spectralSpinDepthTail n j x ∂(Q : Measure (SpectralArray (m + 1))))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
    (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_spectralSpinDepthTail n j⟩)

end InvariantIsing

end

end OAI

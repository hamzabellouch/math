import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaLaw
import OAI.Probability.InvariantIsing.Fields.SpinPriorReplicaAverage

namespace OAI

/-! Finite-replica tests of the actual tensor spectral-array law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

def spinPriorArrayLaw {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m + 1)) :=
  spectralArrayLaw ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
    (fun p : TensorFlatDisorder N n => p.1.1) measurable_fst.fst I n
    (spinPriorNamespacedReference (n := n) π eig c I degree amplitude r h)
    (measurable_spinPriorNamespacedReference (n := n) π eig c I degree amplitude r h)

/-- Injection into the infinite replica sequence gives the exact actual
finite-replica mean, while retaining its common rotation. -/
theorem spinPriorArrayLaw_test {N m k z : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F)
    (D : SpecialOrthogonal N → (Fin z → Spin N × LabeledLeaf n) → ℝ)
    (ι : Fin z → ℕ) (hi : Function.Injective ι)
    (he : ∀ (U : SpecialOrthogonal N) (σ : ℕ → Spin N × LabeledLeaf n), F (fun ij : ℕ × ℕ =>
      spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2)) = D U (fun i => σ (ι i))) :
    (∫ x, F x ∂(spinPriorArrayLaw μ π eig c I degree amplitude n b r h :
      Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amplitude n b r h D := by
  rw [spinPriorArrayLaw, spectralArrayLaw_integral _ _ _ _ _ _ _ F hF]
  unfold spinPriorReplicaAverage
  simp only [referenceReplicaMean_zero]
  apply integral_congr_ae
  filter_upwards [] with p
  have hm : Measurable (fun σ : ℕ → Spin N × LabeledLeaf n => fun i : Fin z => σ (ι i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (ι i)
  let ν := spinPriorNamespacedReference (n := n) π eig c I degree amplitude r h p
  have ht := integral_map hm.aemeasurable (μ := Measure.infinitePi (fun _ : ℕ => ν))
    (measurable_of_countable (D p.1.1)).aestronglyMeasurable
  rw [replica_injective_map ν ι hi] at ht
  change (∫ σ, F (fun ij : ℕ × ℕ =>
    spectralJointEntry (specialRotation p.1.1) I n (σ ij.1) (σ ij.2))
    ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫ σ, D p.1.1 σ ∂Measure.pi (fun _ : Fin z => ν)
  simp_rw [he]
  exact ht.symm

end InvariantIsing

end

end OAI

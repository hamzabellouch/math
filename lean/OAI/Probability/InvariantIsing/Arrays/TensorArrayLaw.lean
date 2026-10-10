import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaLaw
import OAI.Probability.InvariantIsing.Arrays.TensorReplicaAverageLaw

namespace OAI

/-! Finite-replica tests of the actual tensor spectral-array law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

def tensorNamespacedArrayLaw {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m + 1)) :=
  spectralArrayLaw ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
    (fun p : TensorFlatDisorder N n => p.1.1) measurable_fst.fst I n
    (tensorNamespacedReference eig c I degree amplitude n r h)
    (measurable_tensorNamespacedReference eig c I degree amplitude n r h)

/-- Injection into the infinite replica sequence gives the exact actual
finite-replica mean, while retaining its common rotation. -/
theorem tensorNamespacedArrayLaw_test {N m k z : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F)
    (D : SpecialOrthogonal N → (Fin z → Spin N × LabeledLeaf n) → ℝ)
    (ι : Fin z → ℕ) (hi : Function.Injective ι)
    (he : ∀ (U : SpecialOrthogonal N) (σ : ℕ → Spin N × LabeledLeaf n), F (fun ij : ℕ × ℕ =>
      spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2)) = D U (fun i => σ (ι i))) :
    (∫ x, F x ∂(tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h :
      Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h D := by
  rw [tensorNamespacedArrayLaw, spectralArrayLaw_integral _ _ _ _ _ _ _ F hF]
  unfold tensorNamespacedReplicaAverage
  simp only [referenceReplicaMean_zero]
  apply integral_congr_ae
  filter_upwards [] with p
  have hm : Measurable (fun σ : ℕ → Spin N × LabeledLeaf n => fun i : Fin z => σ (ι i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (ι i)
  let ν := tensorNamespacedReference eig c I degree amplitude n r h p
  have ht := integral_map hm.aemeasurable (μ := Measure.infinitePi (fun _ : ℕ => ν))
    (measurable_of_countable (D p.1.1)).aestronglyMeasurable
  rw [replica_injective_map ν ι hi] at ht
  change (∫ σ, F (fun ij : ℕ × ℕ =>
    spectralJointEntry (specialRotation p.1.1) I n (σ ij.1) (σ ij.2))
    ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫ σ, D p.1.1 σ ∂Measure.pi (fun _ : Fin z => ν)
  simp_rw [he]
  exact ht.symm

def finiteSpectralBlock {N m z : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (n : ℕ) (σ : Fin z → Spin N × LabeledLeaf n) :
    SpectralBlock (m + 1) z :=
  fun i j => spectralJointEntry U I n (σ i) (σ j)

private lemma measurable_finiteReplicaBlock {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] {z : ℕ}
    (J : Ω → X → X → Y)
    (hJ : Measurable (fun p : Ω × (X × X) => J p.1 p.2.1 p.2.2)) :
    Measurable (fun p : Ω × (Fin z → X) => fun i j : Fin z => J p.1 (p.2 i) (p.2 j)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have hi : Measurable (fun p : Ω × (Fin z → X) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hj : Measurable (fun p : Ω × (Fin z → X) => p.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact hJ.comp (measurable_fst.prodMk (hi.prodMk hj))

lemma measurable_finiteSpectralBlock {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) :
    Measurable (fun p : SpecialOrthogonal N × (Fin z → Spin N × LabeledLeaf n) =>
      finiteSpectralBlock (specialRotation p.1) I n p.2) := by
  exact measurable_finiteReplicaBlock (fun U => spectralJointEntry (specialRotation U) I n)
    (measurable_spectralJointEntry I n)

def permutedSpectralBlockTest {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) (e : Equiv.Perm (Fin z))
    (D : SpectralBlock (m + 1) z → ℝ)
    (U : SpecialOrthogonal N) (σ : Fin z → Spin N × LabeledLeaf n) : ℝ :=
  D (finiteSpectralBlock (specialRotation U) I n (σ ∘ e.symm))

private lemma measurable_permutedReplicaTest {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] {z : ℕ}
    (B : Ω → (Fin z → X) → Y) (hB : Measurable (Function.uncurry B))
    (e : Equiv.Perm (Fin z)) (D : Y → ℝ) (hD : Measurable D) :
    Measurable (Function.uncurry (fun U σ => D (B U (σ ∘ e.symm)))) := by
  have hm : Measurable (fun p : Ω × (Fin z → X) => (p.1, p.2 ∘ e.symm)) :=
    measurable_fst.prodMk (Measurable.of_eval fun i => (measurable_pi_apply (e.symm i)).comp measurable_snd)
  exact hD.comp (hB.comp hm)

lemma measurable_permutedSpectralBlockTest {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) (e : Equiv.Perm (Fin z))
    (D : SpectralBlock (m + 1) z → ℝ) (hD : Continuous D) :
    Measurable (Function.uncurry (permutedSpectralBlockTest I n e D)) := by
  exact measurable_permutedReplicaTest (fun U => finiteSpectralBlock (specialRotation U) I n)
    (measurable_finiteSpectralBlock I n) e D hD.measurable

lemma permutedSpectralBlockTest_embedding {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) (e : Equiv.Perm (Fin z))
    (D : SpectralBlock (m + 1) z → ℝ) (U : SpecialOrthogonal N)
    (σ : ℕ → Spin N × LabeledLeaf n) :
    permutedSpectralBlockTest I n e D U (fun j => σ (e j)) =
      D (spectralBlockView (m + 1) z (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) := by
  apply congrArg D
  funext i j
  simp only [finiteSpectralBlock, Function.comp_apply,
    Equiv.apply_symm_apply, spectralBlockView]

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Cavity.CavityRotationProbability
import OAI.Probability.InvariantIsing.Cavity.CavityGroupedGram
import OAI.Probability.InvariantIsing.Cavity.CavitySampledBlocks

namespace OAI

/-! The spectral array of the concrete base rotation/Gaussian Gibbs
law. The same rotation supplies its overlaps and cavity coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityProjectedOverlap {N : ℕ} (I : Finset (Fin N)) (σ τ : Spin N) :
    Measurable (fun V : Orthogonal N => projectedOverlap (matrixRotation V⁻¹) I σ τ) := by
  unfold projectedOverlap
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact (measurable_cavityRotation_eval (spinVector σ) i).mul
    (measurable_cavityRotation_eval (spinVector τ) i)

lemma measurable_cavitySpectralJointEntry {N m depth : ℕ}
    (I : Fin m → Finset (Fin N)) (x y : Spin N × LabeledLeaf depth) :
    Measurable (fun V : Orthogonal N => spectralJointEntry (matrixRotation V⁻¹) I depth x y) := by
  apply Measurable.of_eval
  intro a
  refine Fin.lastCases ?_ (fun a => ?_) a
  · simp only [spectralJointEntry, Fin.lastCases_last]
    exact measurable_const
  · simp only [spectralJointEntry, Fin.lastCases_castSucc]
    exact (measurable_cavityProjectedOverlap (I a) x.1 y.1).subtype_mk

def cavityRotationEntry {N m depth : ℕ} (I : Fin m → Finset (Fin N))
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
    (x y : Spin N × LabeledLeaf depth) : SpectralEntry (m+1) :=
  spectralJointEntry (matrixRotation p.1.1⁻¹) I depth x y

lemma measurable_cavityRotationEntry {N m depth : ℕ}
    (I : Fin m → Finset (Fin N)) (x y : Spin N × LabeledLeaf depth) :
    Measurable (fun p => cavityRotationEntry I p x y) :=
  (measurable_cavitySpectralJointEntry I x y).comp measurable_fst.fst

lemma cavityRotationEntry_gram {N m depth : ℕ} (I : Fin m → Finset (Fin N))
    (p : ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth)) :
    SpectralGram (cavitySampledEntryArray (cavityRotationEntry I) p) := by
  intro a r
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simpa only [spectralCoordinateArray, cavitySampledEntryArray,
      cavityRotationEntry, spectralJointEntry_tree] using
      treeOverlap_posSemidef depth (fun i : Fin r => (p.2 i).2)
  · simpa only [spectralCoordinateArray, cavitySampledEntryArray,
      cavityRotationEntry, spectralJointEntry_spectral] using
      projectedOverlap_posSemidef (matrixRotation p.1.1.1⁻¹) (I j)
        (fun i : Fin r => (p.2 i).1)

def cavityRotationArrayLaw {N m depth : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (ρ : Measure (LabeledTree depth)) [IsProbabilityMeasure ρ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m+1)) :=
  ⟨(disorderReplicaLaw ((μ.prod ρ).prod gaussianCoordinates)
    (cavityRotationProbability eig I u) (measurable_cavityRotationProbability eig I u)).map
      (cavitySampledEntryArray (cavityRotationEntry I)),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_cavitySampledEntryArray (cavityRotationEntry I)
        (measurable_cavityRotationEntry I)).aemeasurable).mpr inferInstance⟩

lemma cavityRotationArrayLaw_gram {N m depth : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (ρ : Measure (LabeledTree depth)) [IsProbabilityMeasure ρ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    ∀ᵐ x ∂(cavityRotationArrayLaw μ ρ eig I u : Measure (SpectralArray (m+1))),
      SpectralGram x := by
  rw [cavityRotationArrayLaw]
  apply (ae_map_iff (measurable_cavitySampledEntryArray (cavityRotationEntry I)
    (measurable_cavityRotationEntry I)).aemeasurable
    (isClosed_spectralGram (m+1)).measurableSet).mpr
  exact ae_of_all _ (cavityRotationEntry_gram I)

end InvariantIsing

end

end OAI

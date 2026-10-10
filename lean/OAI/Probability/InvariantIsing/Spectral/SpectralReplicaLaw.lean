import OAI.Probability.InvariantIsing.Spectral.SpectralArrayGG
import OAI.Probability.InvariantIsing.Arrays.PerturbationMeasurability

namespace OAI

/-! Actual spectral overlap array laws retain the common rotation disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology ENNReal NNReal

namespace InvariantIsing

def spectralJointEntry {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) : SpectralEntry (m + 1) :=
  Fin.lastCases
    ⟨treeOverlap n x.2 y.2, ⟨(by linarith [(treeOverlap_mem n x.2 y.2).1]),
      (treeOverlap_mem n x.2 y.2).2⟩⟩
    (fun a => ⟨projectedOverlap U (I a) x.1 y.1, abs_le.mp (projectedOverlap_abs_le_one U (I a) x.1 y.1)⟩)

lemma spectralJointEntry_spectral {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) (a : Fin m) :
    (spectralJointEntry U I n x y a.castSucc : ℝ) = projectedOverlap U (I a) x.1 y.1 := by
  simp only [spectralJointEntry, Fin.lastCases_castSucc]

lemma spectralJointEntry_tree {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) :
    (spectralJointEntry U I n x y (Fin.last m) : ℝ) = treeOverlap n x.2 y.2 := by
  simp only [spectralJointEntry, Fin.lastCases_last]

lemma measurable_spectralJointEntry {N m : ℕ} (I : Fin m → Finset (Fin N)) (n : ℕ) :
    Measurable (fun p : SpecialOrthogonal N × ((Spin N × LabeledLeaf n) × (Spin N × LabeledLeaf n)) =>
      spectralJointEntry (specialRotation p.1) I n p.2.1 p.2.2) := by
  apply measurable_from_prod_countable_left
  intro xy
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp only [spectralJointEntry, Fin.lastCases_last]
    exact (measurable_const : Measurable
      (fun _ : SpecialOrthogonal N => treeOverlap n xy.1.2 xy.2.2)).subtype_mk
  · simp only [spectralJointEntry, Fin.lastCases_castSucc]
    exact (measurable_projectedOverlap (I a) xy.1.1 xy.2.1).subtype_mk

def spectralReplicaArray {Ω : Type*} {N m : ℕ} (U : Ω → SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (p : Ω × (ℕ → Spin N × LabeledLeaf n)) : SpectralArray (m + 1) :=
  fun ij => spectralJointEntry (specialRotation (U p.1)) I n (p.2 ij.1) (p.2 ij.2)

lemma measurable_spectralReplicaArray {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ) : Measurable (spectralReplicaArray U I n) := by
  unfold spectralReplicaArray
  apply Measurable.of_eval
  intro ij
  change Measurable (fun p : Ω × (ℕ → Spin N × LabeledLeaf n) =>
    spectralJointEntry (specialRotation (U p.1)) I n (p.2 ij.1) (p.2 ij.2))
  let f : (Ω × (ℕ → Spin N × LabeledLeaf n)) →
      SpecialOrthogonal N × ((Spin N × LabeledLeaf n) × (Spin N × LabeledLeaf n)) :=
    fun p => (U p.1, (p.2 ij.1, p.2 ij.2))
  have hrot : Measurable (fun p : Ω × (ℕ → Spin N × LabeledLeaf n) => U p.1) :=
    hU.comp measurable_fst
  have hi : Measurable (fun p : Ω × (ℕ → Spin N × LabeledLeaf n) => p.2 ij.1) :=
    (measurable_pi_apply ij.1).comp measurable_snd
  have hj : Measurable (fun p : Ω × (ℕ → Spin N × LabeledLeaf n) => p.2 ij.2) :=
    (measurable_pi_apply ij.2).comp measurable_snd
  have hp : Measurable f := hrot.prodMk (hi.prodMk hj)
  have he := (measurable_spectralJointEntry I n).comp hp
  convert he using 1
  rfl

/-- Keeping the external disorder in the sampled space is essential:
projected overlaps depend on the same rotation as the Gibbs measure. -/
def disorderReplicaLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] : Measure (Ω × (ℕ → X)) :=
  P ⊗ₘ replicaKernel ν hν

instance disorderReplicaLaw_probability {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    IsProbabilityMeasure (disorderReplicaLaw P ν hν) := by
  unfold disorderReplicaLaw
  infer_instance

def spectralArrayLaw {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] : ProbabilityMeasure (SpectralArray (m + 1)) :=
  ⟨(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_spectralReplicaArray U hU I n).aemeasurable).mpr inferInstance⟩

theorem spectralArrayLaw_integral {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)]
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F) :
    (∫ x, F x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1)))) =
      ∫ ω, ∫ σ, F (spectralReplicaArray U I n (ω, σ))
        ∂Measure.infinitePi (fun _ : ℕ => ν ω) ∂P := by
  have hm := measurable_spectralReplicaArray U hU I n
  have hi : Integrable (F ∘ spectralReplicaArray U I n) (disorderReplicaLaw P ν hν) := by
    exact (MeasureTheory.integrable_map_measure hF.aestronglyMeasurable hm.aemeasurable).mp
      (compact_integrable hF)
  change (∫ x, F x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n)) = _
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable]
  exact Measure.integral_compProd hi

end InvariantIsing

end

end OAI

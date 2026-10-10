import OAI.Probability.InvariantIsing.Cavity.CavityDisorderMean
import OAI.Probability.InvariantIsing.Magnetic.RestrictedHaarSymmetry

namespace OAI

/-! Disorder-dependent bounded tests, used for physical spectral
projections before any restriction of the Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_restrictedCavityFullDisorderInner {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => referenceReplicaMean
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig (specialRotation p.1) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2)
      (F p.1)) := by
  let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
  let : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T))
  let H : (SpecialOrthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) → ℝ :=
    fun z => rotatedEnergy eig (specialRotation z.1.1) z.2.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation z.1.1) I u depth z.2) z.1.2
  have hmH : Measurable H := by
    apply measurable_from_prod_countable_left
    intro x
    have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
      unfold rotatedEnergy
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
    exact (hr.comp measurable_fst).add (measurable_cavityPerturbationField I u x)
  change Measurable (fun p => referenceReplicaMean ν (fun x => H (p, x)) (F p.1))
  exact measurable_referenceReplicaMean ν (H := H) (D := fun z => F z.1.1 z.2)
    hmH (hFm.comp (measurable_fst.fst.prodMk measurable_snd))

theorem restricted_full_disorder_site_symmetry {N m depth : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (p : Equiv.Perm (Fin N))
    (hinv : ∀ σ, cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ ∈ S ↔ σ ∈ S)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) :
    let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
    (∫ U, ∫ g, referenceReplicaMean ν
      (fun x => rotatedEnergy eig (specialRotation U) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
      (F U) ∂gaussianCoordinates ∂μ) =
    ∫ U, ∫ g, referenceReplicaMean ν
      (fun x => rotatedEnergy eig (specialRotation U) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
      (fun σ => F (U * (spectralPermutation hN p)⁻¹) (fun i =>
        (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) (σ i).1, (σ i).2)))
      ∂gaussianCoordinates ∂μ := by
  dsimp only
  let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
  let e := cavitySignedSpinPermutation p (cavityPermutationFlip hN p)
  let H := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    rotatedEnergy eig (specialRotation U) x.1
  let C := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    cavityPerturbationCoefficients (specialRotation U) I u depth x
  have hmean : Measurable (fun U => ∫ g, referenceReplicaMean ν
      (fun x => H U x + cylinderField (C U x) g) (F U) ∂gaussianCoordinates) :=
    (measurable_restrictedCavityFullDisorderInner S hS T eig I u F hFm).stronglyMeasurable.integral_prod_right'.measurable
  apply cavity_twoReplica_disorder_symmetry μ
    (fun U => U * (spectralPermutation hN p)⁻¹)
    (measurePreserving_mul_right μ _) ν (fun x => (e x.1, x.2))
    (restricted_labeled_spin_reference_equiv S hS T e hinv) H C
    (fun U => ∑ σ : Spin N, |rotatedEnergy eig (specialRotation U) σ|)
    (fun _ => 4 * (N * perturbationScale N ^ 2))
  · intro U x
    exact Finset.single_le_sum (f := fun σ : Spin N =>
      |rotatedEnergy eig (specialRotation U) σ|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x.1)
  · intro U x
    exact cavityPerturbationCoefficients_sq_le _ I u hu x
  · intro U x
    exact rotatedEnergy_cavityPermutation hN p eig U x.1
  · intro U x y
    simp only [C, e, cavityPerturbationCoefficients_cross, cavityWeightedKernel,
      cavityPerturbationKernel, projectedOverlap_cavityPermutation]
  · exact hB
  · exact hF
  · exact hmean.aestronglyMeasurable

def restrictedCavityFullDisorderTest {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (μ : Measure (SpecialOrthogonal N))
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  ∫ U, ∫ g, referenceReplicaMean
    (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (fun x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    (F U) ∂gaussianCoordinates ∂μ

lemma restrictedCavityFullDisorderTest_abs_le {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) :
    |restrictedCavityFullDisorderTest S hS μ T eig I u F| ≤ B := by
  exact cavity_nested_disorder_abs_le μ gaussianCoordinates
    (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ => measurable_of_countable _)
    (measurable_restrictedCavityFullDisorderInner S hS T eig I u F hFm) hB hF

lemma restrictedCavityFullDisorderTest_sum {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) {ι : Type*} [Fintype ι]
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : ι → SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : ∀ i, Measurable (Function.uncurry (F i)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i U σ, |F i U σ| ≤ B) :
    restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => ∑ i, F i U σ) =
      ∑ i, restrictedCavityFullDisorderTest S hS μ T eig I u (F i) := by
  exact cavity_nested_disorder_replica_sum μ gaussianCoordinates
    (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ _ => measurable_of_countable _)
    (fun i => measurable_restrictedCavityFullDisorderInner S hS T eig I u (F i) (hmF i)) hB hF


end InvariantIsing

end

end OAI

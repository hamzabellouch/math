import OAI.Probability.InvariantIsing.Cavity.CavityFullSymmetry
import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinSymmetry

namespace OAI

/-! The full finite Ising model with its actual spectral/tree tensor
perturbation has signed site-permutation symmetry after Haar averaging. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem restricted_full_signed_site_symmetry {N m depth : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (p : Equiv.Perm (Fin N))
    (hinv : ∀ σ, cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ ∈ S ↔ σ ∈ S)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ σ, |F σ| ≤ B) :
    let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
    (∫ U, ∫ g, referenceReplicaMean ν
      (fun x => rotatedEnergy eig (specialRotation U) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g) F
      ∂gaussianCoordinates ∂μ) =
    ∫ U, ∫ g, referenceReplicaMean ν
      (fun x => rotatedEnergy eig (specialRotation U) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
      (fun σ => F (fun i =>
        (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) (σ i).1, (σ i).2)))
      ∂gaussianCoordinates ∂μ := by
  dsimp only
  let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
  let e := cavitySignedSpinPermutation p (cavityPermutationFlip hN p)
  let H := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    rotatedEnergy eig (specialRotation U) x.1
  let C := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    cavityPerturbationCoefficients (specialRotation U) I u depth x
  have hHm : Measurable (fun z : (SpecialOrthogonal N × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth) => H z.1.1 z.2 + cylinderField (C z.1.1 z.2) z.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hr : Measurable (fun U : SpecialOrthogonal N => H U x) := by
      unfold H rotatedEnergy
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
    exact (hr.comp measurable_fst).add (measurable_cavityPerturbationField I u x)
  have hmean : Measurable (fun U => ∫ g, referenceReplicaMean ν
      (fun x => H U x + cylinderField (C U x) g) F ∂gaussianCoordinates) :=
    (measurable_referenceReplicaMean ν hHm
      ((measurable_of_countable F).comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  apply cavity_twoReplica_ensemble_symmetry μ
    (fun U => U * (spectralPermutation hN p)⁻¹)
    (measurePreserving_mul_right μ _) ν (fun x => (e x.1, x.2))
    (restricted_labeled_spin_reference_equiv S hS T e hinv) H C
    (fun U => ∑ σ : Spin N, |rotatedEnergy eig (specialRotation U) σ|)
    (fun _ => 4 * (N * perturbationScale N ^ 2))
  · intro U x
    exact Finset.single_le_sum
      (f := fun σ : Spin N => |rotatedEnergy eig (specialRotation U) σ|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ x.1)
  · intro U x
    exact cavityPerturbationCoefficients_sq_le _ I u hu x
  · intro U x
    exact rotatedEnergy_cavityPermutation hN p eig U x.1
  · intro U x y
    simp only [C, e, cavityPerturbationCoefficients_cross, cavityWeightedKernel,
      cavityPerturbationKernel, projectedOverlap_cavityPermutation]
  · exact measurable_of_countable F
  · exact hB
  · exact hF
  · exact hmean.aestronglyMeasurable

end InvariantIsing

end

end OAI

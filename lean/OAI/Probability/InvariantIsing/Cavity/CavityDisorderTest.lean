import OAI.Probability.InvariantIsing.Cavity.CavityFullSymmetry

namespace OAI

/-! Disorder-dependent bounded tests, used for physical spectral
projections before any restriction of the Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem cavity_twoReplica_disorder_symmetry {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X]
    (μ : Measure Ω) (R : Ω → Ω) (hR : MeasurePreserving R μ μ)
    (ν : Measure X) [IsProbabilityMeasure ν]
    (e : X → X) (he : MeasurePreserving e ν ν)
    (H : Ω → X → ℝ) (C : Ω → X → ℕ →₀ ℝ)
    (M V : Ω → ℝ) (hH : ∀ ω x, |H ω x| ≤ M ω)
    (hV : ∀ ω x, (C ω x).sum (fun _ z => z ^ 2) ≤ V ω)
    (henergy : ∀ ω x, H (R ω) (e x) = H ω x)
    (hcov : ∀ ω x y, cylinderCross (C (R ω) (e x)) (C (R ω) (e y)) =
      cylinderCross (C ω x) (C ω y))
    (F : Ω → (Fin 2 → X) → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hFb : ∀ ω σ, |F ω σ| ≤ B)
    (hmeas : AEStronglyMeasurable (fun ω => ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g) (F ω) ∂gaussianCoordinates) μ) :
    (∫ ω, ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g) (F ω) ∂gaussianCoordinates ∂μ) =
    ∫ ω, ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g)
      (fun σ => F (R ω) (fun i => e (σ i))) ∂gaussianCoordinates ∂μ := by
  rw [← hR.hasLaw.integral_comp hmeas]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only [Function.comp_apply]
    have ht := cavity_twoReplica_gaussian_transport ν e he (H (R ω))
      (measurable_of_countable _) (C (R ω)) (fun _ => measurable_of_countable _)
      (F (R ω)) (measurable_of_countable _)
    simp_rw [henergy] at ht
    rw [← ht]
    exact (cavity_twoReplica_same_covariance ν (H ω)
      (fun σ => F (R ω) (fun i => e (σ i))) (hH ω) (C ω)
      (fun x => C (R ω) (e x)) (hV ω) (fun x => hV (R ω) (e x))
      (hcov ω) hB (fun σ => hFb (R ω) (fun i => e (σ i)))).symm

lemma measurable_cavityFullDisorderInner {N m depth : ℕ}
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => referenceReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig (specialRotation p.1) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2)
      (F p.1)) := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T))
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

theorem cavity_full_disorder_site_symmetry {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (p : Equiv.Perm (Fin N))
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) :
    let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
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
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let e := cavitySignedSpinPermutation p (cavityPermutationFlip hN p)
  let H := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    rotatedEnergy eig (specialRotation U) x.1
  let C := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    cavityPerturbationCoefficients (specialRotation U) I u depth x
  have hmean : Measurable (fun U => ∫ g, referenceReplicaMean ν
      (fun x => H U x + cylinderField (C U x) g) (F U) ∂gaussianCoordinates) :=
    (measurable_cavityFullDisorderInner T eig I u F hFm).stronglyMeasurable.integral_prod_right'.measurable
  apply cavity_twoReplica_disorder_symmetry μ
    (fun U => U * (spectralPermutation hN p)⁻¹)
    (measurePreserving_mul_right μ _) ν (fun x => (e x.1, x.2))
    (labeledSpinReference_equiv e T) H C
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

end InvariantIsing

end

end OAI

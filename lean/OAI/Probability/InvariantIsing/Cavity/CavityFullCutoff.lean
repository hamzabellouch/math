import OAI.Probability.InvariantIsing.Cavity.CavityRandomCutoff
import OAI.Probability.InvariantIsing.Cavity.CavityFullTightness
import OAI.Probability.InvariantIsing.Cavity.CavityBaseExhaustion

namespace OAI

/-! Bounded cutoff tests for the actual perturbed Ising law, with the
same Haar and Gaussian disorder in the full and restricted models. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

def cavityFullHamiltonian {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) (x : Spin N × LabeledLeaf depth) : ℝ :=
  rotatedEnergy eig (specialRotation p.1) x.1 +
    cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2

lemma measurable_cavityFullHamiltonian {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add (measurable_cavityPerturbationField I u x)

lemma cavity_full_exp_integrable_ae {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) :
    ∀ᵐ p ∂μ.prod gaussianCoordinates, Integrable
      (fun x => Real.exp (cavityFullHamiltonian eig I u p x))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T) := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  apply (Measure.ae_prod_iff_ae_ae (_root_.measurableSet_integrable (μ := ν)
    (f := fun p x => Real.exp (cavityFullHamiltonian (depth := depth) eig I u p x))
    (measurable_cavityFullHamiltonian (depth := depth) eig I u).exp.stronglyMeasurable)).mpr
  exact ae_of_all _ fun U => cylinder_partition_exp_integrable_ae ν
    (fun x => rotatedEnergy eig (specialRotation U) x.1)
    (cavity_bounded_base_exp_integrable ν _ (fun x =>
      Finset.single_le_sum (f := fun σ : Spin N => |rotatedEnergy eig (specialRotation U) σ|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ x.1)))
    (cavityPerturbationCoefficients (specialRotation U) I u depth)
    (cavityPerturbationCoefficients_sq_le _ I u hu)

def cavityFullCutoffDisorderTest {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  ∫ U, ∫ g, cavityCutoffReplicaMean
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (cavityFullHamiltonian eig I u (U, g)) (s U) (F U) ∂gaussianCoordinates ∂μ

theorem cavity_full_cutoff_error {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (hs : MeasurableSet {p : SpecialOrthogonal N × (Spin N × LabeledLeaf depth) | p.2 ∈ s p.1})
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F))
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ U σ, |F U σ| ≤ M) :
    |cavityFullCutoffDisorderTest μ T eig I u s F - cavityFullDisorderTest μ T eig I u F| ≤
      4 * M * cavityFullDisorderTest μ T eig I u
        (fun U σ => if σ 0 ∈ (s U)ᶜ then 1 else 0) := by
  let P := μ.prod gaussianCoordinates
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let H := cavityFullHamiltonian (depth := depth) eig I u
  let G : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → Spin N × LabeledLeaf depth) → ℝ :=
    fun p => F p.1.1 p.2
  let S := fun p : SpecialOrthogonal N × (ℕ → ℝ) => s p.1
  have hmH : Measurable (Function.uncurry H) := measurable_cavityFullHamiltonian eig I u
  have hmG : Measurable G := hmF.comp (measurable_fst.fst.prodMk measurable_snd)
  have hmS : MeasurableSet {p : (SpecialOrthogonal N × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth) | p.2 ∈ S p.1} :=
    hs.preimage (measurable_fst.fst.prodMk measurable_snd)
  have hiH := cavity_full_exp_integrable_ae μ T eig I u hu
  have hmC := measurable_cavityCutoffReplicaMean ν (Function.uncurry H) hmH S hmS G hmG
  have hmR := measurable_referenceReplicaMean ν (H := Function.uncurry H) hmH hmG
  have hmTail : Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      referenceReplicaMean ν (H p) (fun σ : Fin 2 → Spin N × LabeledLeaf depth =>
        if σ 0 ∈ (S p)ᶜ then (1 : ℝ) else 0)) := by
    apply measurable_referenceReplicaMean ν (H := Function.uncurry H)
      (D := fun p : (SpecialOrthogonal N × (ℕ → ℝ)) ×
        (Fin 2 → Spin N × LabeledLeaf depth) =>
        if p.2 0 ∈ (S p.1)ᶜ then 1 else 0) hmH
    exact Measurable.ite ((hmS.preimage
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).compl)
      measurable_const measurable_const
  have hms (p : SpecialOrthogonal N × (ℕ → ℝ)) : MeasurableSet (S p) :=
    hmS.preimage measurable_prodMk_left
  have hiC : Integrable (fun p => cavityCutoffReplicaMean ν (H p) (S p) (fun σ => G (p, σ))) P :=
    Integrable.of_bound hmC.aestronglyMeasurable M (hiH.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using
        cavity_cutoff_replica_abs_le ν _ hp _ (hms p) _ hM (hF p.1))
  have hiR : Integrable (fun p => referenceReplicaMean ν (H p) (fun σ => G (p, σ))) P :=
    integrable_of_measurable_abs_le hmR (fun p => referenceReplicaMean_abs_le ν _ _
      (measurable_of_countable _) hM (hF p.1))
  have hiTail : Integrable (fun p => referenceReplicaMean ν (H p)
      (fun σ : Fin 2 → Spin N × LabeledLeaf depth => if σ 0 ∈ (S p)ᶜ then 1 else 0)) P :=
    integrable_of_measurable_abs_le hmTail (fun p => referenceReplicaMean_abs_le ν _ _
      (measurable_of_countable _) zero_le_one (fun σ => by split_ifs <;> norm_num))
  have ht := cavity_random_cutoff_error P ν (Function.uncurry H) hmH hiH S hmS G hmG hM
    (fun p => hF p.1)
  dsimp only [P, Function.uncurry] at ht
  rw [integral_prod _ hiC, integral_prod _ hiR, integral_prod _ hiTail] at ht
  exact ht

end InvariantIsing

end

end OAI

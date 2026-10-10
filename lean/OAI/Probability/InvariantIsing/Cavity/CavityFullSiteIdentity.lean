import OAI.Probability.InvariantIsing.Cavity.CavityReplicaLinearity
import OAI.Probability.InvariantIsing.Cavity.CavitySiteSymmetry

namespace OAI

/-! The cavity-spin insertion identity for the actual full perturbed
model, before any restriction of its Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityFullTest {N m depth : ℕ} (μ : Measure (SpecialOrthogonal N))
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  ∫ U, ∫ g, referenceReplicaMean
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g) F
    ∂gaussianCoordinates ∂μ

lemma measurable_cavityFullInner {N m depth : ℕ} (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => referenceReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig (specialRotation p.1) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2) F) := by
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
  change Measurable (fun p => referenceReplicaMean ν (fun x => H (p, x)) F)
  exact measurable_referenceReplicaMean ν (H := H) (D := fun z => F z.2)
    hmH ((measurable_of_countable F).comp measurable_snd)

lemma cavityFullTest_sum {N m depth : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : ι → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i σ, |F i σ| ≤ B) :
    cavityFullTest μ T eig I u (fun σ => ∑ i, F i σ) =
      ∑ i, cavityFullTest μ T eig I u (F i) := by
  exact cavity_nested_replica_sum μ gaussianCoordinates
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ => measurable_of_countable _) (fun i => measurable_cavityFullInner T eig I u (F i)) hB hF

lemma cavityFullTest_const_mul {N m depth : ℕ} (μ : Measure (SpecialOrthogonal N))
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) (c : ℝ) :
    cavityFullTest μ T eig I u (fun σ => c * F σ) = c * cavityFullTest μ T eig I u F := by
  simp only [cavityFullTest, referenceReplicaMean_const_mul, integral_const_mul]

def cavityReplicaOverlap {N depth : ℕ} (σ : Fin 2 → Spin N × LabeledLeaf depth) : ℝ :=
  cavityTotalSpinOverlap ((σ 0).1, (σ 1).1)

lemma cavityReplicaOverlap_signed {N depth : ℕ} (p : Equiv.Perm (Fin N))
    (flip : Fin N → Bool) (σ : Fin 2 → Spin N × LabeledLeaf depth) :
    cavityReplicaOverlap (fun i => (cavitySignedSpinPermutation p flip (σ i).1, (σ i).2)) =
      cavityReplicaOverlap σ := by
  unfold cavityReplicaOverlap cavityTotalSpinOverlap
  simp only [cavitySignedSpinPermutation_pair]
  congr 1
  exact Equiv.sum_comp p (fun i => spinValue ((σ 0).1 i) * spinValue ((σ 1).1 i))

theorem cavity_full_site_identity {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (j : Fin N) :
    cavityFullTest μ T eig I u
      (fun σ => Φ (cavityReplicaOverlap σ) * spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)) =
    cavityFullTest μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) := by
  let F := fun i (σ : Fin 2 → Spin N × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * spinValue ((σ 0).1 i) * spinValue ((σ 1).1 i)
  let a := fun i => cavityFullTest μ T eig I u (F i)
  have hF (i : Fin N) (σ) : |F i σ| ≤ ‖Φ‖ := by
    simpa only [F, abs_mul, abs_spinValue, mul_one, Real.norm_eq_abs] using
      Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  have he (i : Fin N) : a i = a j := by
    have h := cavity_full_signed_site_symmetry hN μ T eig I u hu (Equiv.swap i j)
      (F i) (norm_nonneg _) (hF i)
    change a i = cavityFullTest μ T eig I u _ at h
    rw [show (fun σ => F i (fun k =>
        (cavitySignedSpinPermutation (Equiv.swap i j) (cavityPermutationFlip hN (Equiv.swap i j))
          (σ k).1, (σ k).2))) = F j from ?_] at h
    · exact h
    · funext σ
      dsimp only [F]
      rw [cavityReplicaOverlap_signed, mul_assoc, cavitySignedSpinPermutation_pair,
        Equiv.swap_apply_left]
      ring
  have htotal : (fun σ : Fin 2 → Spin N × LabeledLeaf depth =>
      Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) =
      (fun σ => (N : ℝ)⁻¹ * ∑ i, F i σ) := by
    funext σ
    simp only [F, cavityReplicaOverlap, cavityTotalSpinOverlap, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [htotal, cavityFullTest_const_mul,
    cavityFullTest_sum μ T eig I u F (norm_nonneg _) hF]
  change a j = (N : ℝ)⁻¹ * ∑ i, a i
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

end InvariantIsing

end

end OAI

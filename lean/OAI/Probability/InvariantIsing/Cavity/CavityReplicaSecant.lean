import OAI.Probability.InvariantIsing.Cavity.CavityReplicaLogTilt

namespace OAI

/-! Expected bounded replica tests are controlled by the corresponding
Gaussian log partitions, with a uniform quadratic secant error. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityCylinderLogPartition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) (A : X → ℕ →₀ ℝ) : ℝ :=
  ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
    ∂gaussianCoordinates

def cavityCylinderReplicaMean {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) (A : X → ℕ →₀ ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) : ℝ :=
  ∫ g : ℕ → ℝ, referenceReplicaMean ν (fun x => H x + cylinderField (A x) g) F
    ∂gaussianCoordinates

lemma cavity_replica_sum_bound {X : Type*} (H : X → ℝ) {M : ℝ}
    (hH : ∀ x, |H x| ≤ M) {r : ℕ} (σ : Fin r → X) :
    |∑ i, H (σ i)| ≤ (r : ℝ) * M := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun i _ => hH (σ i)).trans_eq (by simp))

lemma cavity_expected_replica_secant {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) {M V : ℝ} (hH : ∀ x, |H x| ≤ M)
    (A : X → ℕ →₀ ℝ) (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ V)
    {r : ℕ} (F : (Fin r → X) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ σ, |F σ| ≤ B) (s : ℝ) :
    let L := cavityCylinderLogPartition (Measure.pi (fun _ : Fin r => ν))
      (fun σ => (∑ i, H (σ i)) + s * F σ) (fun σ => ∑ i, A (σ i)) -
      (r : ℝ) * cavityCylinderLogPartition ν H A
    s * cavityCylinderReplicaMean ν H A F ≤ L ∧
      L ≤ s * cavityCylinderReplicaMean ν H A F + B ^ 2 * s ^ 2 / 2 := by
  intro L
  let J := fun σ : Fin r → X => (∑ i, H (σ i)) + s * F σ
  let C := fun σ : Fin r → X => ∑ i, A (σ i)
  let π := Measure.pi (fun _ : Fin r => ν)
  have hJ σ : |J σ| ≤ (r : ℝ) * M + |s| * B := by
    exact (abs_add_le _ _).trans (add_le_add (cavity_replica_sum_bound H hH σ)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF σ) (abs_nonneg s)))
  have hC σ : (C σ).sum (fun _ z => z ^ 2) ≤ (r : ℝ)^2 * V := by
    simpa only [Fintype.card_fin] using cylinder_variance_sum_le (fun i => A (σ i)) (fun i => hA (σ i))
  have hiH := (cylinder_log_partition_memLp_two ν H (cavity_bounded_base_exp_integrable ν H hH)
    A hA 1).integrable (by norm_num)
  have hiJ := (cylinder_log_partition_memLp_two π J (cavity_bounded_base_exp_integrable π J hJ)
    C hC 1).integrable (by norm_num)
  simp only [one_mul] at hiH hiJ
  have hmH : Measurable (fun p : (ℕ → ℝ) × X => H p.2 + cylinderField (A p.2) p.1) :=
    ((measurable_of_countable H).comp measurable_snd).add (measurable_cylinderFields A)
  have hmF : Measurable (fun p : (ℕ → ℝ) × (Fin r → X) => F p.2) :=
    (measurable_of_countable F).comp measurable_snd
  have hiF : Integrable (fun g => referenceReplicaMean ν
      (fun x => H x + cylinderField (A x) g) F) gaussianCoordinates :=
    integrable_of_measurable_abs_le (measurable_referenceReplicaMean ν hmH hmF)
      (fun g => referenceReplicaMean_abs_le ν _ F (measurable_of_countable F) hB hF)
  have he (g : ℕ → ℝ) (σ : Fin r → X) : J σ + cylinderField (C σ) g =
      (∑ i, (H (σ i) + cylinderField (A (σ i)) g)) + s * F σ := by
    dsimp only [J, C]
    rw [cylinderField_finset_sum, Finset.sum_add_distrib]
    ring
  have hpoint : ∀ᵐ g ∂gaussianCoordinates,
      s * referenceReplicaMean ν (fun x => H x + cylinderField (A x) g) F ≤
        Real.log (∫ σ, Real.exp (J σ + cylinderField (C σ) g) ∂π) -
        (r : ℝ) * Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν) ∧
      Real.log (∫ σ, Real.exp (J σ + cylinderField (C σ) g) ∂π) -
        (r : ℝ) * Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν) ≤
        s * referenceReplicaMean ν (fun x => H x + cylinderField (A x) g) F + B ^ 2 * s ^ 2 / 2 := by
    filter_upwards [cylinder_partition_exp_integrable_ae ν H (cavity_bounded_base_exp_integrable ν H hH) A hA,
      cylinder_partition_exp_integrable_ae π J (cavity_bounded_base_exp_integrable π J hJ) C hC]
      with g hgH hgJ
    have hgJ' : Integrable (fun σ => Real.exp
        ((∑ i, (H (σ i) + cylinderField (A (σ i)) g)) + s * F σ)) π := by
      simpa only [he] using hgJ
    simpa only [← he] using cavity_replica_cgf_secant ν
      (fun x => H x + cylinderField (A x) g) hgH F hB hF s hgJ'
  have hl := integral_mono_ae (hiF.const_mul s) (hiJ.sub (hiH.const_mul (r : ℝ)))
    (hpoint.mono fun _ h => h.1)
  have hu := integral_mono_ae (hiJ.sub (hiH.const_mul (r : ℝ)))
    ((hiF.const_mul s).add (integrable_const _)) (hpoint.mono fun _ h => h.2)
  simp only [Pi.sub_apply, Pi.add_apply] at hl hu
  simp only [integral_sub hiJ (hiH.const_mul (r : ℝ)), integral_const_mul,
    integral_add (hiF.const_mul s) (integrable_const _), integral_const,
    probReal_univ, one_smul] at hl hu
  exact ⟨hl, hu⟩

end InvariantIsing

end

end OAI

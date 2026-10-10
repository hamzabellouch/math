import OAI.Probability.InvariantIsing.Cavity.CavityReplicaTest

namespace OAI

/-! A bounded Gibbs replica test depends on a centered Gaussian field
only through its covariance, including for the countable leaf prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem cavity_twoReplica_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (F : (Fin 2 → X) → ℝ) {M B₀ B₁ B : ℝ}
    (hH : ∀ x, |H x| ≤ M) (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y))
    (hB : 0 ≤ B) (hF : ∀ σ, |F σ| ≤ B) :
    (∫ g, referenceReplicaMean ν (fun x => H x + cylinderField (C x) g) F
      ∂gaussianCoordinates) =
    ∫ g, referenceReplicaMean ν (fun x => H x + cylinderField (A x) g) F
      ∂gaussianCoordinates := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let s := ε / (B ^ 2 + 1)
  have hs : 0 < s := div_pos hε (by positivity)
  have ht := cavity_twoReplica_test_comparison ν H H F hH hH C A hC hA
    (show (0 : ℝ) ≤ 0 from le_rfl)
    (fun x y => by rw [hcov x y]; simp)
    (by intro x; simp : ∀ x, |H x - H x| ≤ (0 : ℝ)) hB hF hs
  have he : s * (B ^ 2 + 1) = ε := div_mul_cancel₀ _ (by positivity)
  simp only [mul_zero, add_zero, zero_div, zero_add] at ht ⊢
  exact ht.trans (by nlinarith [sq_nonneg B])

/-- Pull back both the energy and the test by a prior-preserving
configuration map. This retains the common Gaussian disorder. -/
theorem cavity_twoReplica_gaussian_transport {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (e : X → X)
    (he : MeasurePreserving e ν ν) (H : X → ℝ) (hH : Measurable H)
    (C : X → ℕ →₀ ℝ) (hC : ∀ g, Measurable (fun x => cylinderField (C x) g))
    (F : (Fin 2 → X) → ℝ) (hF : Measurable F) :
    (∫ g, referenceReplicaMean ν
      (fun x => H (e x) + cylinderField (C (e x)) g)
      (fun σ => F (fun i => e (σ i))) ∂gaussianCoordinates) =
    ∫ g, referenceReplicaMean ν (fun x => H x + cylinderField (C x) g) F
      ∂gaussianCoordinates := by
  apply integral_congr_ae
  exact ae_of_all _ fun g => referenceReplicaMean_map he (hH.add (hC g)) hF

/-- A symmetry of the deterministic energy and Gaussian covariance,
combined with invariance of the disorder and the prior, gives the full
annealed replica-test symmetry. -/
theorem cavity_twoReplica_ensemble_symmetry {Ω X : Type*}
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
    (F : (Fin 2 → X) → ℝ) (hFm : Measurable F) {B : ℝ}
    (hB : 0 ≤ B) (hFb : ∀ σ, |F σ| ≤ B)
    (hmeas : AEStronglyMeasurable (fun ω => ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g) F ∂gaussianCoordinates) μ) :
    (∫ ω, ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g) F ∂gaussianCoordinates ∂μ) =
    ∫ ω, ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g)
      (fun σ => F (fun i => e (σ i))) ∂gaussianCoordinates ∂μ := by
  rw [← hR.hasLaw.integral_comp hmeas]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only [Function.comp_apply]
    have ht := cavity_twoReplica_gaussian_transport ν e he (H (R ω)) (measurable_of_countable _)
      (C (R ω)) (fun _ => measurable_of_countable _) F hFm
    simp_rw [henergy] at ht
    rw [← ht]
    exact (cavity_twoReplica_same_covariance ν (H ω)
      (fun σ => F (fun i => e (σ i))) (hH ω) (C ω) (fun x => C (R ω) (e x))
      (hV ω) (fun x => hV (R ω) (e x)) (hcov ω) hB
      (fun σ => hFb (fun i => e (σ i)))).symm

end InvariantIsing

end

end OAI

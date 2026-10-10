import OAI.Probability.InvariantIsing.Cavity.CavityBoundedSecant
import OAI.Probability.InvariantIsing.Cavity.CavityUniformComparison

namespace OAI

/-! Bounded replica tilts are finite differences of the actual
countable-prior Gaussian log partition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_replica_cgf_eq {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    {r : ℕ} (F : (Fin r → X) → ℝ) (s : ℝ)
    (hF : Integrable (fun σ => Real.exp ((∑ i, H (σ i)) + s * F σ))
      (Measure.pi (fun _ : Fin r => ν))) :
    cgf F (Measure.pi (fun _ : Fin r => ν.tilted H)) s =
      Real.log (∫ σ, Real.exp ((∑ i, H (σ i)) + s * F σ)
        ∂Measure.pi (fun _ : Fin r => ν)) -
      (r : ℝ) * Real.log (∫ x, Real.exp (H x) ∂ν) := by
  rw [cgf, mgf, ← replica_tilted_pi ν H hH r, integral_exp_tilted]
  change Real.log ((∫ σ, Real.exp ((∑ i, H (σ i)) + s * F σ)
      ∂Measure.pi (fun _ : Fin r => ν)) /
      (∫ σ, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ : Fin r => ν))) = _
  rw [reference_replica_partition, referencePartition, Real.log_div (integral_exp_pos hF).ne'
    (pow_pos (integral_exp_pos hH) r).ne', Real.log_pow]

lemma cavity_replica_cgf_secant {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    {r : ℕ} (F : (Fin r → X) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hFb : ∀ σ, |F σ| ≤ B) (s : ℝ)
    (hF : Integrable (fun σ => Real.exp ((∑ i, H (σ i)) + s * F σ))
      (Measure.pi (fun _ : Fin r => ν))) :
    s * referenceReplicaMean ν H F ≤
      Real.log (∫ σ, Real.exp ((∑ i, H (σ i)) + s * F σ)
        ∂Measure.pi (fun _ : Fin r => ν)) -
      (r : ℝ) * Real.log (∫ x, Real.exp (H x) ∂ν) ∧
    Real.log (∫ σ, Real.exp ((∑ i, H (σ i)) + s * F σ)
        ∂Measure.pi (fun _ : Fin r => ν)) -
      (r : ℝ) * Real.log (∫ x, Real.exp (H x) ∂ν) ≤
      s * referenceReplicaMean ν H F + B ^ 2 * s ^ 2 / 2 := by
  let := isProbabilityMeasure_tilted hH
  have hh := cavity_bounded_cgf_secant (Measure.pi (fun _ : Fin r => ν.tilted H)) F
    (measurable_of_countable F) hB hFb s
  rw [cavity_replica_cgf_eq ν H hH F s hF,
    ← referenceReplicaMean_eq_tilted ν H hH] at hh
  exact hh

lemma cavity_replica_covariance_difference {X : Type*} {r : ℕ}
    (A C : X → ℕ →₀ ℝ) {K : ℝ}
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (σ τ : Fin r → X) :
    |cylinderCross (∑ i, A (σ i)) (∑ i, A (τ i)) -
      cylinderCross (∑ i, C (σ i)) (∑ i, C (τ i))| ≤ (r : ℝ)^2 * K := by
  simp only [cylinderCross_finset_left, cylinderCross_sum_right,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin r, ∑ i : Fin r,
        |cylinderCross (A (σ i)) (A (τ j)) - cylinderCross (C (σ i)) (C (τ j))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _j : Fin r, ∑ _i : Fin r, K :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hcov (σ i) (τ j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end InvariantIsing

end

end OAI

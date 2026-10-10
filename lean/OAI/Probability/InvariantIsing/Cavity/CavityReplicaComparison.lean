import OAI.Probability.InvariantIsing.Cavity.CavityReplicaSecant

namespace OAI

/-! Quantitative comparison of bounded replica tests under two Gaussian
cylinder fields. This applies to a fixed cavity cutoff prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem cavity_bounded_replica_comparison {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J : X → ℝ) {M₀ M₁ V₀ V₁ K E : ℝ}
    (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ V₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ V₁)
    (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (hbase : ∀ x, |H x - J x| ≤ E)
    {r : ℕ} (F : (Fin r → X) → ℝ) {B s : ℝ} (hB : 0 ≤ B)
    (hF : ∀ σ, |F σ| ≤ B) (hs : 0 < s) :
    |cavityCylinderReplicaMean ν H C F - cavityCylinderReplicaMean ν J A F| ≤
      (2 * (r : ℝ)^2 * K + 2 * r * K + 2 * r * E) / s + B ^ 2 * s / 2 := by
  let π := Measure.pi (fun _ : Fin r => ν)
  let HH := fun σ : Fin r → X => (∑ i, H (σ i)) + s * F σ
  let JJ := fun σ : Fin r → X => (∑ i, J (σ i)) + s * F σ
  let CC := fun σ : Fin r → X => ∑ i, C (σ i)
  let AA := fun σ : Fin r → X => ∑ i, A (σ i)
  have hHH σ : |HH σ| ≤ (r : ℝ) * M₀ + |s| * B :=
    (abs_add_le _ _).trans (add_le_add (cavity_replica_sum_bound H hH σ)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF σ) (abs_nonneg s)))
  have hJJ σ : |JJ σ| ≤ (r : ℝ) * M₁ + |s| * B :=
    (abs_add_le _ _).trans (add_le_add (cavity_replica_sum_bound J hJ σ)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF σ) (abs_nonneg s)))
  have hCC σ : (CC σ).sum (fun _ z => z ^ 2) ≤ (r : ℝ)^2 * V₀ := by
    simpa only [Fintype.card_fin] using cylinder_variance_sum_le (fun i => C (σ i)) (fun i => hC (σ i))
  have hAA σ : (AA σ).sum (fun _ z => z ^ 2) ≤ (r : ℝ)^2 * V₁ := by
    simpa only [Fintype.card_fin] using cylinder_variance_sum_le (fun i => A (σ i)) (fun i => hA (σ i))
  have hE σ : |HH σ - JJ σ| ≤ (r : ℝ) * E := by
    change |((∑ i, H (σ i)) + s * F σ) - ((∑ i, J (σ i)) + s * F σ)| ≤ _
    rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    exact cavity_replica_sum_bound (fun x => H x - J x) hbase σ
  have hL := countable_cylinder_uniform_comparison π HH JJ hHH hJJ CC AA hCC hAA
    (mul_nonneg (sq_nonneg (r : ℝ)) hK) (cavity_replica_covariance_difference A C hcov) hE
  have hZ := countable_cylinder_uniform_comparison ν H J hH hJ C A hC hA hK hcov hbase
  change |cavityCylinderLogPartition π HH CC - cavityCylinderLogPartition π JJ AA| ≤
    2 * ((r : ℝ)^2 * K) + (r : ℝ) * E at hL
  change |cavityCylinderLogPartition ν H C - cavityCylinderLogPartition ν J A| ≤ 2 * K + E at hZ
  have hd : |(cavityCylinderLogPartition π HH CC - (r : ℝ) * cavityCylinderLogPartition ν H C) -
      (cavityCylinderLogPartition π JJ AA - (r : ℝ) * cavityCylinderLogPartition ν J A)| ≤
      2 * (r : ℝ)^2 * K + 2 * r * K + 2 * r * E := by
    calc
      _ = |(cavityCylinderLogPartition π HH CC - cavityCylinderLogPartition π JJ AA) -
          (r : ℝ) * (cavityCylinderLogPartition ν H C - cavityCylinderLogPartition ν J A)| := by congr 1; ring
      _ ≤ |cavityCylinderLogPartition π HH CC - cavityCylinderLogPartition π JJ AA| +
          |(r : ℝ) * (cavityCylinderLogPartition ν H C - cavityCylinderLogPartition ν J A)| := abs_sub _ _
      _ ≤ (2 * ((r : ℝ)^2 * K) + (r : ℝ) * E) + (r : ℝ) * (2 * K + E) := by
        have hr : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg (Nat.cast_nonneg r)
        simp only [abs_mul, hr]
        exact add_le_add hL (mul_le_mul_of_nonneg_left hZ (Nat.cast_nonneg r))
      _ = _ := by ring
  exact cavity_secant_comparison_algebra hs (cavity_expected_replica_secant ν H hH C hC F hB hF s)
    (cavity_expected_replica_secant ν J hJ A hA F hB hF s) hd

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Cavity.CavityCountableTest

namespace OAI

/-! The bounded-test comparison for the two-replica law used in the
cavity overlap argument. Both replicas share the same Gaussian field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_twoReplica_mean_eq {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (A : X → ℕ →₀ ℝ)
    (F : (Fin 2 → X) → ℝ) (g : ℕ → ℝ) :
    referenceReplicaMean ν (fun x => H x + cylinderField (A x) g) F =
      ∫ σ, F σ ∂(Measure.pi (fun _ : Fin 2 => ν)).tilted
        (fun σ => (∑ i, H (σ i)) + cylinderField (∑ i, A (σ i)) g) := by
  rw [referenceReplicaMean_eq_ratio, integral_tilted_eq_div]
  have he (σ : Fin 2 → X) :
      (∑ i, (H (σ i) + cylinderField (A (σ i)) g)) =
        (∑ i, H (σ i)) + cylinderField (∑ i, A (σ i)) g := by
    rw [cylinderField_finset_sum, Finset.sum_add_distrib]
  simp_rw [he]

lemma cavity_twoReplica_sum_bound {X : Type*} (H : X → ℝ) {M : ℝ}
    (hH : ∀ x, |H x| ≤ M) (σ : Fin 2 → X) : |∑ i, H (σ i)| ≤ 2 * M := by
  rw [Fin.sum_univ_two]
  exact (abs_add_le _ _).trans (by linarith [hH (σ 0), hH (σ 1)])


lemma cavity_twoReplica_covariance_bound {X : Type*}
    (C A : X → ℕ →₀ ℝ) {K : ℝ}
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (σ τ : Fin 2 → X) :
    |cylinderCross (∑ i, A (σ i)) (∑ i, A (τ i)) -
      cylinderCross (∑ i, C (σ i)) (∑ i, C (τ i))| ≤ 4 * K := by
  simp only [cylinderCross_finset_left, cylinderCross_sum_right]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : Fin 2, |∑ j : Fin 2,
        (cylinderCross (A (σ i)) (A (τ j)) - cylinderCross (C (σ i)) (C (τ j)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
        |(cylinderCross (A (σ i)) (A (τ j)) - cylinderCross (C (σ i)) (C (τ j)))| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, K :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov (σ i) (τ j)))
    _ = 4 * K := by simp; ring

theorem cavity_twoReplica_test_comparison {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J : X → ℝ) (F : (Fin 2 → X) → ℝ) {M₀ M₁ B₀ B₁ K E B s : ℝ}
    (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (hbase : ∀ x, |H x - J x| ≤ E) (hB : 0 ≤ B)
    (hF : ∀ σ, |F σ| ≤ B) (hs : 0 < s) :
    |(∫ g : ℕ → ℝ, referenceReplicaMean ν
        (fun x => H x + cylinderField (C x) g) F ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, referenceReplicaMean ν
        (fun x => J x + cylinderField (A x) g) F ∂gaussianCoordinates| ≤
      (16 * K + 4 * E) / s + B ^ 2 * s / 2 := by
  have hcv (σ : Fin 2 → X) : (∑ i, C (σ i)).sum (fun _ z => z ^ 2) ≤ 4 * B₀ := by
    have hh := cylinder_variance_sum_le (fun i : Fin 2 => C (σ i)) (fun i => hC (σ i))
    norm_num at hh
    simpa only [Fin.sum_univ_two] using hh
  have hav (σ : Fin 2 → X) : (∑ i, A (σ i)).sum (fun _ z => z ^ 2) ≤ 4 * B₁ := by
    have hh := cylinder_variance_sum_le (fun i : Fin 2 => A (σ i)) (fun i => hA (σ i))
    norm_num at hh
    simpa only [Fin.sum_univ_two] using hh
  have hb (σ : Fin 2 → X) : |(∑ i, H (σ i)) - ∑ i, J (σ i)| ≤ 2 * E := by
    rw [← Finset.sum_sub_distrib]
    exact cavity_twoReplica_sum_bound (fun x => H x - J x) hbase σ
  have ht := cavity_countable_test_comparison (Measure.pi (fun _ : Fin 2 => ν))
    (fun σ => ∑ i, H (σ i)) (fun σ => ∑ i, J (σ i)) F
    (cavity_twoReplica_sum_bound H hH) (cavity_twoReplica_sum_bound J hJ)
    (fun σ => ∑ i, C (σ i)) (fun σ => ∑ i, A (σ i)) hcv hav
    (show 0 ≤ 4 * K by positivity) (cavity_twoReplica_covariance_bound C A hcov)
    hb hB hF hs
  simp_rw [← cavity_twoReplica_mean_eq] at ht
  convert ht using 1
  ring

end InvariantIsing

end

end OAI

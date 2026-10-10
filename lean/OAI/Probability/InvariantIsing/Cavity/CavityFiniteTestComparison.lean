import OAI.Probability.InvariantIsing.Cavity.CavityReplicaComparison
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteIncrement

namespace OAI

/-! On a fixed geometric cutoff, the full perturbed model and the base
model tilted by the unperturbed cavity energy have the same bounded
replica tests up to explicit vanishing perturbation errors. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem cavity_finite_cutoff_test_comparison {N n m depth r : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (hw : ∀ x, 1 ≤ w x)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (herr : ∀ x y a, |projectedOverlap U (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
      projectedOverlap V (J a) x.1 y.1| ≤ C / N * (w x + w y))
    (ν : Measure {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D})
    [IsProbabilityMeasure ν]
    (Φ : (Fin r → {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D}) → ℝ)
    {B s : ℝ} (hB : 0 ≤ B) (hΦ : ∀ σ, |Φ σ| ≤ B) (hs : 0 < s) :
    let H := fun x : {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D} =>
      rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.val.1.1 +
        t * (rotatedEnergy eig U (cavityJoinedSpin x.val.1) - rotatedEnergy eig₀ V x.val.1.1)
    let F := fun x : {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D} =>
      rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x.val.1)
    let A := fun x : {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D} =>
      cavityPerturbationCoefficients U I u depth (cavityJoinedSpin x.val.1, x.val.2)
    let A₀ := fun x : {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D} =>
      cavityPerturbationCoefficients V J u depth (x.val.1.1, x.val.2)
    let K := cavityCovarianceRate n C N * (2 * D)
    let E := cavityDeterministicRate n m (2 * C) N * D
    |cavityCylinderReplicaMean ν H A₀ Φ - cavityCylinderReplicaMean ν F A Φ| ≤
      (2 * (r : ℝ)^2 * K + 2 * r * K + 2 * r * E) / s + B ^ 2 * s / 2 := by
  intro H F A A₀ K E
  have hdet : 0 ≤ cavityDeterministicRate n m (2 * C) N := by
    unfold cavityDeterministicRate perturbationScale
    positivity
  have hcov := cavityCovarianceRate_nonneg n hC N
  obtain ⟨M, hM⟩ := Finite.exists_le (fun x : Spin N × Spin n =>
    |rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.1 +
      t * (rotatedEnergy eig U (cavityJoinedSpin x) - rotatedEnergy eig₀ V x.1)|)
  obtain ⟨L, hL⟩ := Finite.exists_le (fun x : Spin N × Spin n =>
    |rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x)|)
  apply cavity_bounded_replica_comparison ν H F (fun x => hM x.val.1) (fun x => hL x.val.1)
    A₀ A (fun x => cavityPerturbationCoefficients_sq_le V J u hu (x.val.1.1, x.val.2))
    (fun x => cavityPerturbationCoefficients_sq_le U I u hu (cavityJoinedSpin x.val.1, x.val.2))
    (mul_nonneg hcov (by linarith)) ?_ ?_ Φ hB hΦ hs
  · intro x y
    have hh := cavity_actual_covariance_rate hN U V I J u hu
      (cavityJoinedSpin x.val.1) (cavityJoinedSpin y.val.1) x.val.1.1 y.val.1.1 x.val.2 y.val.2 hC
      (by linarith [hw x.val.1, hw y.val.1]) (herr x.val.1 y.val.1)
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [x.property, y.property]) hcov)
  · intro x
    have hh := cavity_actual_diagonal_rate hN U V I J eig eig₀ v hv t
      (cavityJoinedSpin x.val.1) x.val.1.1 (hw x.val.1) (C := 2 * C)
      (fun a => by
        have ha := herr x.val.1 x.val.1 a
        convert ha using 1
        ring)
    have he : H x - F x = -((rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U
        (cavityJoinedSpin x.val.1) - t * rotatedEnergy eig U (cavityJoinedSpin x.val.1)) -
        (rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.val.1.1 -
          t * rotatedEnergy eig₀ V x.val.1.1)) := by dsimp only [H, F]; ring
    rw [he, abs_neg]
    exact hh.trans (mul_le_mul_of_nonneg_left x.property hdet)

end InvariantIsing

end

end OAI

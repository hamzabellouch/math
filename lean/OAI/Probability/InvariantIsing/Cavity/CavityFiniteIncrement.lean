import OAI.Probability.InvariantIsing.Cavity.CavityActualErrorRates
import OAI.Probability.InvariantIsing.Cavity.CavityIncrementComparison

namespace OAI

/-! Finite cavity comparison for the actual Ising energies and tensor
perturbations. The reference law may include a countable cascade leaf. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityJoinedSpin {N n : ℕ} (x : Spin N × Spin n) : Spin (N + n) :=
  Fin.append x.1 x.2

/-- Conditional on the coupled spectral geometry, the actual finite
perturbations cost a vanishing coefficient times the special-coordinate
penalty. The Gaussian perturbation stays inside the base Gibbs law. -/
theorem cavity_finite_energy_increment {N n m depth : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    (ν : Measure ((Spin N × Spin n) × LabeledLeaf depth)) [IsProbabilityMeasure ν]
    (w : Spin N × Spin n → ℝ) (hw : ∀ x, 1 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C)
    (herr : ∀ x y a, |projectedOverlap U (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
      projectedOverlap V (J a) x.1 y.1| ≤ C / N * (w x + w y)) :
    let H := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.1.1
    let W := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      t * (rotatedEnergy eig U (cavityJoinedSpin x.1) - rotatedEnergy eig₀ V x.1.1)
    let F := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x.1)
    let A := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      cavityPerturbationCoefficients U I u depth (cavityJoinedSpin x.1, x.2)
    let B := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      cavityPerturbationCoefficients V J u depth (x.1.1, x.2)
    let δ := cavityDeterministicRate n m (2 * C) N + 2 * cavityCovarianceRate n C N
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (W x - δ * w x.1)
      ∂ν.tilted (fun x => H x + cylinderField (B x) g)) ∂gaussianCoordinates) ≤
      (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (F x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (B x) g) ∂ν)
        ∂gaussianCoordinates := by
  dsimp only
  let H₀ := fun x : Spin N × Spin n =>
    rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.1
  let W₀ := fun x : Spin N × Spin n =>
    t * (rotatedEnergy eig U (cavityJoinedSpin x) - rotatedEnergy eig₀ V x.1)
  let F₀ := fun x : Spin N × Spin n =>
    rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x)
  obtain ⟨M, hM⟩ := Finite.exists_le (fun x => |H₀ x|)
  obtain ⟨L, hL⟩ := Finite.exists_le (fun x => |W₀ x|)
  obtain ⟨M₁, hM₁⟩ := Finite.exists_le (fun x => |F₀ x|)
  obtain ⟨D, hD⟩ := Finite.exists_le (fun x => |w x|)
  apply cavity_log_increment_comparison ν
    (fun x => H₀ x.1) (fun x => W₀ x.1) (fun x => F₀ x.1) (fun x => w x.1)
    (cavityCovarianceRate n C N) (cavityDeterministicRate n m (2 * C) N)
    (fun x => hM x.1) (fun x => hL x.1) (fun x => hM₁ x.1) (fun x => hD x.1)
  · intro x
    have hh := cavity_actual_diagonal_rate hN U V I J eig eig₀ v hv t
      (cavityJoinedSpin x.1) x.1.1 (hw x.1) (C := 2 * C) (fun a => by
        have ha := herr x.1 x.1 a
        convert ha using 1; ring)
    convert hh using 1; dsimp only [H₀, W₀, F₀]; congr 1; ring
  · intro x
    exact cavityPerturbationCoefficients_sq_le V J u hu (x.1.1, x.2)
  · intro x
    exact cavityPerturbationCoefficients_sq_le U I u hu (cavityJoinedSpin x.1, x.2)
  · intro x y
    exact cavity_actual_covariance_rate hN U V I J u hu
      (cavityJoinedSpin x.1) (cavityJoinedSpin y.1) x.1.1 y.1.1 x.2 y.2 hC
      (by linarith [hw x.1, hw y.1]) (herr x.1 y.1)

end InvariantIsing

end

end OAI

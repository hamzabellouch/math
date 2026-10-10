import OAI.Probability.InvariantIsing.Cavity.CavityComparisonRates
import OAI.Probability.InvariantIsing.Arrays.TensorProfiles
import OAI.Probability.InvariantIsing.Arrays.MonomialEnumeration

namespace OAI

/-! The cavity error bound for the actual finite Gaussian perturbation:
the spectral/tree monomials, their amplitudes and dimension cutoff are
kept explicit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityPerturbationCoefficients {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (depth : ℕ)
    (x : Spin N × LabeledLeaf depth) : ℕ →₀ ℝ :=
  tensorLeafCoefficients U I (fun j : Fin N => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N (fun j => u j)) depth
    (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
      depth (fun j => enumeratedTreeDegree m j) (fun _ => 0) i) x

def cavityPerturbationKernel {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (x y : Spin N × LabeledLeaf depth) (j : ℕ) : ℝ :=
  (∏ a, projectedOverlap U (I a) x.1 y.1 ^ enumeratedSpectralDegree m j a) *
    treeOverlap depth x.2 y.2 ^ enumeratedTreeDegree m j

lemma cavityPerturbationCoefficients_cross {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (x y : Spin N × LabeledLeaf depth) :
    cylinderCross (cavityPerturbationCoefficients U I u depth x)
      (cavityPerturbationCoefficients U I u depth y) =
      (N * perturbationScale N ^ 2) * cavityWeightedKernel N u (cavityPerturbationKernel U I x y) := by
  rw [cavityPerturbationCoefficients, cavityPerturbationCoefficients,
    tensorPathProfile_covariance U I _ _ depth _ (fun _ => 0) monotone_const le_rfl]
  simp only [zero_mul, Finset.sum_const_zero, zero_add, tensorPerturbationAmplitude, mul_pow, perturbationAmplitude_sq,
    cavityWeightedKernel, Finset.mul_sum, cavityPerturbationKernel]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma cavityPerturbationKernel_abs_le {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (x y : Spin N × LabeledLeaf depth) (j : ℕ) :
    |cavityPerturbationKernel U I x y j| ≤ 1 := by
  rw [cavityPerturbationKernel, abs_mul, abs_pow]
  have hT : |treeOverlap depth x.2 y.2| ≤ 1 := by
    rw [abs_of_nonneg (treeOverlap_mem depth x.2 y.2).1]
    exact (treeOverlap_mem depth x.2 y.2).2
  exact (mul_le_mul (spectralMonomial_abs_le_one U I _ x.1 y.1)
    (pow_le_one₀ (abs_nonneg _) hT) (pow_nonneg (abs_nonneg _) _) (by norm_num)).trans_eq
      (one_mul 1)

lemma cavityPerturbationCoefficients_sq_le {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (x : Spin N × LabeledLeaf depth) :
    (cavityPerturbationCoefficients U I u depth x).sum (fun _ z => z ^ 2) ≤
      4 * (N * perturbationScale N ^ 2) := by
  rw [← cylinderCross_self, cavityPerturbationCoefficients_cross]
  have hb := cavityWeightedKernel_abs_le N u (cavityPerturbationKernel U I x x) hu
    (cavityPerturbationKernel_abs_le U I x x)
  have ha : 0 ≤ (N : ℝ) * perturbationScale N ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 ha
  simpa only [mul_comm] using hh

lemma cavityPerturbationKernel_difference {N M m depth : ℕ}
    (U : Rotation N) (V : Rotation M)
    (I : Fin m → Finset (Fin N)) (J : Fin m → Finset (Fin M))
    (σ₁ σ₂ : Spin N) (τ₁ τ₂ : Spin M) (α β : LabeledLeaf depth)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (herr : ∀ a, |projectedOverlap U (I a) σ₁ σ₂ - projectedOverlap V (J a) τ₁ τ₂| ≤ δ)
    (j : ℕ) :
    |cavityPerturbationKernel U I (σ₁, α) (σ₂, β) j -
      cavityPerturbationKernel V J (τ₁, α) (τ₂, β) j| ≤ ((j : ℝ) + 1) * δ := by
  have ht : |treeOverlap depth α β| ≤ 1 := by
    rw [abs_of_nonneg (treeOverlap_mem depth α β).1]
    exact (treeOverlap_mem depth α β).2
  have h := cavity_spectral_tree_kernel_difference
    (fun a => projectedOverlap U (I a) σ₁ σ₂) (fun a => projectedOverlap V (J a) τ₁ τ₂)
    (enumeratedSpectralDegree m j) (enumeratedTreeDegree m j) (treeOverlap depth α β)
    (fun a => projectedOverlap_abs_le_one U (I a) σ₁ σ₂)
    (fun a => projectedOverlap_abs_le_one V (J a) τ₁ τ₂) ht herr
  exact h.trans (mul_le_mul_of_nonneg_right (enumeratedSpectralDegree_real_sum_le m j) hδ)

/-- The actual covariance error, including the additional monomials at
dimension N+n, is controlled by the same vanishing rate. -/
theorem cavity_actual_covariance_error {N n m depth : ℕ}
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (σ₁ σ₂ : Spin (N + n)) (τ₁ τ₂ : Spin N) (α β : LabeledLeaf depth)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (herr : ∀ a, |projectedOverlap U (I a) σ₁ σ₂ - projectedOverlap V (J a) τ₁ τ₂| ≤ δ) :
    |cylinderCross (cavityPerturbationCoefficients U I u depth (σ₁, α))
        (cavityPerturbationCoefficients U I u depth (σ₂, β)) -
      cylinderCross (cavityPerturbationCoefficients V J u depth (τ₁, α))
        (cavityPerturbationCoefficients V J u depth (τ₂, β))| ≤
      4 * |(N + n) * perturbationScale (N + n) ^ 2 - N * perturbationScale N ^ 2| +
        4 * (N * perturbationScale N ^ 2) * δ +
        4 * ((N + n) * perturbationScale (N + n) ^ 2) * (1 / 2 : ℝ) ^ N := by
  rw [cavityPerturbationCoefficients_cross, cavityPerturbationCoefficients_cross]
  have hh := cavityWeightedKernel_amplitude_difference (d := δ)
    (a := (N : ℝ) * perturbationScale N ^ 2)
    (b := ((N + n : ℕ) : ℝ) * perturbationScale (N + n) ^ 2) N n u
    (cavityPerturbationKernel U I (σ₁, α) (σ₂, β))
    (cavityPerturbationKernel V J (τ₁, α) (τ₂, β)) hu
    (cavityPerturbationKernel_abs_le U I _ _) hδ (by positivity) (by positivity)
    (cavityPerturbationKernel_difference U V I J σ₁ σ₂ τ₁ τ₂ α β hδ herr)
  simpa only [Nat.cast_add] using hh

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Arrays.TensorContactMinimum
import OAI.Probability.InvariantIsing.Spectral.SpectralTemperatureFunctional

namespace OAI

/-! Uniform temperature control of the actual contact objective keeps a
negative minimum away from the zero-temperature boundary. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma tensorContactObjective_temperature_modulus {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (trial : OverlapPath) (δ S : ℝ) (p : TensorContactParameter N m n)
    (ha : ∀ i, 0 ≤ p.2.1 i) (K : ℝ) (heig : ∀ i, |eig i| ≤ K)
    (hlam : ∀ a, |lam a| ≤ K) (s : ℝ) :
    |tensorContactObjective μ eig c I b w S
        (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t + t * δ) p -
      tensorContactObjective μ eig c I b w S
        (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t + t * δ)
        (s, p.2.1, p.2.2.1, p.2.2.2)| ≤ (K + |δ|) * |p.1 - s| := by
  let P := fun t => tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I p.2.2.2 t)
    c I (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
  let G := finiteTemperatureFunctional ρ lam hρ hρsum trial
  have hP : |P p.1 - P s| ≤ (K / 2) * |p.1 - s| :=
    tensorNamespacedMeanPressure_temperature_modulus hN μ eig c I p.2.2.2
      (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
      n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
      (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0) K heig p.1 s
  have hG : |G p.1 - G s| ≤ (K / 2) * |p.1 - s| :=
    finiteTemperatureFunctional_modulus ρ lam hρ hρsum trial K hlam p.1 s
  change |(-P p.1 - _ / 2 + S + (G p.1 + p.1 * δ) + _ + _) -
    (-P s - _ / 2 + S + (G s + s * δ) + _ + _)| ≤ _
  have he : (-P p.1 - (∑ i, w i * finiteFieldPath p.2.1 i) / 2 + S +
      (G p.1 + p.1 * δ) + (∑ j : Fin N, perturbationWeight j * (p.2.2.1 j - 3 / 2) ^ 2) +
      (∑ a, (p.2.2.2 a - 3 / 2) ^ 2)) -
    (-P s - (∑ i, w i * finiteFieldPath p.2.1 i) / 2 + S +
      (G s + s * δ) + (∑ j : Fin N, perturbationWeight j * (p.2.2.1 j - 3 / 2) ^ 2) +
      (∑ a, (p.2.2.2 a - 3 / 2) ^ 2)) =
      -(P p.1 - P s) + (G p.1 - G s) + (p.1 - s) * δ := by ring
  rw [he]
  calc
    _ ≤ |P p.1 - P s| + |G p.1 - G s| + |(p.1 - s) * δ| := by
      simpa only [abs_neg] using (abs_add_le (-(P p.1 - P s) + (G p.1 - G s))
        ((p.1 - s) * δ)).trans
        (add_le_add (abs_add_le (-(P p.1 - P s)) (G p.1 - G s)) (le_refl _))
    _ ≤ (K / 2) * |p.1 - s| + (K / 2) * |p.1 - s| + |(p.1 - s) * δ| :=
      add_le_add (add_le_add hP hG) (le_refl _)
    _ = _ := by rw [abs_mul]; ring


lemma tensorContact_temperature_lower_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (trial : OverlapPath) (δ S : ℝ) (p : TensorContactParameter N m n)
    (ha : ∀ i, 0 ≤ p.2.1 i) (ht : 0 ≤ p.1) (hδ : 0 ≤ δ)
    (K : ℝ) (heig : ∀ i, |eig i| ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (hpos : 0 < K + δ) (η ε : ℝ) (hε : ε ≤ η / 2)
    (hneg : tensorContactObjective μ eig c I b w S
      (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t + t * δ) p ≤ -η)
    (hzero : -ε ≤ tensorContactObjective μ eig c I b w S
      (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t + t * δ)
        (0, p.2.1, p.2.2.1, p.2.2.2)) :
    η / (2 * (K + δ)) ≤ p.1 := by
  have hm := tensorContactObjective_temperature_modulus hN μ eig c I b w
    ρ lam hρ hρsum trial δ S p ha K heig hlam 0
  rw [abs_of_nonneg hδ, sub_zero, abs_of_nonneg ht] at hm
  have hab := neg_le_abs
    (tensorContactObjective μ eig c I b w S
        (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t + t * δ) p -
      tensorContactObjective μ eig c I b w S
        (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t + t * δ)
          (0, p.2.1, p.2.2.1, p.2.2.2))
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hpos)).mpr
  nlinarith

end InvariantIsing

end

end OAI

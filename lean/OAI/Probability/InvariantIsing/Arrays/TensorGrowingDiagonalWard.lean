import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalWardLimit

namespace OAI

/-! Diagonal Ward equations for growing cascade depth, using the same
depth-independent finite Gaussian/Haar error bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorGrowingArrayLaw_diagonalWard_limit
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (m : ℕ) (depth : ℕ → ℕ) (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (degree : (k : ℕ) → Fin (N k) → Fin m → ℕ) (treeDegree : (k : ℕ) → Fin (N k) → ℕ)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ k r, (∑ j, (degree k r j : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (κ : ℕ → Fin m → ℝ) (ρ₀ κ₀ : Fin m → ℝ)
    (hρ : Tendsto (fun k j => ((I k j).card : ℝ) / N k) atTop (𝓝 ρ₀))
    (hκ : Tendsto κ atTop (𝓝 κ₀)) (a d : Fin m)
    (had : ∀ k, Disjoint (I k a) (I k d))
    (ha : ∀ k i, i ∈ I k a → eig k i = κ k a)
    (hd : ∀ k i, i ∈ I k d → eig k i = κ k d)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorNamespacedArrayLaw (μ k) (eig k) (c k) (I k) (degree k)
      (tensorPerturbationAmplitude (N k) (u k)) (depth k) (b k) (treeDegree k) (h k)) atTop (𝓝 Q)) :
    spectralDiagonalWardResidual Q ρ₀ κ₀ a d = 0 := by
  have hε : Tendsto (fun k => 48 * D * perturbationScale (N k) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (tendsto_const_nhds.mul ((perturbationScale_tendsto.comp hNlim).pow 2) :
        Tendsto (fun k => 48 * D * perturbationScale (N k) ^ 2) atTop (𝓝 (48 * D * 0 ^ 2)))
  apply spectralDiagonalWardResidual_zero_of_vanishing_bound hL hρ hκ a d hε
  intro k
  have : (μ k).IsMulLeftInvariant := hμinv k
  exact tensorNamespacedArrayLaw_diagonalWard_bound (hN k) (μ k) (eig k) (c k) (I k) (degree k)
    (treeDegree k) (u k) (hu k) D hD (hdegree k) (b k) (h k) (hh k) (h0 k) (κ k) a d
    (had k) (ha k) (hd k)

end InvariantIsing

end

end OAI

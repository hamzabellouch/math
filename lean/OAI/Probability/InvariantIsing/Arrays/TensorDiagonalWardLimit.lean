import OAI.Probability.InvariantIsing.Arrays.TensorArrayDiagonalWard
import OAI.Probability.InvariantIsing.Arrays.TensorGGRate

namespace OAI

/-! Actual enriched spectral-array limits satisfy the diagonal Ward equation.
The vanishing finite residual is proved by Gaussian/Haar calculus. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorNamespacedArrayLaw_diagonalWard_limit
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (m n : ℕ) (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (degree : (k : ℕ) → Fin (N k) → Fin m → ℕ) (treeDegree : (k : ℕ) → Fin (N k) → ℕ)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ k r, (∑ j, (degree k r j : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (κ : ℕ → Fin m → ℝ) (ρ₀ κ₀ : Fin m → ℝ)
    (hρ : Tendsto (fun k j => ((I k j).card : ℝ) / N k) atTop (𝓝 ρ₀))
    (hκ : Tendsto κ atTop (𝓝 κ₀)) (a d : Fin m)
    (had : ∀ k, Disjoint (I k a) (I k d))
    (ha : ∀ k i, i ∈ I k a → eig k i = κ k a)
    (hd : ∀ k i, i ∈ I k d → eig k i = κ k d)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorNamespacedArrayLaw (μ k) (eig k) (c k) (I k) (degree k)
      (tensorPerturbationAmplitude (N k) (u k)) n b (treeDegree k) (h k)) atTop (𝓝 Q)) :
    spectralDiagonalWardResidual Q ρ₀ κ₀ a d = 0 := by
  have hε : Tendsto (fun k => 48 * D * perturbationScale (N k) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (tendsto_const_nhds.mul ((perturbationScale_tendsto.comp hNlim).pow 2) :
        Tendsto (fun k => 48 * D * perturbationScale (N k) ^ 2) atTop (𝓝 (48 * D * 0 ^ 2)))
  apply spectralDiagonalWardResidual_zero_of_vanishing_bound hL hρ hκ a d hε
  intro k
  have : (μ k).IsMulLeftInvariant := hμinv k
  exact tensorNamespacedArrayLaw_diagonalWard_bound (hN k) (μ k) (eig k) (c k) (I k) (degree k)
    (treeDegree k) (u k) (hu k) D hD (hdegree k) b (h k) (hh k) (h0 k) (κ k) a d
    (had k) (ha k) (hd k)

/-- Under the independently proved constant limiting diagonals, the
actual diagonal Ward equation has the manuscript's projected-product form. -/
theorem tensorNamespacedArrayLaw_diagonalWard_equation {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1))) (ρ eig : Fin m → ℝ) (a b : Fin m)
    (q : Fin (m + 1) → ℝ)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = q j)
    (hward : spectralDiagonalWardResidual Q ρ eig a b = 0) :
    ρ b * q a.castSucc - ρ a * q b.castSucc =
      (eig a - eig b) * (q a.castSucc * q b.castSucc -
        ∫ x, (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ)
          ∂(Q : Measure (SpectralArray (m + 1)))) := by
  rw [spectralDiagonalWardResidual_constant_diagonal Q ρ eig a b q hd] at hward
  linarith

end InvariantIsing

end

end OAI

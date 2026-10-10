import OAI.Probability.InvariantIsing.Arrays.TensorWardLimit

namespace OAI

/-! Off-diagonal Ward equations with growing cascade depth. The finite
rotation and Gaussian error bound is independent of that depth. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorGrowingArrayLaw_off_ward_limit
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m : ℕ) (depth : ℕ → ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (degree : (k : ℕ) → Fin (N k) → Fin m → ℕ)
    (treeDegree : (k : ℕ) → Fin (N k) → ℕ)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ k r, (∑ a, (degree k r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (κ : ℕ → Fin m → ℝ) (hκ : ∀ k a i, i ∈ I k a → eig k i = κ k a)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorNamespacedArrayLaw (μ k) (eig k) (c k) (I k) (degree k)
      (tensorPerturbationAmplitude (N k) (u k)) (depth k) (b k) (treeDegree k) (h k)) atTop (𝓝 Q))
    (ρ₀ κ₀ : Fin m → ℝ)
    (hρ : Tendsto (fun k a => (I k a).card / (N k : ℝ)) atTop (𝓝 ρ₀))
    (hκlim : Tendsto κ atTop (𝓝 κ₀)) (a b₀ : Fin m)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (B : ℝ) (hB : 0 ≤ B) (hΦB : ∀ r, |Φ r| ≤ B) :
    spectralOffWardResidual Q ρ₀ κ₀ a b₀ Φ = 0 := by
  classical
  by_cases hab : a = b₀
  · subst b₀
    simp [spectralOffWardResidual]
  have he : Tendsto (fun k => 192 * B * D * perturbationScale (N k) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (tendsto_const_nhds.mul ((perturbationScale_tendsto.comp hNlim).pow 2) :
        Tendsto (fun k => 192 * B * D * perturbationScale (N k) ^ 2) atTop
          (𝓝 (192 * B * D * 0 ^ 2)))
  apply spectralOffWardResidual_zero_of_vanishing_bound hL hρ hκlim a b₀ Φ hΦ he
  intro k
  have : (μ k).IsMulLeftInvariant := hμinv k
  exact tensorNamespacedArrayLaw_off_ward_bound (hN k) (μ k) (eig k) (c k) (I k)
    (hdis k) (hcover k) (degree k) (treeDegree k) (u k) (hu k) D hD (hdegree k)
    (b k) (h k) (hh k) (h0 k) (κ k) a b₀ ((hdis k) (Set.mem_univ a) (Set.mem_univ b₀) hab)
    (hκ k a) (hκ k b₀) Φ hΦ B hB hΦB

end InvariantIsing

end

end OAI

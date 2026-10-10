import OAI.Probability.InvariantIsing.Cavity.CavityCoupledEnergy
import OAI.Probability.InvariantIsing.Cavity.CavityGeometricTest
import OAI.Probability.InvariantIsing.Cavity.CavityOriginalWeightedComparison

namespace OAI

/-! The actual original-model cutoff comparison in base Gibbs variables,
with its weight identified as the physical finite-block cavity factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavity_geometric_weighted_test {N n m d depth : ℕ} (hN : 0 < N)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (T₀ : LabeledTree depth) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    {D M s : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) (hs : 0 < s)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    ∃ V : Orthogonal N,
      cavityPhysicalBase g lam B (Matrix.diagonal (fun j => lam (a₀ j)))
        (cavitySpecialOrthogonal U) =
        (V : Matrix (Fin N) (Fin N) ℝ) *
          Matrix.diagonal (fun j => Sum.elim (fun w => lam w.1)
            (fun j => lam (a₀ j)) (e.symm j)) *
          (V : Matrix (Fin N) (Fin N) ℝ).transpose ∧
      cavityPhysicalSpecial g B (cavitySpecialOrthogonal U) =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e ∧
      let eig₀ := fun j => Sum.elim (fun w => lam w.1) (fun j => lam (a₀ j)) (e.symm j)
      let B₁ := B (cavityCompressionGrams g (cavitySpecialOrthogonal U))
      let Ds := cavityRepeatedSpectrum (n := n) lam
      let Ts := cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U))
      let y := fun σ : Spin N => (cavityCanonicalSpecial e).transpose *ᵥ
        (matrixRotation V⁻¹ (spinVector σ)).ofLp
      let μ := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T₀
      let w := cavityGeometricWeight g B₁ U
      |(∫ z, cavityWeightedReplicaMean
          ((μ.tilted (cavityRotationHamiltonian (matrixRotation V⁻¹)
            (diagonalPerturbedEigenvalues eig₀ (cavityBaseGroup k e a₀) v t)
            (cavityBaseGroup k e a₀) u z)).prod (uniformSpinPrior n))
          ({x : (Spin N × LabeledLeaf depth) × Spin n |
            1 + ‖(WithLp.toLp 2 (y x.1.1) : EuclideanSpace ℝ (Fin d))‖^2 ≤ D}.indicator
              (fun x => Real.exp (t * cavityLogFactor
                (B₁.transpose * Ds * B₁ - Matrix.diagonal (fun j => lam (a₀ j)))
                (B₁.transpose * Ds * Ts) (Ts.transpose * Ds * Ts) (y x.1.1) x.2)))
          (fun σ => F (fun i => cavityPairLeafUnswap (σ i))) ∂gaussianCoordinates) -
        (∫ z, cavityCutoffReplicaMean
          (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T₀)
          (cavityRotationHamiltonian (specialRotation U)
            (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
            (cavitySpectralGroup g) u z)
          {x | w (cavitySpinSplit N n x.1) ≤ D}
          (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates)| ≤
        (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
          2 * 2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
          2 * 2 * (cavityDeterministicRate n m (2*(2*n+1)) N * D)) / s + M^2*s/2 := by
  obtain ⟨V, hV, hVS, herr₀⟩ := cavity_coupled_spectral_overlap
    hN g k ek e es U lam a₀ B hB hBT hA
  refine ⟨V, hV, hVS, ?_⟩
  dsimp only
  let eig₀ := fun j => Sum.elim (fun w => lam w.1) (fun j => lam (a₀ j)) (e.symm j)
  let B₁ := B (cavityCompressionGrams g (cavitySpecialOrthogonal U))
  let w := cavityGeometricWeight g B₁ U
  have herr (x z : Spin N × Spin n) (a : Fin m) :
      |projectedOverlap (specialRotation U) (cavitySpectralGroup g a)
        (cavityJoinedSpin x) (cavityJoinedSpin z) -
        projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a) x.1 z.1| ≤
        (2 * (n : ℝ) + 1) / N * (w x + w z) := by
    have h := herr₀ a (cavityJoinedSpin x) (cavityJoinedSpin z)
    simp only [cavityJoinedSpin, Fin.append_left] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (Nat.cast_nonneg N))
    dsimp only [w, cavityGeometricWeight, B₁, cavityJoinedSpin]
    linarith
  have hc := cavity_original_weighted_comparison hN (specialRotation U) (matrixRotation V⁻¹)
    T₀ (cavitySpectralGroup g) (cavityBaseGroup k e a₀) (fun i => lam (g i)) eig₀
    v hv u hu t w (cavityGeometricWeight_one_le g B₁ U) (by positivity) hD hM hs herr F hF
  have hw (x : (Spin N × LabeledLeaf depth) × Spin n) :
      w (cavityPairLeafUnswap x).1 =
        1 + ‖(WithLp.toLp 2 ((cavityCanonicalSpecial e).transpose *ᵥ
          (matrixRotation V⁻¹ (spinVector x.1.1)).ofLp) : EuclideanSpace ℝ (Fin d))‖^2 := by
    dsimp only [w, cavityGeometricWeight, cavityPairLeafUnswap]
    rw [← WithLp.toLp_ofLp 2 (cavityFullSpecialCoordinates g B₁ U
      (cavityJoinedSpin (x.1.1,x.2))),
      cavity_coupled_special_coordinates g U B hBT hA V _ hVS x.1.1 x.2]
  have he (x : (Spin N × LabeledLeaf depth) × Spin n) :=
    cavity_coupled_energy_difference g es U lam (fun j => lam (a₀ j)) B hB hBT hA
      V eig₀ (cavityCanonicalSpecial e) hV hVS x.1.1 x.2
  have hcut : (cavityPairLeafUnswap ⁻¹'
      {x : (Spin N × Spin n) × LabeledLeaf depth | w x.1 ≤ D}) =
      {x : (Spin N × LabeledLeaf depth) × Spin n |
        1 + ‖(WithLp.toLp 2 ((cavityCanonicalSpecial e).transpose *ᵥ
          (matrixRotation V⁻¹ (spinVector x.1.1)).ofLp) : EuclideanSpace ℝ (Fin d))‖^2 ≤ D} := by
    ext x
    change w (cavityPairLeafUnswap x).1 ≤ D ↔ _
    rw [hw]
    rfl
  dsimp only at hc he
  rw [hcut] at hc
  simpa only [he, eig₀, B₁, w, cavityPairLeafUnswap] using hc

end InvariantIsing

end

end OAI

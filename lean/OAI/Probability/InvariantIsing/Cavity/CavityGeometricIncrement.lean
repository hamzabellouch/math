import OAI.Probability.InvariantIsing.Cavity.CavityCoupledOverlap
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteIncrement

namespace OAI

/-! The finite perturbed increment inequality for the actual spectral
coupling. Its overlap estimate is proved by the retained projector geometry. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavity_geometric_energy_increment {N n m d depth : ℕ} (hN : 0 < N)
    (g : Fin (N + n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N + n) // g i = a} ≃ Fin (k a + n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    (ν : Measure ((Spin N × Spin n) × LabeledLeaf depth)) [IsProbabilityMeasure ν] :
    ∃ V : Orthogonal N,
      cavityPhysicalBase g lam B (Matrix.diagonal (fun j => lam (a₀ j)))
        (cavitySpecialOrthogonal U) =
        (V : Matrix (Fin N) (Fin N) ℝ) *
          Matrix.diagonal (fun j => Sum.elim (fun v => lam v.1) (fun j => lam (a₀ j)) (e.symm j)) *
          (V : Matrix (Fin N) (Fin N) ℝ).transpose ∧
      cavityPhysicalSpecial g B (cavitySpecialOrthogonal U) =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e ∧
      let eig₀ := fun j => Sum.elim (fun v => lam v.1) (fun j => lam (a₀ j)) (e.symm j)
      let J := cavityBaseGroup k e a₀
      let y := fun x : Spin N × Spin n => cavityFullSpecialCoordinates g
        (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U (cavityJoinedSpin x)
      let H := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
        rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) (matrixRotation V⁻¹) x.1.1
      let W := fun x : (Spin N × Spin n) × LabeledLeaf depth => t *
        (rotatedEnergy (fun i => lam (g i)) (specialRotation U) (cavityJoinedSpin x.1) -
          rotatedEnergy eig₀ (matrixRotation V⁻¹) x.1.1)
      let F := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
        rotatedEnergy (diagonalPerturbedEigenvalues (fun i => lam (g i))
          (cavitySpectralGroup g) v t) (specialRotation U) (cavityJoinedSpin x.1)
      let A := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
        cavityPerturbationCoefficients (specialRotation U) (cavitySpectralGroup g) u depth
          (cavityJoinedSpin x.1, x.2)
      let C := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
        cavityPerturbationCoefficients (matrixRotation V⁻¹) J u depth (x.1.1, x.2)
      let δ := cavityDeterministicRate n m (2 * (2 * n + 1)) N +
        2 * cavityCovarianceRate n (2 * n + 1) N
      (∫ z : ℕ → ℝ, Real.log (∫ x, Real.exp (W x - δ * (1 + ‖y x.1‖ ^ 2))
        ∂ν.tilted (fun x => H x + cylinderField (C x) z)) ∂gaussianCoordinates) ≤
        (∫ z : ℕ → ℝ, Real.log (∫ x, Real.exp (F x + cylinderField (A x) z) ∂ν)
          ∂gaussianCoordinates) -
        ∫ z : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) z) ∂ν)
          ∂gaussianCoordinates := by
  obtain ⟨V, hV, hVS, herror⟩ := cavity_coupled_spectral_overlap hN g k ek e es U lam a₀ B hB hBT hA
  refine ⟨V, hV, hVS, ?_⟩
  let w := fun x : Spin N × Spin n => 1 + ‖cavityFullSpecialCoordinates g
    (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U (cavityJoinedSpin x)‖ ^ 2
  have hw (x : Spin N × Spin n) : 1 ≤ w x := le_add_of_nonneg_right (sq_nonneg _)
  have hrestrict (x : Spin N × Spin n) :
      (fun i : Fin N => cavityJoinedSpin x (Fin.castAdd n i)) = x.1 := by
    funext i
    exact Fin.append_left x.1 x.2 i
  have herr (x z : Spin N × Spin n) (a : Fin m) :
      |projectedOverlap (specialRotation U) (cavitySpectralGroup g a)
        (cavityJoinedSpin x) (cavityJoinedSpin z) -
        projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a) x.1 z.1| ≤
        (2 * (n : ℝ) + 1) / N * (w x + w z) := by
    have h := herror a (cavityJoinedSpin x) (cavityJoinedSpin z)
    rw [hrestrict x, hrestrict z] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (Nat.cast_nonneg N))
    dsimp only [w]
    linarith
  exact cavity_finite_energy_increment hN (specialRotation U) (matrixRotation V⁻¹)
    (cavitySpectralGroup g) (cavityBaseGroup k e a₀) (fun i => lam (g i))
    (fun j => Sum.elim (fun v => lam v.1) (fun j => lam (a₀ j)) (e.symm j))
    v hv u hu t ν w hw (C := 2 * n + 1) (by positivity) herr

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Cavity.CavityGeometricIncrement
import OAI.Probability.InvariantIsing.Cavity.CavityDisorderTestComparison

namespace OAI

/-! The actual retained-projector coupling supplies the geometric error
needed for every bounded replica test on a fixed special-coordinate cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def cavityGeometricWeight {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (U : SpecialOrthogonal (N + n))
    (x : Spin N × Spin n) : ℝ :=
  1 + ‖cavityFullSpecialCoordinates g B U (cavityJoinedSpin x)‖ ^ 2

lemma cavityGeometricWeight_one_le {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (U : SpecialOrthogonal (N + n))
    (x : Spin N × Spin n) : 1 ≤ cavityGeometricWeight g B U x :=
  le_add_of_nonneg_right (sq_nonneg _)

theorem cavity_geometric_cutoff_test {N n m d depth r : ℕ} (hN : 0 < N)
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
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef) :
    ∃ V : Orthogonal N,
      cavityPhysicalBase g lam B (Matrix.diagonal (fun j => lam (a₀ j)))
        (cavitySpecialOrthogonal U) =
        (V : Matrix (Fin N) (Fin N) ℝ) *
          Matrix.diagonal (fun j => Sum.elim (fun v => lam v.1)
            (fun j => lam (a₀ j)) (e.symm j)) *
          (V : Matrix (Fin N) (Fin N) ℝ).transpose ∧
      cavityPhysicalSpecial g B (cavitySpecialOrthogonal U) =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e ∧
      ∀ (D : ℝ), 1 ≤ D →
        let w := cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
        let eig₀ := fun j => Sum.elim (fun v => lam v.1) (fun j => lam (a₀ j)) (e.symm j)
        ∀ (ν : Measure {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D})
          [IsProbabilityMeasure ν]
          (v : Fin m → ℝ), (∀ a, |v a| ≤ 2) →
          ∀ (u : ℕ → ℝ), (∀ j, |u j| ≤ 2) → ∀ (t : ℝ)
          (Φ : (Fin r → {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D}) → ℝ)
          (M s : ℝ), 0 ≤ M → (∀ σ, |Φ σ| ≤ M) → 0 < s →
          |cavityBaseCutoffReplicaMean (specialRotation U) (matrixRotation V⁻¹)
              (cavityBaseGroup k e a₀) (fun i => lam (g i)) eig₀ v u t w D ν Φ -
            cavityFullCutoffReplicaMean (specialRotation U) (cavitySpectralGroup g)
              (fun i => lam (g i)) v u t w D ν Φ| ≤
            (2 * (r : ℝ)^2 * (cavityCovarianceRate n (2 * n + 1) N * (2 * D)) +
              2 * r * (cavityCovarianceRate n (2 * n + 1) N * (2 * D)) +
              2 * r * (cavityDeterministicRate n m (2 * (2 * n + 1)) N * D)) / s +
                M^2 * s / 2 := by
  obtain ⟨V, hV, hVS, herror⟩ :=
    cavity_coupled_spectral_overlap hN g k ek e es U lam a₀ B hB hBT hA
  refine ⟨V, hV, hVS, ?_⟩
  intro D hD w eig₀ ν hν v hv u hu t Φ M s hM hΦ hs
  have hrestrict (x : Spin N × Spin n) :
      (fun i : Fin N => cavityJoinedSpin x (Fin.castAdd n i)) = x.1 := by
    funext i
    exact Fin.append_left x.1 x.2 i
  have herr (x z : Spin N × Spin n) (a : Fin m) :
      |projectedOverlap (specialRotation U) (cavitySpectralGroup g a)
        (cavityJoinedSpin x) (cavityJoinedSpin z) -
        projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a) x.1 z.1| ≤
        (2 * (n : ℝ) + 1) / N * (w x + w z) := by
    have hh := herror a (cavityJoinedSpin x) (cavityJoinedSpin z)
    rw [hrestrict x, hrestrict z] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (Nat.cast_nonneg N))
    dsimp only [w, cavityGeometricWeight]
    linarith
  exact cavity_finite_cutoff_test_comparison hN (specialRotation U) (matrixRotation V⁻¹)
    (cavitySpectralGroup g) (cavityBaseGroup k e a₀) (fun i => lam (g i)) eig₀ v hv u hu t
    w (cavityGeometricWeight_one_le g _ U) (by positivity) hD herr ν Φ hM hΦ hs

end InvariantIsing

end

end OAI

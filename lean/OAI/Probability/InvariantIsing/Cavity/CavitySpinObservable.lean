import OAI.Probability.InvariantIsing.Cavity.CavityFiniteGroupSelection

namespace OAI

/-! The continuous spectral-block observable used to read the physical
spin overlap from the finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma sum_cavityCanonicalCoordinate {m : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (∑ a, cavityCanonicalCoordinate rho lam hrho hsum p a t) = t := by
  simp only [cavityCanonicalCoordinate, Set.projIcc_of_mem zero_le_one ht]
  rw [← intervalIntegral.integral_finsetSum
    (fun a _ => spectralPathDensity_intervalIntegrable rho lam hrho hsum p a ht)]
  simp only [spectralPathDensity, sum_projectedResolventDerivative,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

def cavitySpinObservable {m k : ℕ} (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (j : Fin k) :
    SpectralBlock m 2 × (Fin 2 → Spin k) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun p => Φ (∑ a, (p.1 0 1 a : ℝ)) *
      (spinValue (p.2 0 j) * spinValue (p.2 1 j)),
      (hΦ.comp (continuous_finsetSum _ (fun a _ => by fun_prop))).mul
        (show Continuous (fun p : SpectralBlock m 2 × (Fin 2 → Spin k) =>
          spinValue (p.2 0 j) * spinValue (p.2 1 j)) from
          (continuous_of_discreteTopology : Continuous (fun ε : Fin 2 → Spin k =>
            spinValue (ε 0 j) * spinValue (ε 1 j))).comp continuous_snd)⟩

lemma cavitySpinObservable_finite {m k n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Icc 0 1)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (j : Fin k)
    (σ : Fin 2 → LabeledLeaf n) (ε : Fin 2 → Spin k) :
    cavitySpinObservable (m := m) Φ hΦ j
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ, ε) =
      Φ (q (cavityFiniteLevel n (labeledCommonDepth n (σ 0) (σ 1)))) *
        (spinValue (ε 0 j) * spinValue (ε 1 j)) := by
  change Φ (∑ a, (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ 0 1 a : ℝ)) * _ = _
  have hs : (∑ a, (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ 0 1 a : ℝ)) =
      q (cavityFiniteLevel n (labeledCommonDepth n (σ 0) (σ 1))) := by
    simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, Fin.zero_ne_one,
      ↓reduceIte, cavityCanonicalLabel]
    exact sum_cavityCanonicalCoordinate rho lam hrho hsum p (hq _)
  rw [hs]

end InvariantIsing

end

end OAI

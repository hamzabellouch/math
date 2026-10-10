import OAI.Probability.InvariantIsing.Cavity.CavityTreePressureIncrement
import OAI.Probability.InvariantIsing.Cavity.CavityRandomTreeLogLaw

namespace OAI

/-! The full physical pressure increment dominates the random-block
fresh-Haar logarithm on the exact probability space used for its limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_random_pressure_increment {N n m d depth : ℕ} (hN : 0<N)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i=a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))
    [IsProbabilityMeasure η] (l r : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val<r a)
    (hln : ∀ a, l a+n ≤ r a) (hr : ∀ a, r a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ] (lam v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
    let A := fun U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams g U)
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N+
      2*cavityCovarianceRate n (2*n+1) N
    let I₀ := cavityBaseGroup k e a₀
    let eig₀ := diagonalPerturbedEigenvalues
      (fun i => lam (Sum.elim (fun w => w.1) a₀ (e.symm i))) I₀ v t
    let I := cavitySpectralGroup g
    let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) I v t
    (∫ p, cavityRandomHaarLog k e a₀ hk lam v u t cap δ A p
      ∂(μ.prod ((ν.prod θ).prod gaussianCoordinates)).prod η) ≤
      (∫ z, cavityRotationLogMean z.2 eig I u z.1 ∂μ.prod θ) -
        ∫ z, cavityRotationLogMean z.2 eig₀ I₀ u z.1 ∂ν.prod θ := by
  intro A δ I₀ eig₀ I eig
  have h := cavity_tree_pressure_capped_increment hN g k ek e es B₀ a₀ l r hg hln hr
    μ ν θ lam v hv u hu t cap hcap
  have hmA : Measurable A :=
    (measurable_cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀).comp
      (measurable_cavityCompressionGrams g)
  have he := cavity_random_tree_log_law μ k e a₀ hk ν θ η lam v u hu t cap δ hcap
    A hmA (fun U => cavity_compression_factor_size_bound g es lam (fun j => lam (a₀ j)) B₀ U)
  exact he.symm.trans_le h

end InvariantIsing

end

end OAI

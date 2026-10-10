import OAI.Probability.InvariantIsing.Magnetic.RestrictedHaarCoefficients
import OAI.Probability.InvariantIsing.Magnetic.RestrictedHaarCutoffComparison
import OAI.Probability.InvariantIsing.Cavity.CavityTestLimit

namespace OAI

/-! At a fixed spatial cutoff the original spin test converges to the
independent base-Haar cavity test with deterministic limiting blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem restricted_haar_cutoff_limit {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (j : ℕ) → Finset (Spin (N j))) (hS : ∀ j, (S j).Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    {D M : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × Spin n) × LabeledLeaf (depth j)) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A₀ : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A₀}) atTop (𝓝 0)) :
    Tendsto (fun j =>
      (∫ U, restrictedOriginalGeometricMean (S j) (hS j) Cset hCset (g j) (cavityConcreteComplement es B₀) (T j)
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) D (F j) (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
      ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
        (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D A₀
        (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
        (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j)
      atTop (𝓝 0) := by
  let A : (j : ℕ) → Orthogonal (N j+n) → CavityFactorBlocks d n := fun j U =>
    cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
      (cavityCompressionGrams (g j) U)
  let R : ℕ → ℝ := fun j => ∫ U, ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
    (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D (A j U)
    (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
    (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j ∂μ j
  let O : ℕ → ℝ := fun j => ∫ U, restrictedOriginalGeometricMean (S j) (hS j) Cset hCset (g j)
    (cavityConcreteComplement es B₀) (T j)
    (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
    (u j) D (F j) (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j
  let L : ℕ → ℝ := fun j => ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
    (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D A₀
    (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
    (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j
  have hcov := (cavityCovarianceRate_tendsto n (2*n+1)).comp hNlim
  have hdet := (cavityDeterministicRate_tendsto n m (2*(2*n+1))).comp hNlim
  have hδ : Tendsto (fun j =>
      2*(2:ℝ)^2*(cavityCovarianceRate n (2*n+1) (N j)*(2*D)) +
      2*2*(cavityCovarianceRate n (2*n+1) (N j)*(2*D)) +
      2*2*(cavityDeterministicRate n m (2*(2*n+1)) (N j)*D)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero, Function.comp_apply] using
      (((hcov.mul_const (2*D)).const_mul (2*(2:ℝ)^2)).add
        ((hcov.mul_const (2*D)).const_mul (2*2))).add
        ((hdet.mul_const D).const_mul (2*2))
  have hRO : Tendsto (fun j => R j-O j) atTop (𝓝 0) := by
    apply cavity_secant_error_tendsto (C := M^2/2) (by positivity) hδ
    intro s hs
    apply Eventually.of_forall
    intro j
    have hh := restricted_haar_cutoff_comparison (hN j) (S j) (hS j) Cset hCset (g j) (k j) (ek j) (e j) es
      B₀ a₀ (l j) (w j) (hg j) (hln j) (hw j) (μ j) (ν j) (T j) lam (v j) (hv j)
      (u j) (hu j) t hD hM hs (F j) (hF j)
    change |R j-O j| ≤ _ at hh
    convert hh using 1
    ring
  have hA j : Measurable (A j) :=
    (measurable_cavityCompressionFactorBlocks es lam _ B₀).comp
      (measurable_cavityCompressionGrams (g j))
  have hRL : Tendsto (fun j => R j-L j) atTop (𝓝 0) := by
    have hh := restricted_haar_normalized_coefficient_tendsto N depth S hS Cset hCset k e a₀ μ ν T lam v
      u hu t (show 0 ≤ D by linarith) A hA A₀
      (fun j σ => F j (fun i => cavityPairLeafUnswap (σ i))) hM (fun j σ => hF j _)
      hprob
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  have hh := hRL.sub hRO
  convert hh using 1
  · funext j
    dsimp only [R, O, L]
    ring
  · norm_num

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalCutoffComparison
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalCavityHaar
import OAI.Probability.InvariantIsing.Cavity.CavityOrientedProjectors
import OAI.Probability.InvariantIsing.Cavity.CavityGeometricMean

namespace OAI

/-! The original Ising cutoff, averaged over its actual Haar disorder,
is compared with an independent Haar base cavity law. All random block
coefficients remain inside the normalized test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_haar_cutoff_comparison {N n m d depth : ℕ} (hN : 0 < N)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l w : Fin m → ℕ) (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < w a)
    (hln : ∀ a, l a+n ≤ w a) (hw : ∀ a, w a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    {D M s : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) (hs : 0 < s)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    let B := cavityConcreteComplement es B₀
    let A := cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
    |(∫ U, ∫ V, cavityProjectorCavityMean T
        (fun a => t*lam a+2*perturbationScale N*v a) u t D
        (A (cavityCompressionGrams g U))
        (fun σ => F (fun i => cavityPairLeafUnswap (σ i)))
        (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν ∂μ) -
      (∫ U, cavityOriginalGeometricMean g B T
        (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
        u D F (cavityOrientationLift (Nat.add_pos_left hN n) U) ∂μ)| ≤
      (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityDeterministicRate n m (2*(2*n+1)) N * D)) / s + M^2*s/2 := by
  intro B A
  let c := fun a => t*lam a+2*perturbationScale N*v a
  let f := fun U : Orthogonal (N+n) => cavityProjectorCavityMean T c u t D
    (A (cavityCompressionGrams g U))
    (fun σ => F (fun i => cavityPairLeafUnswap (σ i)))
    (cavityPhysicalLabeledProjectors g B a₀ U)
  let h := fun U : Orthogonal (N+n) => cavityOriginalGeometricMean g B T
    (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
    u D F (cavityOrientationLift (Nat.add_pos_left hN n) U)
  have hBm : Measurable B := measurable_cavityConcreteComplement es B₀
  have hAm : Measurable A := measurable_cavityCompressionFactorBlocks es lam _ B₀
  have hFs : Measurable (fun σ : Fin 2 → (Spin N × LabeledLeaf depth) × Spin n =>
      F (fun i => cavityPairLeafUnswap (σ i))) := measurable_of_countable _
  have hfm : Measurable f := measurable_cavityProjectorCavityMean
    (N := N) (n := n) (m := m) (d := d) (depth := depth) T c u t D
    (fun U => A (cavityCompressionGrams g U))
    (hAm.comp (measurable_cavityCompressionGrams g))
    (cavityPhysicalLabeledProjectors g B a₀)
    (measurable_cavityPhysicalLabeledProjectors g B hBm a₀)
    (fun _ σ => F (fun i => cavityPairLeafUnswap (σ i)))
    (hFs.comp measurable_snd)
  have hhm : Measurable h := (measurable_cavityOriginalGeometricMean g B hBm T _ u D F).comp
    (measurable_cavityOrientationLift (Nat.add_pos_left hN n))
  have hfb U : ‖f U‖ ≤ M := cavityProjectorCavityMean_bound T c u t D _ _ hM
    (fun σ => hF _) _
  have hhb U : ‖h U‖ ≤ M := cavityOriginalGeometricMean_bound g B T _ u D F hM hF _
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable M (ae_of_all _ hfb)
  have hhi : Integrable h μ := Integrable.of_bound hhm.aestronglyMeasurable M (ae_of_all _ hhb)
  have hcmp : ∀ᵐ U ∂μ, |f U-h U| ≤
      (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityDeterministicRate n m (2*(2*n+1)) N * D)) / s + M^2*s/2 := by
    filter_upwards [cavityCompressionGrams_posDef_ae g l w hg hln hw μ] with U hU
    let R := cavityOrientationLift (Nat.add_pos_left hN n) U
    have hpos : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal R) a).PosDef := by
      simpa only [R, cavityOrientationLift_compression] using hU
    have hh := cavity_physical_cutoff_comparison hN g k ek e es R lam a₀ B
      (cavityConcreteComplement_gram g es B₀ (cavitySpecialOrthogonal R))
      (cavityConcreteComplement_perp g es B₀ (cavitySpecialOrthogonal R)) hpos
      T v hv u hu t hD hM hs F hF
    dsimp only at hh
    simpa only [f, h, c, A, B, cavityCompressionFactorBlocks, R,
      cavityOrientationLift_compression, cavityOrientationLift_projectors,
      cavityOriginalGeometricMean] using hh
  have havg := cavity_physical_cavity_haar g k ek e es B₀ a₀ l w hg hln hw μ ν
    T c u t D A hAm
    (fun _ σ => F (fun i => cavityPairLeafUnswap (σ i)))
    (hFs.comp measurable_snd) hM (fun _ σ => hF _)
  change (∫ U, f U ∂μ) = _ at havg
  rw [← havg, ← integral_sub hfi hhi]
  have hb := norm_integral_le_of_norm_le_const (f := fun U => f U-h U)
    (C := (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
      2*2*(cavityCovarianceRate n (2*n+1) N*(2*D)) +
      2*2*(cavityDeterministicRate n m (2*(2*n+1)) N*D))/s+M^2*s/2)
    (hcmp.mono fun U hU => by simpa only [Real.norm_eq_abs] using hU)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

end InvariantIsing

end

end OAI

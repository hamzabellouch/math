import OAI.Geometry.SurfaceImmersion.Correction.ChartedPolynomialMean

namespace OAI

/-! The polynomial mean constant is chosen before the immersion and scales.
Only the fixed polynomial, compact low-jet range and indicated finite bounds
enter the choice. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes

theorem uniform_charted_polynomial_mean {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (C D J : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (hJ : ∀ m, 1 ≤ J m)
    (k : Fin 3) (q m : ℕ) (B F A N : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F)
    (hA : 0 ≤ A) (hN : 0 ≤ N) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G)
      (φ : Base → ℝ) (K : Compacts Base) (ε τ : ℝ) (s : ℝ≥0)
      (c : PolynomialSolveData P ε G hG φ K τ s),
      c.U = U → c.C = C → c.D = D → c.J = J →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order (P k)) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order (P k)) F
        (fun x => fderiv ℝ φ x (coordinateVector v))) →
      WeightedBound c.e.target s
        (m + order (P k) + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap) →
      ∀ δ : ℝ, 0 < δ → ∀ (b d : SupportedField (F := ℝ) c.chartCompact) (z : ℝ),
      0 ≤ z →
      supportedWeightedSeminorm c.chartCompact s
        (m + order (P k) + (q + 1) * (tensorOrder P + 1)) b ≤ A →
      supportedWeightedSeminorm c.chartCompact s
        (m + order (P k) + (q + 1) * (tensorOrder P + 1)) d ≤ A →
      supportedWeightedSeminorm c.chartCompact s
        (m + order (P k) + (q + 1) * (tensorOrder P + 1)) (b - d) ≤ A * z →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * E)
        (normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q b) τ 0) ∧
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * (2 * E) * z)
        (fun x => normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q b) τ 0 x -
          normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q d) τ 0 x) := by
  obtain ⟨E₀,hE₀,he⟩ := normalizedPolynomialMean_bounds hU hO hQ hQO
    (P k) (hP k) m B F hB hF
  let r := m + order (P k)
  let S := (r.factorial : ℝ) * J r ^ r * correctedSeedBudget (tensorOrder P) C D q r N
  have hS : 0 ≤ S := mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (zero_le_one.trans (hJ r)) _))
    (correctedSeedBudget_nonneg (tensorOrder P) C D hC q r hN)
  refine ⟨E₀ * (S * A) ^ 2, mul_nonneg hE₀ (sq_nonneg _), ?_⟩
  intro G hG φ K ε τ s c hUeq hCeq hDeq hJeq hτ hs hτs hs1 hε hε1 hsmall hGQ hGb hφb hn
    δ hδ b d z hz hb hd hbd
  have hzb : supportedWeightedSeminorm K s r (c.originalFreeSeed δ q b) ≤ S * A * (δ * τ) := by
    simpa only [S, hCeq, hDeq, hJeq] using
      c.originalFreeSeed_bound hδ.le hτ hs hτs hs1 hε hsmall q r hA hN hn b hb
  have hzd : supportedWeightedSeminorm K s r (c.originalFreeSeed δ q d) ≤ S * A * (δ * τ) := by
    simpa only [S, hCeq, hDeq, hJeq] using
      c.originalFreeSeed_bound hδ.le hτ hs hτs hs1 hε hsmall q r hA hN hn d hd
  have hdiff : supportedWeightedSeminorm K s r
      (c.originalFreeSeed δ q b - c.originalFreeSeed δ q d) ≤ S * (A * z) * (δ * τ) := by
    simpa only [S, hCeq, hDeq, hJeq, c.originalFreeSeed_sub] using
      c.originalFreeSeed_bound hδ.le hτ hs hτs hs1 hε hsmall q r
        (mul_nonneg hA hz) hN hn (b - d) hbd
  have hp : loss (P k) ≤ tensorLoss P :=
    Finset.le_sup (f := fun i => loss (P i)) (Finset.mem_univ k)
  have hh := he G φ hG c.smoothPhase K (c.originalFreeSeed δ q b) (c.originalFreeSeed δ q d)
    s δ τ ε (S * A) (S * (A * z)) (tensorLoss P) hδ hτ hs hτs hs1 hε hε1
    (mul_nonneg hS hA) (mul_nonneg hS (mul_nonneg hA hz)) hp hGQ hGb hφb hzb hzd hdiff 0 (by simp)
  rw [← hUeq] at hh
  constructor
  · convert normalizedPolynomialMean_extend c.openU c.smoothPhase K c.supportU
      (c.originalFreeSeed δ q b) δ ε τ 0 (by positivity) hh.1 using 1
    ring
  · convert normalizedPolynomialMean_difference_extend c.openU c.smoothPhase K c.supportU
      (c.originalFreeSeed δ q b) (c.originalFreeSeed δ q d) δ ε τ 0 (by positivity) hh.2 using 1
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI

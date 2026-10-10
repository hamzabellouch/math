import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeSeed
import OAI.Geometry.SurfaceImmersion.Correction.NormalizedPolynomialSupport

namespace OAI

/-! Polynomial mean estimates for the actual free amplitude transported
from a phase chart. The polynomial is evaluated in the original coordinates;
no transformed polynomial expression is assumed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open WeightedEstimates RealModes
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

theorem polynomial_mean_bounds {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ c.O)
    (k : Fin 3) (q m : ℕ) (B F A N : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F)
    (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (hGQ : Set.MapsTo (lowJet G) c.U Q)
    (hGb : WeightedBound c.U s (m + order (P k)) B (lowJet G))
    (hφb : ∀ v, WeightedBound c.U s (m + order (P k)) F
      (fun x => fderiv ℝ φ x (coordinateVector v)))
    (hn : WeightedBound c.e.target s
      (m + order (P k) + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap)) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ δ : ℝ, 0 < δ →
      ∀ (b d : SupportedField (F := ℝ) c.chartCompact) (z : ℝ), 0 ≤ z →
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
  obtain ⟨E₀,hE₀,he⟩ := normalizedPolynomialMean_bounds c.openU c.openO hQ hQO
    (P k) (c.smoothP k) m B F hB hF
  let r := m + order (P k)
  let S := (r.factorial : ℝ) * c.J r ^ r * correctedSeedBudget (tensorOrder P) c.C c.D q r N
  have hS : 0 ≤ S := mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (zero_le_one.trans (c.oneLEJ r)) _))
    (correctedSeedBudget_nonneg (tensorOrder P) c.C c.D c.nonnegC q r hN)
  refine ⟨E₀ * (S * A) ^ 2, mul_nonneg hE₀ (sq_nonneg _), ?_⟩
  intro δ hδ b d z hz hb hd hbd
  have hzb := c.originalFreeSeed_bound hδ.le hτ hs hτs hs1 hε hsmall q r hA hN hn b hb
  have hzd := c.originalFreeSeed_bound hδ.le hτ hs hτs hs1 hε hsmall q r hA hN hn d hd
  have hdiff := c.originalFreeSeed_bound hδ.le hτ hs hτs hs1 hε hsmall q r
    (mul_nonneg hA hz) hN hn (b - d) hbd
  rw [c.originalFreeSeed_sub] at hdiff
  have hp : loss (P k) ≤ tensorLoss P :=
    Finset.le_sup (f := fun i => loss (P i)) (Finset.mem_univ k)
  have hh := he G φ hG c.smoothPhase K (c.originalFreeSeed δ q b) (c.originalFreeSeed δ q d)
    s δ τ ε (S * A) (S * (A * z)) (tensorLoss P) hδ hτ hs hτs hs1 hε hε1
    (mul_nonneg hS hA) (mul_nonneg hS (mul_nonneg hA hz)) hp hGQ hGb hφb hzb hzd hdiff 0 (by simp)
  have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  constructor
  · convert normalizedPolynomialMean_extend c.openU c.smoothPhase K c.supportU
      (c.originalFreeSeed δ q b) δ ε τ 0 (by positivity) hh.1 using 1
    ring
  · have hdif := normalizedPolynomialMean_difference_extend c.openU c.smoothPhase K c.supportU
      (c.originalFreeSeed δ q b) (c.originalFreeSeed δ q d) δ ε τ 0 (by positivity) hh.2
    convert hdif using 1
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI

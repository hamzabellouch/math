import OAI.Probability.InvariantIsing.Cavity.CavityHaarCoefficientProbability
import OAI.Probability.InvariantIsing.Cavity.CavityCompressionLimitGeometry
import OAI.Probability.InvariantIsing.Cavity.CavitySchurFiniteR

namespace OAI

/-! The actual contiguous spectral groups give the precise deterministic
factor blocks required by the original-model spin and entropy limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix BigOperators

namespace InvariantIsing

theorem cavity_actual_factor_probability {m n d : ℕ}
    (es : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (N : ℕ → ℕ) (l w : Fin m → ℕ → ℕ)
    (g : (k : ℕ) → Fin (N k+n) → Fin m)
    (hg : ∀ a k i, g k i = a ↔ l a k ≤ i.val ∧ i.val < w a k)
    (hN : Tendsto (fun k => N k+n) atTop atTop)
    (hw : ∀ a, Tendsto (w a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlw : ∀ a k, l a k ≤ w a k)
    (hle : ∀ a k, l a k ≤ N k+n) (hwe : ∀ a k, w a k ≤ N k+n)
    (ρl ρw : Fin m → ℝ) (hρ : ∀ a, 0 < ρw a-ρl a)
    (hsum : ∑ a, (ρw a-ρl a) = 1)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ)/(N k+n)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun k => (w a k : ℝ)/(N k+n)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => (ρw a-ρl a) • 1)).transpose * B₀ = 0)
    (μ : (k : ℕ) → Measure (Orthogonal (N k+n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant] :
    let ρ := fun a => ρw a-ρl a
    let B := cavityCompressionLimitFrame es B₀
    let A : CavityFactorBlocks d n :=
      (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun i => lam (a₀ i)),
       B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
       (finiteR ρ lam hρ hsum 0) • 1)
    ∀ δ > 0, Tendsto (fun k => (μ k).real {U | δ < cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
        (cavityCompressionGrams (g k) U)) A}) atTop (𝓝 0) := by
  intro ρ B A δ hδ
  have hh := cavityHaarFactorCoefficients_probability es lam (fun i => lam (a₀ i)) B₀ hB₀
    (fun k => N k+n) l w hN hw hl hlw hle hwe ρl ρw (fun a => (hρ a).le)
    (fun a => by simpa only [Nat.cast_add] using hρl a)
    (fun a => by simpa only [Nat.cast_add] using hρw a) hperp μ (fun k => cavityColumns (1 : Orthogonal (N k+n)))
    (fun _ => cavityColumns_gram _) hδ
  have hA : cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun i => lam (a₀ i))) (fun i j => B₀ (es i) j)
      (cavitySpectralStack (fun a => (ρw a-ρl a) • (1 : Matrix (Fin n) (Fin n) ℝ))) = A := by
    change cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun i => lam (a₀ i))) B
      (cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ))) = A
    rw [cavitySpectralStack_scalar_eq ρ (fun a => (hρ a).le)]
    change (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun i => lam (a₀ i)),
      B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
      (cavityLimitingStack (n := n) ρ).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityLimitingStack (n := n) ρ) = A
    rw [cavity_limiting_cavityBlock_eq_finiteR_zero ρ lam hρ hsum]
  rw [hA] at hh
  have hgram (k : ℕ) (U : Orthogonal (N k+n)) :
      (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k+n)) (Fin (N k+n)) ℝ)*cavityColumns (1 : Orthogonal (N k+n)))
        (l a k) (w a k)) = cavityCompressionGrams (g k) U := by
    funext a
    rw [cavityCompressionGrams_eq_window (g k) a (l a k) (w a k) (hlw a k) (hg a k) U,
      cavityColumns_eq_mul U]
  apply hh.congr
  intro k
  apply congrArg ((μ k).real)
  ext U
  change (δ < cavityFactorDeviation
    (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
      (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k+n)) (Fin (N k+n)) ℝ)*cavityColumns (1 : Orthogonal (N k+n)))
        (l a k) (w a k))) A) ↔ _
  rw [hgram k U]
  rfl

end InvariantIsing

end

end OAI

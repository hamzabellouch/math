import OAI.Probability.InvariantIsing.Cavity.CavityBaseHaarFactorization
import OAI.Probability.InvariantIsing.Cavity.CavityConcreteComplement

namespace OAI

/-! The actual measurable finite cavity construction has a Haar base
spectral orbit independent of its compression matrices. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

theorem cavityConcreteBase_haar_factorization {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N + n) // g i = a} ≃ Fin (k a + n))
    (e : ((a : Fin m) × Fin (k a)) ⊕ Fin d ≃ Fin N)
    (e₀ : Fin (m * n) ≃ Fin (d + n))
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (l u : Fin m → ℕ)
    (hg : ∀ a i, g i = a ↔ l a ≤ i.val ∧ i.val < u a)
    (hln : ∀ a, l a + n ≤ u a) (hu : ∀ a, u a ≤ N + n)
    (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (μ : Measure (Orthogonal (N + n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (f : Matrix (Fin N) (Fin N) ℝ → ℝ)
    (q : (Fin m → Matrix (Fin n) (Fin n) ℝ) → ℝ)
    (hf : Measurable f) (hq : Measurable q)
    (Cf Cq : ℝ) (hCq : 0 ≤ Cq)
    (hfb : ∀ J, ‖f J‖ ≤ Cf) (hqb : ∀ M, ‖q M‖ ≤ Cq) :
    (∫ U, q (cavityCompressionGrams g U) *
      f (cavityPhysicalBase g lam (cavityConcreteComplement e₀ B₀) (Matrix.diagonal lam₀) U) ∂μ) =
      (∫ U, q (cavityCompressionGrams g U) ∂μ) *
        ∫ V, f (cavityConjugate V (Matrix.diagonal
          (fun j => Sum.elim (fun a => lam a.1) lam₀ (e.symm j)))) ∂ν := by
  apply cavityBase_compression_factorization g k ek e lam lam₀
    (cavityConcreteComplement e₀ B₀) (measurable_cavityConcreteComplement e₀ B₀)
    μ ν (cavityCompressionGrams_posDef_ae g l u hg hln hu μ)
  · intro U _
    exact cavityConcreteComplement_gram g e₀ B₀ U
  · intro U _
    exact cavityConcreteComplement_perp g e₀ B₀ U
  · exact hf
  · exact hq
  · exact hCq
  · exact hfb
  · exact hqb

end InvariantIsing

end

end OAI

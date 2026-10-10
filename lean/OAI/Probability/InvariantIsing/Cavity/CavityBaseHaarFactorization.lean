import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalBase

namespace OAI

/-! Exact independence, in bounded-test form, of the Haar base spectral
orbit and the small compression data in the concrete cavity coupling. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

def cavityConjugate {N : ℕ} (V : Orthogonal N) (J : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (V : Matrix (Fin N) (Fin N) ℝ) * J * (V : Matrix (Fin N) (Fin N) ℝ).transpose

lemma continuous_cavityConjugate (N : ℕ) :
    Continuous (Function.uncurry (cavityConjugate (N := N))) :=
  ((continuous_subtype_val.comp continuous_fst).matrix_mul continuous_snd).matrix_mul
    (continuous_subtype_val.comp continuous_fst).matrix_transpose

lemma cavityConjugate_mul {N : ℕ} (U V : Orthogonal N)
    (J : Matrix (Fin N) (Fin N) ℝ) :
    cavityConjugate (U * V) J = cavityConjugate U (cavityConjugate V J) := by
  change ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) * J *
    ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)).transpose = _
  simp only [cavityConjugate, Matrix.transpose_mul, Matrix.mul_assoc]

lemma cavityPhysicalBase_reservoir_inv {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (U : Orthogonal (N + n)) (V : Orthogonal N) :
    cavityPhysicalBase g lam B A₀ (U * cavityReservoirRotation (n := n) V⁻¹) =
      cavityConjugate V (cavityPhysicalBase g lam B A₀ U) := by
  rw [cavityPhysicalBase_reservoir]
  have hV : (V⁻¹ : Orthogonal N).val = (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
    ext i j
    rfl
  simp only [hV, Matrix.transpose_transpose, cavityConjugate]

theorem cavityBase_compression_factorization {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N + n) // g i = a} ≃ Fin (k a + n))
    (e : ((a : Fin m) × Fin (k a)) ⊕ Fin d ≃ Fin N)
    (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hBm : Measurable B)
    (μ : Measure (Orthogonal (N + n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (hA : ∀ᵐ U ∂μ, ∀ a, (cavityCompressionGrams g U a).PosDef)
    (hB : ∀ U, (∀ a, (cavityCompressionGrams g U a).PosDef) →
      (B (cavityCompressionGrams g U)).transpose * B (cavityCompressionGrams g U) = 1)
    (hBT : ∀ U, (∀ a, (cavityCompressionGrams g U a).PosDef) →
      (B (cavityCompressionGrams g U)).transpose *
        cavitySpectralStack (cavityCompressionGrams g U) = 0)
    (f : Matrix (Fin N) (Fin N) ℝ → ℝ)
    (q : (Fin m → Matrix (Fin n) (Fin n) ℝ) → ℝ)
    (hf : Measurable f) (hq : Measurable q)
    (Cf Cq : ℝ) (hCq : 0 ≤ Cq)
    (hfb : ∀ J, ‖f J‖ ≤ Cf) (hqb : ∀ M, ‖q M‖ ≤ Cq) :
    (∫ U, q (cavityCompressionGrams g U) *
      f (cavityPhysicalBase g lam B (Matrix.diagonal lam₀) U) ∂μ) =
      (∫ U, q (cavityCompressionGrams g U) ∂μ) *
        ∫ V, f (cavityConjugate V (Matrix.diagonal
          (fun j => Sum.elim (fun a => lam a.1) lam₀ (e.symm j)))) ∂ν := by
  let : OpensMeasurableSpace (Orthogonal N × Matrix (Fin N) (Fin N) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace (Orthogonal N × (Fin N → Fin N → ℝ)))
  apply cavity_orbit_factorization_right_ae μ ν
    (fun V => cavityReservoirRotation (n := n) V⁻¹)
    (cavityPhysicalBase g lam B (Matrix.diagonal lam₀)) (cavityCompressionGrams g)
    (measurable_cavityPhysicalBase g lam B hBm _) (measurable_cavityCompressionGrams g)
    cavityConjugate (continuous_cavityConjugate N).measurable cavityConjugate_mul
    _ _ _ _ f q hf hq Cf Cq hCq hfb hqb
  · intro V
    exact ae_of_all _ (fun U => cavityPhysicalBase_reservoir_inv g lam B _ U V)
  · intro V
    exact ae_of_all _ (fun U => cavityCompressionGrams_reservoir g U V⁻¹)
  · filter_upwards [hA] with U hU
    exact cavityPhysicalBase_mem_orbit g k ek e U lam lam₀ B (hB U hU) (hBT U hU) hU

end InvariantIsing

end

end OAI

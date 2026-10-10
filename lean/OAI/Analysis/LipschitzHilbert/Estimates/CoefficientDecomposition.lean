import OAI.Analysis.LipschitzHilbert.Phase.AngularErrorConvolution

namespace OAI

/-! The actual coefficient decomposes exactly into its frozen main part
and the angular error whose positive majorant was proved above. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

theorem analyzingCoefficient_sub {Ω σ κ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (area : σ → ℝ) (f h : σ → κ → Ω → ℂ)
    (g : Ω → EuclideanSpace ℂ κ)
    (hf : ∀ i k, Integrable (fun z => g z k * conj (f i k z)) μ)
    (hh : ∀ i k, Integrable (fun z => g z k * conj (h i k z)) μ) (i : σ) :
    analyzingCoefficient μ area (fun i k z => f i k z-h i k z) g i =
      analyzingCoefficient μ area f g i - analyzingCoefficient μ area h g i := by
  ext k
  change ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (f i k z-h i k z) ∂μ) =
    ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (f i k z) ∂μ) -
      ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (h i k z) ∂μ)
  simp only [map_sub, mul_sub]
  rw [integral_sub (hf i k) (hh i k)]
  ring

theorem angularErrorWave_eq_sub {ι κ : Type*} (b : ι → κ → ℝ → ℂ)
    (ψ : ι → κ → ℝ × ℝ → ℂ) (u : ℝ × ℝ → ℝ) (t d : ℝ)
    (i : ι) (k : κ) (z : ℝ × ℝ) :
    angularErrorWave b ψ u t d i k z =
      b i k (u z) * ψ i k z - (if |u z-t| ≤ d then b i k t * ψ i k z else 0) := by
  unfold angularErrorWave multiplierError
  split_ifs <;> ring

theorem angularCoefficient_decomposition {ι κ : Type*}
    (area : ι → ℝ) (b : ι → κ → ℝ → ℂ) (ψ : ι → κ → ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℝ) (t d : ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (hOriginal : ∀ i k, Integrable (fun z => g z k * conj (b i k (u z) * ψ i k z)))
    (hMain : ∀ i k, Integrable (fun z => g z k *
      conj (if |u z-t| ≤ d then b i k t * ψ i k z else 0))) (i : ι) :
    analyzingCoefficient volume area (fun i k z => b i k (u z)*ψ i k z) g i =
      analyzingCoefficient volume area (fun i k z =>
        if |u z-t| ≤ d then b i k t*ψ i k z else 0) g i +
      analyzingCoefficient volume area (angularErrorWave b ψ u t d) g i := by
  have heq : angularErrorWave b ψ u t d = (fun i k z =>
      b i k (u z)*ψ i k z - (if |u z-t| ≤ d then b i k t*ψ i k z else 0)) := by
    funext i k z
    exact angularErrorWave_eq_sub b ψ u t d i k z
  rw [heq, analyzingCoefficient_sub volume area _ _ g hOriginal hMain]
  abel

end LipschitzHilbert

end

end OAI

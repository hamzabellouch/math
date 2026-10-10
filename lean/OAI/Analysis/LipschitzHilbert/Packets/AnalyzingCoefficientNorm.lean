import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingCoefficients
import OAI.Analysis.LipschitzHilbert.Packets.PacketVectorDerivative

namespace OAI

/-! A dimension-independent bound on one analyzing coefficient, obtained
from the common scalar envelope of its diagonal multiplier. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

theorem analyzingCoefficient_norm_le {Ω σ κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (area : σ → ℝ) (wave : σ → κ → Ω → ℂ)
    (g : Ω → EuclideanSpace ℂ κ) (i : σ) (W : Ω → ℝ)
    (ha : 0 < area i) (hW : Integrable W μ) (hW0 : ∀ z, 0 ≤ W z)
    (hint : ∀ k, Integrable (fun z => g z k * conj (wave i k z)) μ)
    (hg : ∀ z, ‖g z‖ ≤ 1) (hw : ∀ k z, ‖wave i k z‖ ≤ W z) :
    ‖analyzingCoefficient μ area wave g i‖ ≤ (area i)⁻¹ * ∫ z, W z ∂μ := by
  let F : Ω → EuclideanSpace ℂ κ := fun z =>
    WithLp.toLp 2 (fun k => g z k * conj (wave i k z))
  have hF : Integrable F μ := integrable_piLp_iff.mpr hint
  have hbound (z : Ω) : ‖F z‖ ≤ W z := by
    have h := diagonal_packet_norm (g z) (fun k => conj (wave i k z)) (hW0 z)
      (fun k => by simpa only [RCLike.norm_conj] using hw k z)
    exact h.trans ((mul_le_mul_of_nonneg_left (hg z) (hW0 z)).trans_eq (mul_one _))
  have heq : analyzingCoefficient μ area wave g i = (area i)⁻¹ • ∫ z, F z ∂μ := by
    ext k
    change ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (wave i k z) ∂μ) =
      (area i)⁻¹ • (∫ z, F z ∂μ) k
    rw [eval_integral_piLp hint, Complex.real_smul, Complex.ofReal_inv]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
  exact (norm_integral_le_integral_norm F).trans (integral_mono hF.norm hW hbound)

end LipschitzHilbert

end

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.SelectedCoefficientDerivative
import OAI.Analysis.LipschitzHilbert.Estimates.TopPolynomialDecay
import OAI.Analysis.LipschitzHilbert.Packets.TopRawPacketData

namespace OAI

/-! The unconditional horizontal derivative estimate for actual selected
top sums. The lower length cutoff gives the reciprocal scale factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def selectedTopSum (P : PlanarPacketFamily N κ ι) (s : Finset (Fin N))
    (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (x y : ℝ) : EuclideanSpace ℂ κ :=
  ∑ j ∈ s, vectorPacketSynthesis (P.mainCoefficient cutoff v g j)
    (fun u k => P.wave j u k y) x

def topDerivativeConstant (P : PlanarPacketFamily N κ ι) (D : ℕ) : ℝ :=
  (P.constant*Real.pi^2)*(4*((16^(8*D+1)*(16^(8*D+1)*P.constant))*(4*Real.pi)^2))

theorem selectedTopSum_horizontal_bound (P : PlanarPacketFamily N κ ι)
    {lo hi K : ℝ} {D : ℕ} (T : SlopeBox) (hK : 0 < K)
    (data : TopRawPacketData P lo hi T K D)
    (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (s : Finset (Fin N)) (r : ℝ) (hr : 0 < r) (hs : ∀ j ∈ s, r ≤ P.length j)
    (z : ℝ × ℝ) :
    ‖deriv (fun x => P.selectedTopSum s cutoff v g x (z.2-T.slope*z.1)) z.1‖ ≤
      (P.topDerivativeConstant D/r)*(T.weight K (D:ℝ) z)^8 := by
  let y := z.2-T.slope*z.1
  let w := polynomialWeight T.x (K*T.length) (8*D+1) z.1 *
    polynomialWeight (T.y-T.slope*T.x) (K*T.width) (8*D+1) y
  have hw : 0 < w := mul_pos
    (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
    (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
  have hderiv (j : Fin N) (u : ι j) (k : κ) :
      ‖deriv (P.wave j u k y) z.1‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) z.1 *
          lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y) := by
    simpa only [data.wave_eq] using data.derivative_bound 0 y j u k z.1
  have hb := top_weighted_selected_derivative_bounded
    (P.mainCoefficient cutoff v g) (fun j u k => P.wave j u k y) P.site P.site_injective
    P.baseX P.baseZ P.topLength P.width T.x (T.y-T.slope*T.x)
    (K*T.length) (K*T.width) z.1 y P.constant (P.constant*Real.pi^2) r (8*D+1)
    P.topLength_pos P.width_pos (mul_pos hK T.length_pos) (mul_pos hK T.width_pos)
    data.length_le data.width_le P.constant_pos.le (mul_pos P.constant_pos (sq_pos_of_pos Real.pi_pos)) hr
    (P.mainCoefficient_norm cutoff v hv g hg hg1) data.centerX_le data.centerZ_le s hs hderiv
  change w*‖deriv (fun x => P.selectedTopSum s cutoff v g x y) z.1‖ ≤ _ at hb
  have hbudget : w*‖deriv (fun x => P.selectedTopSum s cutoff v g x y) z.1‖ ≤
      P.topDerivativeConstant D/r := by
    convert hb using 1
    unfold topDerivativeConstant
    ring
  have hinv : w⁻¹ ≤ (T.weight K (D:ℝ) z)^8 := T.inverse_polynomial_le_weight K hK D z
  calc
    _ = w⁻¹*(w*‖deriv (fun x => P.selectedTopSum s cutoff v g x y) z.1‖) := by
      rw [← mul_assoc,inv_mul_cancel₀ hw.ne',one_mul]
    _ ≤ w⁻¹*(P.topDerivativeConstant D/r) :=
      mul_le_mul_of_nonneg_left hbudget (inv_nonneg.mpr hw.le)
    _ ≤ (T.weight K (D:ℝ) z)^8*(P.topDerivativeConstant D/r) :=
      mul_le_mul_of_nonneg_right hinv (by have := P.constant_pos; unfold topDerivativeConstant; positivity)
    _ = _ := mul_comm _ _

end LipschitzHilbert.PlanarPacketFamily

end

end OAI

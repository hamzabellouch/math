import OAI.Analysis.LipschitzHilbert.Packets.VerticalFrameBound

namespace OAI

/-! The L2 operator bound for an actual vertical Schwartz multiplier
uses its Fourier-symbol supremum, without an L1 kernel loss. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem verticalL2Projection_symbol_bound (p : SchwartzMap ℝ ℂ) (w C : ℝ)
    (hw : 0<w) (hC : 0≤C) (hp : ∀ eta, ‖p eta‖≤C) (f : Lp ℂ 2 planeMeasure) :
    ‖verticalL2Projection p w f‖≤C*‖f‖ := by
  have hs := verticalFrame_L2 ({()} : Finset Unit) (fun _ : Unit => p)
    (fun _ => w) (fun _ => hw) (C^2) (fun eta => by
      simpa only [Finset.sum_singleton] using pow_le_pow_left₀ (norm_nonneg _) (hp (w*eta)) 2) f
  simp only [Finset.sum_singleton] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).1 (by
    simpa only [mul_pow] using hs)

theorem verticalL2Projection_symbol_norm (p : SchwartzMap ℝ ℂ) (w C : ℝ)
    (hw : 0<w) (hC : 0≤C) (hp : ∀ eta, ‖p eta‖≤C) :
    ‖verticalL2Projection p w‖≤C :=
  (verticalL2Projection p w).opNorm_le_bound hC
    (verticalL2Projection_symbol_bound p w C hw hC hp)

end LipschitzHilbert.PacketRepresentation

end

end OAI

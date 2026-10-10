import OAI.Analysis.LipschitzHilbert.Fourier.SymbolWeights

namespace OAI

/-! The remaining Fourier parameter is averaged against a fixed integrable
weight. A uniform bound survives this averaging with only its fixed mass. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem symbol_average_bound (q : ℕ) (hq : 4≤q) (F : SymbolSpace → ℂ)
    (hF : AEStronglyMeasurable F volume) (C : ℝ)
    (hbound : ∀ᵐ nu ∂volume, ‖F nu‖≤C) :
    Integrable (fun nu => (symbolWeight q nu:ℂ)*F nu) volume ∧
      ‖∫ nu, (symbolWeight q nu:ℂ)*F nu‖≤C*(∫ nu, symbolWeight q nu) := by
  have hw := symbolWeight_integrable q hq
  have hnorm : ∀ᵐ nu ∂volume,
      ‖(symbolWeight q nu:ℂ)*F nu‖≤symbolWeight q nu*C := by
    filter_upwards [hbound] with nu hnu
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (symbolWeight_pos q nu)]
    exact mul_le_mul_of_nonneg_left hnu (symbolWeight_pos q nu).le
  have hi : Integrable (fun nu => (symbolWeight q nu:ℂ)*F nu) volume :=
    (hw.mul_const C).mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul hF) hnorm
  refine ⟨hi,(norm_integral_le_integral_norm _).trans ?_⟩
  calc
    (∫ nu, ‖(symbolWeight q nu:ℂ)*F nu‖)≤∫ nu, symbolWeight q nu*C :=
      integral_mono_ae hi.norm (hw.mul_const C) hnorm
    _ = C*(∫ nu, symbolWeight q nu) := by rw [integral_mul_const]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI

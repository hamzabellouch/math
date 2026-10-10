import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeRetainedSum

namespace OAI

/-! Retaining logarithmically comparable amplitude masses preserves the
source model's full disparity interval. -/
noncomputable section
namespace LipschitzHilbert

theorem sqrt_mass_ratio (F E : ℝ) (hF : 0<F) (hE : 0<E) :
    0<Real.sqrt (E/F) ∧ E=(Real.sqrt (E/F))^2*F := by
  refine ⟨Real.sqrt_pos.2 (div_pos hE hF),?_⟩
  rw [Real.sq_sqrt (div_pos hE hF).le]
  field_simp

theorem log_amplitude_disparity (F E f g ratio : ℝ)
    (hF : 0<F) (hE : 0<E) (hf : 0<f) (hg : 0<g) (hr : 0<ratio)
    (heq : E=ratio^2*F) :
    Real.log (Real.sqrt (g/f))=
      Real.log ratio+(Real.log (g/E)-Real.log (f/F))/2 := by
  rw [Real.log_sqrt (div_pos hg hf).le,Real.log_div hg.ne' hf.ne',
    Real.log_div hg.ne' hE.ne',Real.log_div hf.ne' hF.ne',heq,
    Real.log_mul (pow_pos hr 2).ne' hF.ne',Real.log_pow]
  ring

theorem retained_amplitude_disparity (F E f g ratio L : ℝ)
    (hF : 0<F) (hE : 0<E) (hf : 0<f) (hg : 0<g) (hr : 0<ratio)
    (heq : E=ratio^2*F) (hL : Real.log ratio=L)
    (hlogf : |Real.log (f/F)|≤L/4) (hlogg : |Real.log (g/E)|≤L/4) :
    L/2≤Real.log (Real.sqrt (g/f)) ∧ Real.log (Real.sqrt (g/f))≤2*L := by
  have hnonneg : 0≤L := by linarith [abs_nonneg (Real.log (f/F))]
  rw [log_amplitude_disparity F E f g ratio hF hE hf hg hr heq,hL]
  obtain ⟨hflo,hfhi⟩ := abs_le.mp hlogf
  obtain ⟨hglo,hghi⟩ := abs_le.mp hlogg
  constructor <;> linarith

end LipschitzHilbert

end

end OAI

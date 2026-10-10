import OAI.Analysis.LipschitzHilbert.Fourier.AnnularFrequencyEnvelope

namespace OAI

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem annularBandSymbol_measurable (psi beta : SchwartzMap ℝ ℂ)
    (l W center : ℝ) (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (annularBandSymbol psi beta l W center u) := by
  have hu' : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => u p.1) := hu.comp measurable_fst
  unfold annularBandSymbol symbolY
  apply Measurable.mul
  · apply psi.continuous.measurable.comp
    fun_prop
  · apply beta.continuous.measurable.comp
    fun_prop

theorem exists_annularBandSymbol_envelope
    (psi beta : SchwartzMap ℝ ℂ) (l W center M B U : ℝ)
    (hl : 0<l) (hW : 0<W) (hU : 0≤U)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U) :
    ∃ q : ℝ×ℝ → ℝ, Integrable q planeMeasure ∧
      ∀ z omega, ‖annularBandSymbol psi beta l W center u (z,omega)‖≤q omega := by
  apply exists_frequency_rectangle_envelope _
    (SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 beta)
    (M/l+U*(|center|+B/W)) (|center|+B/W)
  · intro z omega
    unfold annularBandSymbol
    rw [norm_mul]
    exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ psi _)
      (SchwartzMap.norm_le_seminorm ℝ beta _) (norm_nonneg _) (apply_nonneg _ _)
  · intro z omega hm
    have hp : psi (l*(omega.1+u z*omega.2))≠0 := by
      intro hp; exact hm (by simp [annularBandSymbol,hp])
    have hb : beta (symbolY W omega.2 center)≠0 := by
      intro hb; exact hm (by simp [annularBandSymbol,hb])
    exact annularBandSymbol_support_bounds psi beta l W center M B U hl hW hU hpsi hbeta u hu z omega hp hb

end LipschitzHilbert.PacketRepresentation

end

end OAI

import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram
import OAI.Analysis.LipschitzHilbert.Packets.PacketConvolution

namespace OAI

/-! Cauchy--Schwarz in the actual planar integral pairing. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem planar_pairing_energy (f g : (ℝ×ℝ) → ℂ)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    ‖∫ z, f z*star (g z) ∂planeMeasure‖^2≤
      (∫ z, ‖f z‖^2 ∂planeMeasure)*(∫ z, ‖g z‖^2 ∂planeMeasure) := by
  have hpair : (∫ z, f z*star (g z) ∂planeMeasure)=inner ℂ (hg.toLp g) (hf.toLp f) := by
    rw [memLp_inner_integral]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [RCLike.inner_apply,starRingEnd_apply]
  rw [hpair]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜:=ℂ) (hg.toLp g) (hf.toLp f)) 2
  rw [mul_pow,memLp_toL2_norm_sq,memLp_toL2_norm_sq] at h
  simpa only [mul_comm] using h

theorem planar_pairing_bound_of_energy (f g : (ℝ×ℝ) → ℂ)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure)
    (L E : ℝ) (hL : 0<L) (hE : 0≤E)
    (he : (∫ z, ‖f z‖^2 ∂planeMeasure)≤L^(-40:ℝ)*E) :
    ‖∫ z, f z*star (g z) ∂planeMeasure‖≤
      L^(-20:ℝ)*Real.sqrt E*Real.sqrt (∫ z, ‖g z‖^2 ∂planeMeasure) := by
  have hg0 : 0≤∫ z, ‖g z‖^2 ∂planeMeasure := integral_nonneg fun _ => sq_nonneg _
  have hp := (planar_pairing_energy f g hf hg).trans (mul_le_mul_of_nonneg_right he hg0)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hpow : (L^(-20:ℝ))^2=L^(-40:ℝ) := by
    rw [pow_two,←Real.rpow_add hL]
    norm_num
  simpa only [mul_pow,hpow,Real.sq_sqrt hE,Real.sq_sqrt hg0] using hp

end LipschitzHilbert.PacketRepresentation

end

end OAI

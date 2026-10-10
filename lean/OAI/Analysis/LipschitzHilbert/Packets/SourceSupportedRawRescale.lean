import OAI.Analysis.LipschitzHilbert.Estimates.PlanarHorizontalRescale
import OAI.Analysis.LipschitzHilbert.Estimates.SlopeBoxHorizontalRescale
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedPacketData

namespace OAI

/-! Normalize the physical horizontal scale of raw packet data. All
kernel, derivative and spectral conditions are transported explicitly. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
namespace SupportedTopRawPacketData
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
  {P : PlanarPacketFamily N κ ι} {lo hi K : ℝ} {T : SlopeBox} {D : ℕ}

def horizontalRescale (r : ℝ) (hr : 0 < r)
    (data : SupportedTopRawPacketData P (lo/r) (hi/r) T K D) :
    SupportedTopRawPacketData (P.horizontalRescale r hr) lo hi (T.horizontalRescale r hr) K D where
  raw := fun i j u k y => schwartzDilation (data.raw i j u k y) r hr.ne'
  frequency := data.frequency
  length_le := by
    intro j u
    rw [PlanarPacketFamily.horizontalRescale_length]
    change P.length j/r ≤ K*(T.length/r)
    simpa only [mul_div_assoc] using (div_le_div_iff_of_pos_right hr).mpr (data.length_le j u)
  width_le := data.width_le
  centerX_le := by
    intro j u
    rw [PlanarPacketFamily.horizontalRescale_centerX]
    change |P.centerX j u/r-T.x/r| ≤ K*(T.length/r)
    rw [← sub_div,abs_div,abs_of_pos hr]
    simpa only [mul_div_assoc] using (div_le_div_iff_of_pos_right hr).mpr (data.centerX_le j u)
  centerZ_le := by
    intro j u
    rw [PlanarPacketFamily.horizontalRescale_centerZ,SlopeBox.horizontalRescale_intercept]
    exact data.centerZ_le j u
  wave_eq := by
    intro j u k y
    apply congrArg (fun f : SchwartzMap ℝ ℂ => schwartzDilation f r hr.ne')
    exact data.wave_eq j u k y
  bound := by
    intro i y j u k x
    rw [schwartzDilation_apply,PlanarPacketFamily.horizontalRescale_centerX,
      PlanarPacketFamily.horizontalRescale_length,PlanarPacketFamily.horizontalRescale_centerZ,
      lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    exact data.bound i y j u k (r*x)
  derivative_bound := by
    intro i y j u k x
    rw [schwartzDilation_deriv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      PlanarPacketFamily.horizontalRescale_centerX,PlanarPacketFamily.horizontalRescale_length,
      PlanarPacketFamily.horizontalRescale_centerZ,lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    have h := mul_le_mul_of_nonneg_left (data.derivative_bound i y j u k (r*x)) hr.le
    convert h using 1
    field_simp [(P.length_pos j).ne',hr.ne']
    dsimp only [PlanarPacketFamily.horizontalRescale]
    ring
  low := by
    intro i y j u k ξ hξ
    apply schwartzDilation_low (data.raw i j u k y) r (lo*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply data.low i y j u k η
    convert hη using 1
    ring
  high := by
    intro i y j u k ξ hξ
    apply schwartzDilation_high (data.raw i j u k y) r (hi*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply data.high i y j u k η
    convert hη using 1
    ring
  covariant := by
    intro y j u k x
    exact data.covariant y j u k (r*x)
  continuous := by
    intro i j u k
    change Continuous (fun z : ℝ × ℝ => data.raw i j u k z.1 (r*z.2))
    exact (data.continuous i j u k).comp
      (continuous_fst.prodMk (continuous_const.mul continuous_snd))
  differentiable := by
    intro j u k x y
    exact data.differentiable j u k (r*x) y

end SupportedTopRawPacketData
end LipschitzHilbert

end

end OAI

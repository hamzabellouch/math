import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedRawRescale
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedPacketData

namespace OAI

/-! The second covariant kernel obeys the same horizontal transport. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
namespace SupportedTopCovariantData
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
  {P : PlanarPacketFamily N κ ι} {lo hi K : ℝ} {T : SlopeBox} {D : ℕ}

def horizontalRescale (r : ℝ) (hr : 0 < r)
    {data : SupportedTopRawPacketData P (lo/r) (hi/r) T K D} (second : SupportedTopCovariantData data) :
    SupportedTopCovariantData (data.horizontalRescale r hr) where
  second := fun j u k y => schwartzDilation (second.second j u k y) r hr.ne'
  bound := by
    intro y j u k x
    rw [schwartzDilation_apply,PlanarPacketFamily.horizontalRescale_centerX,
      PlanarPacketFamily.horizontalRescale_length,PlanarPacketFamily.horizontalRescale_centerZ,
      lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    exact second.bound y j u k (r*x)
  derivative_bound := by
    intro y j u k x
    rw [schwartzDilation_deriv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      PlanarPacketFamily.horizontalRescale_centerX,PlanarPacketFamily.horizontalRescale_length,
      PlanarPacketFamily.horizontalRescale_centerZ,lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    have h := mul_le_mul_of_nonneg_left (second.derivative_bound y j u k (r*x)) hr.le
    convert h using 1
    field_simp [(P.length_pos j).ne',hr.ne']
    dsimp only [PlanarPacketFamily.horizontalRescale]
    ring
  low := by
    intro y j u k ξ hξ
    apply schwartzDilation_low (second.second j u k y) r (lo*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply second.low y j u k η
    convert hη using 1
    ring
  high := by
    intro y j u k ξ hξ
    apply schwartzDilation_high (second.second j u k y) r (hi*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply second.high y j u k η
    convert hη using 1
    ring
  covariant := by
    intro y j u k x
    exact second.covariant y j u k (r*x)
  continuous := by
    intro j u k
    change Continuous (fun z : ℝ × ℝ => second.second j u k z.1 (r*z.2))
    exact (second.continuous j u k).comp
      (continuous_fst.prodMk (continuous_const.mul continuous_snd))
  differentiable := by
    intro j u k x y
    exact second.differentiable j u k (r*x) y

end SupportedTopCovariantData
end LipschitzHilbert

end

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIncomingBootstrap
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteEndpoint

namespace OAI

/-! The full incoming two-vector is small for an outgoing solution. Its
qualitative terminal condition is derived by the finite incoming bootstrap. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_outgoing_incoming_bound
    (L T C K sigma : ℝ) (m : ℕ) (hLT : L < T) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hgap : 5*C < 2*(m : ℝ)) (hdecay : C+(sigma-2*(m : ℝ)) < 0)
    (c : ℝ → Fin 2 → ℝ) (A R : ℝ → SpectralRemoteOperator) (Y : ℝ → SpectralRemoteSpace)
    (hc : HasLogJetBound 0 c) (hA : HasLogJetBound 0 A)
    (hR : HasLogJetBound (-2*(m : ℝ)) R) (hY : HasLogJetBound sigma Y)
    (hcc : ContinuousOn c (Ioi L)) (hAc : ContinuousOn A (Ioi L)) (hRc : ContinuousOn R (Ioi L))
    (hsmall : ∀ t ∈ Ioi L, ∀ k, |c t k| ≤ 1/32)
    (hblock : ∀ t ∈ Ioi L, spectralRemoteBlockOperator (A t) = A t)
    (hAb : ∀ t ∈ Ioi L, ‖A t‖ ≤ C) (hAR : ∀ t ∈ Ioi L, ‖A t+R t‖ ≤ C)
    (hRb : ∀ t ∈ Ioi L, ‖R t‖ ≤ K*Real.exp (-2*(m : ℝ)*t))
    (hode : ∀ t ∈ Ioi L,
      HasDerivAt Y ((spectralRemoteLeadingOperator (c t) t+A t+R t) (Y t)) t) :
    ‖spectralPhysicalDerivativeMap (Y T)‖ ≤
      (2*K/(2*(m : ℝ)-5*C)*Real.exp (-2*(m : ℝ)*T))*‖Y T‖ := by
  have hb (i : SpectralRemoteIndex) (hi : i.2 = 1) :
      ‖spectralRemoteCoordinate i (Y T)‖ ≤
        2*K/(2*(m : ℝ)-5*C)*Real.exp (-2*(m : ℝ)*T)*‖Y T‖ := by
    have hyi := spectralRemote_incoming_bootstrap sigma m c A R Y hc hA hR hY
      ((eventually_gt_atTop L).mono (fun t ht => hsmall t ht))
      ((eventually_gt_atTop L).mono (fun t ht => hblock t ht))
      ((eventually_gt_atTop L).mono (fun t ht => hode t ht)) i hi
    have hh := spectralRemote_incoming_estimate L T C (2*(m : ℝ)) K
      (sigma-2*(m : ℝ)) hLT hC hK hgap hdecay c A R Y hcc hAc hRc hblock
      hAb hAR (by simpa only [neg_mul] using hRb) hode i hi hyi
    simpa only [neg_mul] using hh
  have hp := hb (0,1) rfl
  have hm := hb (1,1) rfl
  change max ‖(Y T).1.2‖ ‖(Y T).2.2‖ ≤ _
  apply max_le
  · simpa only [spectralRemoteCoordinate_apply,spectralRemoteBasis_repr,Prod.fst,Prod.snd,
      ite_true,ite_false,show (1 : Fin 2) ≠ 0 by decide] using hp
  · simpa only [spectralRemoteCoordinate_apply,spectralRemoteBasis_repr,Prod.fst,Prod.snd,
      ite_true,ite_false,show (1 : Fin 2) ≠ 0 by decide] using hm

end DefocusingNLS

end OAI

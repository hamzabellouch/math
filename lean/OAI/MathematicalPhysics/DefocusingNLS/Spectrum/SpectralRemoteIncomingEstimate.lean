import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIncomingIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteCoordinateBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteRootPropagation

namespace OAI

/-! The terminal integral applied to the actual four-coordinate root system. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def spectralRemoteScalarCoefficient (c : ℝ → Fin 2 → ℝ)
    (A : ℝ → SpectralRemoteOperator) (i : SpectralRemoteIndex) (t : ℝ) : ℂ :=
  (Real.exp t : ℂ)^2*spectralRemoteDiagonalRoot (c t) i+spectralRemoteOperatorMatrix (A t) i i

theorem spectralRemote_incoming_estimate
    (L T C m K sigma : ℝ) (hLT : L < T) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hgap : 5*C < m) (hdecay : C+sigma < 0)
    (c : ℝ → Fin 2 → ℝ) (A R : ℝ → SpectralRemoteOperator) (Y : ℝ → SpectralRemoteSpace)
    (hc : ContinuousOn c (Ioi L)) (hA : ContinuousOn A (Ioi L)) (hR : ContinuousOn R (Ioi L))
    (hblock : ∀ t ∈ Ioi L, spectralRemoteBlockOperator (A t) = A t)
    (hAb : ∀ t ∈ Ioi L, ‖A t‖ ≤ C) (hAR : ∀ t ∈ Ioi L, ‖A t+R t‖ ≤ C)
    (hRb : ∀ t ∈ Ioi L, ‖R t‖ ≤ K*Real.exp (-m*t))
    (hY : ∀ t ∈ Ioi L,
      HasDerivAt Y ((spectralRemoteLeadingOperator (c t) t+A t+R t) (Y t)) t)
    (i : SpectralRemoteIndex) (hi : i.2 = 1)
    (hyi : HasLogJetBound sigma (fun t => spectralRemoteCoordinate i (Y t))) :
    ‖spectralRemoteCoordinate i (Y T)‖ ≤
      2*K/(m-5*C)*Real.exp (-m*T)*‖Y T‖ := by
  let b := spectralRemoteScalarCoefficient c A i
  let y := fun t => spectralRemoteCoordinate i (Y t)
  let f := fun t => spectralRemoteCoordinate i (R t (Y t))
  have hYc : ContinuousOn Y (Ioi L) := fun t ht => (hY t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Ioi L) :=
    (spectralRemoteCoordinate i).continuous.comp_continuousOn (hR.clm_apply hYc)
  have hbc : ContinuousOn b (Ioi L) := by
    have he : ContinuousOn (fun t => spectralRemoteOperatorMatrix (A t) i i) (Ioi L) := by
      simp_rw [spectralRemoteOperatorMatrix_entry]
      exact (spectralRemoteCoordinate i).continuous.comp_continuousOn
        (hA.clm_apply continuousOn_const)
    exact ((Complex.continuous_ofReal.comp Real.continuous_exp).continuousOn.pow 2 |>.mul
      ((spectralRemote_diagonal_root_continuous i).comp_continuousOn hc)).add he
  have hbnd (t : ℝ) (ht : t ∈ Ioi L) : |(b t).re| ≤ C :=
    (spectralRemote_incoming_coefficient_re (c t) t (A t) i).trans (hAb t ht)
  have hy (t : ℝ) (ht : t ∈ Ici T) : HasDerivAt y (b t*y t+f t) t :=
    spectralRemote_incoming_equation Y (c t) (A t) (R t) i hi
      (hblock t (lt_of_lt_of_le hLT ht)) t (hY t (lt_of_lt_of_le hLT ht))
  have hforcing (t : ℝ) (ht : t ∈ Ici T) :
      ‖f t‖ ≤ (2*K)*‖Y T‖*Real.exp (4*C*(t-T))*Real.exp (-m*t) := by
    have hp := (spectralRemote_root_propagation c (fun u => A u+R u) Y T t C ht hC
      (fun u hu => by simpa only [add_assoc] using hY u (lt_of_lt_of_le hLT hu.1))
      (fun u hu => hAR u (lt_of_lt_of_le hLT hu.1))).1
    calc
      _ ≤ ‖R t (Y t)‖ := spectralRemoteCoordinate_norm_le i _
      _ ≤ ‖R t‖*‖Y t‖ := (R t).le_opNorm _
      _ ≤ (K*Real.exp (-m*t))*(2*Real.exp (4*C*(t-T))*‖Y T‖) :=
        mul_le_mul (hRb t (lt_of_lt_of_le hLT ht)) hp (norm_nonneg _)
          (mul_nonneg hK (Real.exp_pos _).le)
      _ = _ := by ring
  have hh := spectralRemote_incoming_terminal L T C m (2*K) ‖Y T‖ hLT hgap b y f hbc
    (hfc.mono (fun _ ht => lt_of_lt_of_le hLT ht)) hbnd hy
    (spectralRemote_integrating_factor_limit L T C sigma hLT b y hbc hbnd hyi hdecay) hforcing
  exact hh.trans_eq (by ring)

end DefocusingNLS

end OAI

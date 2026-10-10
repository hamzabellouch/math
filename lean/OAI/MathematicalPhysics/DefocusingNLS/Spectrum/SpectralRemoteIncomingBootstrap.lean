import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIncomingEstimate
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIncomingInverse
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIndividualOperations

namespace OAI

/-! The incoming ODE improves an outgoing symbol by two powers per step.
This proves the vanishing terminal condition used by the integral estimate. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_incoming_bootstrap (sigma : ℝ) (m : ℕ)
    (c : ℝ → Fin 2 → ℝ) (A R : ℝ → SpectralRemoteOperator) (Y : ℝ → SpectralRemoteSpace)
    (hc : HasLogJetBound 0 c) (hA : HasLogJetBound 0 A)
    (hR : HasLogJetBound (-2*(m : ℝ)) R) (hY : HasLogJetBound sigma Y)
    (hsmall : ∀ᶠ t in atTop, ∀ k, |c t k| ≤ 1/32)
    (hblock : ∀ᶠ t in atTop, spectralRemoteBlockOperator (A t) = A t)
    (hode : ∀ᶠ t in atTop,
      HasDerivAt Y ((spectralRemoteLeadingOperator (c t) t+A t+R t) (Y t)) t)
    (i : SpectralRemoteIndex) (hi : i.2 = 1) :
    HasLogJetBound (sigma-2*(m : ℝ)) (fun t => spectralRemoteCoordinate i (Y t)) := by
  let y := fun t => spectralRemoteCoordinate i (Y t)
  let b := fun t => spectralRemoteOperatorMatrix (A t) i i
  let f := fun t => spectralRemoteCoordinate i (R t (Y t))
  let a := fun t => (spectralRemoteDiagonalRoot (c t) i)⁻¹
  let scalar := (spectralRemoteCoordinate i).restrictScalars ℝ
  let restrict := ContinuousLinearMap.restrictScalarsL ℂ SpectralRemoteSpace SpectralRemoteSpace ℝ ℝ
  have hy : HasLogJetBound sigma y := hY.map scalar
  have hb : HasLogJetBound 0 b := by
    have hh := ((hA.map restrict).apply (HasLogJetBound.const (spectralRemoteBasis i))).map scalar
    simp only [zero_add] at hh
    convert hh using 1
    funext t
    exact spectralRemoteOperatorMatrix_entry (A t) i i
  have hf : HasLogJetBound (sigma-2*(m : ℝ)) f := by
    have hh := ((hR.map restrict).apply hY).map scalar
    convert hh using 1
    · ring
    · rfl
  have ha : HasLogJetBound 0 a := spectralRemote_incoming_inverse_single c hc hsmall i hi
  have hsolve : ∀ᶠ t in atTop, y t = (Real.exp (-2*t) : ℂ)*a t*(deriv y t-b t*y t-f t) := by
    filter_upwards [hsmall,hblock,hode] with t ht hb hyt
    have hd := (spectralRemote_incoming_equation Y (c t) (A t) (R t) i hi hb t hyt).deriv
    have hroot : spectralRemoteDiagonalRoot (c t) i ≠ 0 := norm_pos_iff.mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3/8) (spectralRemote_incoming_root_bound (c t) i hi ht))
    have he2 : (Real.exp (-2*t) : ℂ) = ((Real.exp t : ℂ)^2)⁻¹ := by
      norm_cast
      rw [← Real.exp_nat_mul,← Real.exp_neg]
      congr 1
      norm_num
    have hexp : (Real.exp t : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos t).ne'
    change deriv y t = _ at hd
    dsimp only [a,b,f,y] at hd ⊢
    rw [he2,hd]
    field_simp [hroot,hexp]
    ring
  exact spectralRemote_incoming_iterate sigma (sigma-2*(m : ℝ)) m a b f y ha hb hf hy hsolve le_rfl

end DefocusingNLS

end OAI

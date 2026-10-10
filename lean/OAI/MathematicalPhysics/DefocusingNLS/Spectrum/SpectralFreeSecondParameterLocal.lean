import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDifferentiatedOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeTailIdentification

namespace OAI

/-! The zero-profile weighted resolvent provides the actual local holomorphic
free H column and its parameter derivative equation. -/

open Filter Topology Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFreeSecond_local_differentiated (ell : ℕ) (νp νm z : ℂ)
    (hq : -1 < (((ell : ℂ)-νm)/2+z).re) :
    ∃ Y : ℂ → ℝ → E₄,
      (∀ᶠ lam in 𝓝 z, ∀ t, max 0 (Real.log 4/2) ≤ t →
        Y lam t = spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+lam) t) ∧
      (∀ t, AnalyticAt ℂ (fun lam => Y lam t) z) ∧
      ∀ t, 0 ≤ t → HasDerivAt (fun s => deriv (fun lam => Y lam s) z)
        (circularLeadingField t (deriv (fun lam => Y lam t) z) +
          circularBoundedField (νp-2*z) (νm-2*z) ((ell*(ell+10) : ℕ) : ℂ) 1 0
            (deriv (fun lam => Y lam t) z) + circularPointSlopeCLM νp νm z (Y z t)) t := by
  let η : ℂ := ((ell*(ell+10) : ℕ) : ℂ)
  obtain ⟨j,hj⟩ := exists_nat_gt (circularFieldBound (νp-2*z) (νm-2*z) η 1 0)
  have hgap : circularFieldBound (νp-2*z) (νm-2*z) η 1 0 < 2*((j+1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  obtain ⟨Y,hYa,hYd,_,hYe,hYp⟩ := exists_differentiated_circular_outgoing
    νp νm η 1 (by omega) 0 (0,1) (j+1) (by omega)
    (0 : ℝ →ᵇ ℂ) (0 : ℝ →ᵇ ℂ) (by
      intro t _
      simp [radialExteriorPolynomialFunction])
  have hnorm : ‖(0 : ℝ →ᵇ ℂ)‖ = 0 := norm_zero
  have hcont : Continuous (fun lam : ℂ => circularFieldBound (νp-2*lam) (νm-2*lam) η 1 0) := by
    unfold circularFieldBound
    fun_prop
  have hqc : Continuous (fun lam : ℂ => (((ell : ℂ)-νm)/2+lam).re) := by fun_prop
  have hnear : ∀ᶠ lam in 𝓝 z,
      circularFieldBound (νp-2*lam) (νm-2*lam) η 1 0 < 2*((j+1 : ℕ) : ℝ) ∧
      -1 < (((ell : ℂ)-νm)/2+lam).re :=
    (hcont.continuousAt.eventually (gt_mem_nhds hgap)).and
      (hqc.continuousAt.eventually (lt_mem_nhds hq))
  refine ⟨Y,?_,?_,?_⟩
  · filter_upwards [hnear] with lam hlam
    obtain ⟨v,hv⟩ := hYe lam
    have he : (ell : ℂ)-2*(((ell : ℂ)-νm)/2+lam)=νm-2*lam := by ring
    apply spectralFreeSecond_eq_of_tail ell (((ell : ℂ)-νm)/2+lam) (νp-2*lam) hlam.2 j (Y lam) v
    · simpa only [he] using hlam.1
    · simpa only [he,BoundedContinuousFunction.coe_zero,Pi.zero_apply,η] using
        hYd lam (by simpa only [hnorm] using hlam.1)
    · simpa only [he,η] using hv
  · exact hYa z (by simpa only [hnorm] using hgap)
  · simpa only [BoundedContinuousFunction.coe_zero,Pi.zero_apply,η] using
      hYp z (by simpa only [hnorm] using hgap)

end DefocusingNLS

end OAI

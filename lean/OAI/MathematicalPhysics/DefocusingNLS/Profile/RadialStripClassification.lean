import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralStripBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactSpectralClassification

namespace OAI

/-! The escape bound makes angular degree finite and the spectral parameter
compact, giving the full classification on the upper counting strip. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSpectralMode_strip_classification (hRou : RectangleRouche)
    (N : ℕ) (hN : 7 ≤ N) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ ell : ℕ, ∀ lam : ℂ,
      -(1/32 : ℝ) ≤ lam.re → lam.re ≤ 4 → 0 ≤ lam.im →
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam) →
      (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2) := by
  obtain ⟨M,hbound⟩ := radialMatchedSpectralMode_strip_bound N hN
  obtain ⟨B,hB⟩ := exists_nat_gt M
  let K : Set ℂ := Metric.closedBall 0 (4+max M 0)
  have hK : IsCompact K := isCompact_closedBall 0 _
  have hclasses := (eventually_all_finset (Finset.range B)).mpr
    (fun ell _ => radialMatchedSpectralMode_compact_classification hRou ell N hN K hK)
  filter_upwards [hbound,hclasses] with n hn hc z hX hz ell lam hl hu hi hmode
  have hb := hn z hX hz ell lam hl hu hi hmode
  have hell : ell < B := by exact_mod_cast (lt_of_le_of_lt (by linarith : (ell : ℝ) ≤ M) hB)
  have hmem : lam ∈ K := by
    change dist lam 0 ≤ 4+max M 0
    rw [dist_zero_right]
    have hre : |lam.re| ≤ 4 := abs_le.mpr ⟨by linarith,hu⟩
    have him : |lam.im| ≤ max M 0 := by rw [abs_of_nonneg hi]; exact (by linarith : lam.im ≤ M).trans (le_max_left _ _)
    exact (Complex.norm_le_abs_re_add_abs_im lam).trans (add_le_add hre him)
  apply hc ell (Finset.mem_range.mpr hell) z hX hz lam hmem hl
  have heq : (((ell : ℝ)*(ell+10) : ℝ) : ℂ)=(ell : ℂ)*(ell+10) := by push_cast; rfl
  simpa only [heq] using hmode

end DefocusingNLS

end OAI

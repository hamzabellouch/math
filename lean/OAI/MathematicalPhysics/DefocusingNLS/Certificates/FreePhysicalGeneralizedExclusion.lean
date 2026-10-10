import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreePhysicalSymmetryNoChain
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeChainCore
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinColumnDerivative

namespace OAI

/-! The physical free boundary problem has no first generalized eigenvector
at a symmetry root, assuming the rectangle form of Rouché's theorem. -/

open Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialFreePhysical_generalized_exclusion (hRou : RectangleRouche) (w : RadialShootingDisk)
    (hw : diskProfile w=0) (ell : ℕ) (lam : ℂ)
    (hs : (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2))
    (R : ℝ) (hR : radialShootingR w < R) (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0)
    (U₀ U₁ : ℝ → E₄)
    (hU₀ : ∀ r ∈ Icc (radialShootingR w) R,
      U₀ r = a • spectralFreePositivePhysical ell (radialShootingB w) lam r +
        b • spectralFreeNegativePhysical ell (radialShootingB w) lam r)
    (hC₀ : spectralFreeCoreBoundary ell (radialShootingR w) (U₀ (radialShootingR w))=0)
    (hC₁ : spectralFreeCoreBoundary ell (radialShootingR w) (U₁ (radialShootingR w))=0)
    (hcont : ContinuousOn U₁ (Icc (radialShootingR w) R))
    (hD : ∀ r ∈ Ioo (radialShootingR w) R, HasDerivAt U₁
      (spectralFreePhysicalPairField (radialShootingB w) lam ((ell : ℂ)*((ell : ℂ)+10)) r (U₁ r) +
        spectralFreeChainSource (U₀ r)) r)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB w) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB w) lam R)) ≠ 0)
    (hRobin : spectralPhysicalDerivativeMap (U₁ R) =
      spectralJetRobin (spectralFreePositivePhysical ell (radialShootingB w) lam R)
        (spectralFreeNegativePhysical ell (radialShootingB w) lam R) (spectralPhysicalValueMap (U₁ R)) +
      deriv (fun z => spectralJetRobin (spectralFreePositivePhysical ell (radialShootingB w) z R)
        (spectralFreeNegativePhysical ell (radialShootingB w) z R)) lam (spectralPhysicalValueMap (U₀ R))) : False := by
  let L := radialShootingR w
  let β := radialShootingB w
  let P := spectralFreePositivePhysical ell β lam
  let N := spectralFreeNegativePhysical ell β lam
  let DP := fun r => deriv (fun z => spectralFreePositivePhysical ell β z r) lam
  let DN := fun r => deriv (fun z => spectralFreeNegativePhysical ell β z r) lam
  have hL : 0 < L := by have := (radialShooting_geometry w).2.1; dsimp [L]; linarith
  have hhalf : -(1/32 : ℝ) ≤ lam.re := by
    rcases hs with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  have hq (h : ℝ) : -1 < (spectralQ ell h β lam).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have hlog (r : ℝ) (hr : r ∈ Icc L R) : max 0 (Real.log 4/2) < Real.log r :=
    spectralFreeRadius_log r ((radialShooting_geometry w).2.1.trans hr.1)
  have hDP (r : ℝ) (hr : r ∈ Icc L R) : HasDerivAt DP
      (spectralFreePhysicalPairField β lam ((ell : ℂ)*((ell : ℂ)+10)) r (DP r) +
        spectralFreeChainSource (P r)) r :=
    spectralFreePositivePhysical_parameter_hasDerivAt ell β lam (hq 1) r
      (hL.trans_le hr.1) (hlog r hr)
  have hDN (r : ℝ) (hr : r ∈ Icc L R) : HasDerivAt DN
      (spectralFreePhysicalPairField β lam ((ell : ℂ)*((ell : ℂ)+10)) r (DN r) +
        spectralFreeChainSource (N r)) r :=
    spectralFreeNegativePhysical_parameter_hasDerivAt ell β lam (hq (-1)) r
      (hL.trans_le hr.1) (hlog r hr)
  have hP (r : ℝ) (hr : r ∈ Icc L R) :=
    spectralFreePositivePhysical_hasDerivAt ell β lam hhalf r (hL.trans_le hr.1)
  have hN (r : ℝ) (hr : r ∈ Icc L R) :=
    spectralFreeNegativePhysical_hasDerivAt ell β lam hhalf r (hL.trans_le hr.1)
  have hRR : R ∈ Icc L R := ⟨hR.le,le_rfl⟩
  obtain ⟨c,hc⟩ := spectralJetRobin_derivative_plane
    (fun z => spectralFreePositivePhysical ell β z R) (fun z => spectralFreeNegativePhysical ell β z R) lam
    (spectralFreePositivePhysical_analyticAt ell β lam (hq 1) R (hlog R hRR).le)
    (spectralFreeNegativePhysical_analyticAt ell β lam (hq (-1)) R (hlog R hRR).le)
    hdet a b (U₀ R) (U₁ R) (hU₀ R hRR) hRobin
  obtain ⟨hbase,hzero⟩ := spectralFreeChain_core_coefficients β lam
    ((ell : ℂ)*((ell : ℂ)+10)) L R hL hR a b U₀ U₁ P N DP DN
    (spectralFreeCoreBoundaryCLM ell L) hU₀
    (by simpa only [spectralFreeCoreBoundaryCLM_apply] using hC₀)
    (by simpa only [spectralFreeCoreBoundaryCLM_apply] using hC₁)
    hcont hD hP hN hDP hDN c hc
  simp only [spectralFreeCoreBoundaryCLM_apply] at hbase hzero
  have hLL : L ∈ Icc L R := ⟨le_rfl,hR.le⟩
  have hCP := (spectralFreeCoreBoundary_hasDerivAt ell L
    (fun z => spectralFreePositivePhysical ell β z L) (DP L) lam
      (spectralFreePositivePhysical_analyticAt ell β lam (hq 1) L (hlog L hLL).le).differentiableAt.hasDerivAt).deriv
  have hCN := (spectralFreeCoreBoundary_hasDerivAt ell L
    (fun z => spectralFreeNegativePhysical ell β z L) (DN L) lam
      (spectralFreeNegativePhysical_analyticAt ell β lam (hq (-1)) L (hlog L hLL).le).differentiableAt.hasDerivAt).deriv
  have hno := radialFreePhysical_symmetry_no_chain hRou w hw ell lam hs a b c.1 c.2 hab hbase
  apply hno
  rw [hCP,hCN]
  exact hzero

end DefocusingNLS

end OAI

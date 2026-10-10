import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeBasisParameter
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoreBoundaryLinear
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeRadiusLog
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralKernelCoefficientLine
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeBoundaryMultiplicity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeSymmetryNoChain

namespace OAI

/-! A simple determinant zero excludes chains of the physical H columns
at every symmetry root, assuming the rectangle form of Rouché's theorem. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialFreePhysical_symmetry_no_chain (hR : RectangleRouche) (w : RadialShootingDisk)
    (hw : diskProfile w=0) (ell : ℕ) (lam : ℂ)
    (hs : (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2)) :
    let r := radialShootingR w
    let b := radialShootingB w
    let U := fun z => spectralFreeCoreBoundary ell r (spectralFreePositivePhysical ell b z r)
    let V := fun z => spectralFreeCoreBoundary ell r (spectralFreeNegativePhysical ell b z r)
    ∀ a b A B : ℂ, (a≠0 ∨ b≠0) → a • U lam+b • V lam=0 →
      A • U lam+B • V lam+a • deriv U lam+b • deriv V lam≠0 := by
  let r := radialShootingR w
  let b := radialShootingB w
  let U := fun z => spectralFreeCoreBoundary ell r (spectralFreePositivePhysical ell b z r)
  let V := fun z => spectralFreeCoreBoundary ell r (spectralFreeNegativePhysical ell b z r)
  have hgeom : 3 ≤ r := (radialShooting_geometry w).2.1
  have hr : 0 < r := by linarith
  have hlog := spectralFreeRadius_log r hgeom
  have hhalf : -(1/32 : ℝ)<lam.re := by
    rcases hs with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  have hq (h : ℝ) : -1 < (spectralQ ell h b lam).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have hU : AnalyticAt ℂ U lam := spectralFreeCoreBoundary_analyticAt ell r _ lam
    (spectralFreePositivePhysical_analyticAt ell b lam (hq 1) r hlog.le)
  have hV : AnalyticAt ℂ V lam := spectralFreeCoreBoundary_analyticAt ell r _ lam
    (spectralFreeNegativePhysical_analyticAt ell b lam (hq (-1)) r hlog.le)
  have hu : U lam ≠ 0 := spectralFreePositivePhysical_core_ne_zero ell b r lam hr hhalf.le
  have horder : analyticOrderAt (fun z => matchingColumnDeterminant (U z) (V z)) lam=1 := by
    change analyticOrderAt (spectralFreeCoreDeterminant ell b r) lam=1
    rw [spectralFreeCoreDeterminant_order ell b r lam hr hhalf]
    simpa only [ite_eq_left hs] using radialFree_spectral_order hR w hw ell lam hhalf.le
  exact matchingColumn_simple_zero_no_chain U V lam hU hV hu horder

end DefocusingNLS

end OAI

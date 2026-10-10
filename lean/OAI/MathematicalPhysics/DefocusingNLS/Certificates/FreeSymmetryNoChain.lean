import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSpectralClassification
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingSimpleZero

namespace OAI

/-! The actual free H columns at each symmetry root admit no differentiated
matching chain. This applies the simple-zero calculation without introducing
an additional spectral assumption. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialFree_symmetry_no_chain (hR : RectangleRouche) (w : RadialShootingDisk)
    (hw : diskProfile w=0) (ell : ℕ) (lam : ℂ)
    (hs : (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2)) :
    let U := fun z => slowBoundaryColumn
      (spectralQ ell 1 (radialShootingB w) z) (ell+6)
      (Complex.I*((radialShootingR w)^2/4 : ℝ))
    let V := fun z => slowBoundaryColumn
      (spectralQ ell (-1) (radialShootingB w) z) (ell+6)
      (-Complex.I*((radialShootingR w)^2/4 : ℝ))
    ∀ a b A B : ℂ, (a≠0 ∨ b≠0) → a • U lam+b • V lam=0 →
      A • U lam+B • V lam+a • deriv U lam+b • deriv V lam≠0 := by
  let b := radialShootingB w
  let Z := (radialShootingR w)^2/4
  let U := fun z => slowBoundaryColumn (spectralQ ell 1 b z) (ell+6) (Complex.I*Z)
  let V := fun z => slowBoundaryColumn (spectralQ ell (-1) b z) (ell+6) (-Complex.I*Z)
  have hD := radialShooting_freeMatchingDisk w
  have hZ : Z≠0 := by
    have hh := (abs_le.mp (freeMatchingDisk_subset_certificate_box hD).2).1
    intro he
    norm_num [show (radialShootingR w)^2/4=Z from rfl,he] at hh
  have hhalf : -(1/32 : ℝ)≤lam.re := by
    rcases hs with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  have hU : AnalyticAt ℂ U lam := by
    simpa only [U,Complex.ofReal_one,one_mul] using
      analyticAt_spectralSlowColumn ell 1 b Z lam (by norm_num) hZ hhalf
  have hV : AnalyticAt ℂ V lam := by
    simpa only [V,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
      analyticAt_spectralSlowColumn ell (-1) b Z lam (by norm_num) hZ hhalf
  have hu : U lam≠0 := slowBoundaryColumn_ne_zero _ _ _
    (by rw [spectralQ_re]; linarith [Nat.cast_nonneg (α := ℝ) ell])
    (by simp) (by simpa using hZ)
  have horder : analyticOrderAt (fun z => matchingColumnDeterminant (U z) (V z)) lam=1 := by
    change analyticOrderAt (spectralSlowDeterminant ell b Z) lam=1
    simpa only [ite_eq_left hs] using
      radialFree_spectral_order hR w hw ell lam hhalf
  exact matchingColumn_simple_zero_no_chain U V lam hU hV hu horder

end DefocusingNLS

end OAI

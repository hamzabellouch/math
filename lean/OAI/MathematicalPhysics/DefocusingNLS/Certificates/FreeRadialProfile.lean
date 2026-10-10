import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeExterior
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularPathEquation

namespace OAI

/-! The actual flat-core/free-exterior limiting profile and its matching derivative. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def freeProfileRadius (Z : ℝ) : ℝ := 2*Real.sqrt Z

noncomputable def freeRadialExterior (b Z r : ℝ) : ℂ :=
  regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*((r^2/4 : ℝ) : ℂ)) /
    regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))

noncomputable def freeRadialProfile (b Z r : ℝ) : ℂ :=
  if r ≤ freeProfileRadius Z then 1 else freeRadialExterior b Z r

theorem freeProfileRadius_pos {Z : ℝ} (hZ : 0 < Z) : 0 < freeProfileRadius Z := by
  exact mul_pos (by norm_num) (Real.sqrt_pos.2 hZ)

theorem freeProfileRadius_sq {Z : ℝ} (hZ : 0 ≤ Z) :
    (freeProfileRadius Z)^2/4=Z := by
  dsimp [freeProfileRadius]
  nlinarith [Real.sq_sqrt hZ]

theorem freeRadialExterior_at_radius (b Z : ℝ) (hZ : 0 ≤ Z)
    (hH : regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)) ≠ 0) :
    freeRadialExterior b Z (freeProfileRadius Z)=1 := by
  simp only [freeRadialExterior,freeProfileRadius_sq hZ,div_self hH]

theorem hasDerivAt_freeRadialExterior (b Z r : ℝ) (hr : 0 < r) :
    HasDerivAt (freeRadialExterior b Z)
      ((-Complex.I*((r/2 : ℝ) : ℂ))*
        deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6)
          (-Complex.I*((r^2/4 : ℝ) : ℂ)) /
        regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))) r := by
  have hq : -1 < (-Complex.I*(b : ℂ)).re := by simp
  have hx : -Complex.I*((r^2/4 : ℝ) : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.2
    right
    simp only [neg_mul,Complex.neg_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    nlinarith [sq_pos_of_pos hr]
  have hg : HasDerivAt (fun t : ℝ => -Complex.I*((t^2/4 : ℝ) : ℂ))
      (-Complex.I*((r/2 : ℝ) : ℂ)) r := by
    convert! (((hasDerivAt_id r).pow 2).div_const 4).ofReal_comp.const_mul (-Complex.I) using 1
    simp only [id_eq]
    push_cast
    ring
  have h := (analyticOnNhd_regularizedSlowSolution_slit (-Complex.I*(b : ℂ)) 6 hq _ hx).differentiableAt.hasDerivAt.scomp r hg
  change HasDerivAt (fun t : ℝ => regularizedSlowSolution (-Complex.I*(b : ℂ)) 6
    (-Complex.I*((t^2/4 : ℝ) : ℂ)) /
    regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))) _ r
  convert! h.div_const (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))) using 1

theorem hasDerivAt_freeRadialExterior_at_radius (b Z : ℝ) (hZ : 0 < Z)
    (hD : deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ))=0) :
    HasDerivAt (freeRadialExterior b Z) 0 (freeProfileRadius Z) := by
  simpa only [freeProfileRadius_sq hZ.le,hD,mul_zero,zero_div] using
    hasDerivAt_freeRadialExterior b Z _ (freeProfileRadius_pos hZ)

theorem hasDerivAt_freeRadialProfile_at_radius (b Z : ℝ) (hZ : 0 < Z)
    (hH : regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)) ≠ 0)
    (hD : deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ))=0) :
    HasDerivAt (freeRadialProfile b Z) 0 (freeProfileRadius Z) := by
  have hv := freeRadialExterior_at_radius b Z hZ.le hH
  have hleft : HasDerivWithinAt (freeRadialProfile b Z) 0 (Iic (freeProfileRadius Z))
      (freeProfileRadius Z) := by
    apply (hasDerivAt_const (freeProfileRadius Z) (1 : ℂ)).hasDerivWithinAt.congr
    · intro r hr
      exact ite_eq_left hr
    · exact ite_eq_left le_rfl
  have hright : HasDerivWithinAt (freeRadialProfile b Z) 0 (Ici (freeProfileRadius Z))
      (freeProfileRadius Z) := by
    apply (hasDerivAt_freeRadialExterior_at_radius b Z hZ hD).hasDerivWithinAt.congr
    · intro r hr
      change freeProfileRadius Z ≤ r at hr
      rcases hr.eq_or_lt with he | he
      · subst r
        simpa only [freeRadialProfile,ite_true,le_refl] using hv.symm
      · exact ite_eq_right (not_le.mpr he)
    · simpa only [freeRadialProfile,ite_true,le_refl] using hv.symm
  have h := hleft.union hright
  rw [Iic_union_Ici] at h
  exact h.hasDerivAt (by simp)

theorem hasDerivAt_freeRadialProfile_inside (b Z r : ℝ)
    (hr : r < freeProfileRadius Z) : HasDerivAt (freeRadialProfile b Z) 0 r := by
  apply (hasDerivAt_const r (1 : ℂ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds hr] with t ht
  exact ite_eq_left ht.le

theorem hasDerivAt_freeRadialProfile_outside (b Z r : ℝ) (hZ : 0 < Z)
    (hr : freeProfileRadius Z < r) :
    HasDerivAt (freeRadialProfile b Z)
      ((-Complex.I*((r/2 : ℝ) : ℂ))*
        deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6)
          (-Complex.I*((r^2/4 : ℝ) : ℂ)) /
        regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))) r := by
  apply (hasDerivAt_freeRadialExterior b Z r ((freeProfileRadius_pos hZ).trans hr)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hr] with t ht
  exact ite_eq_right (not_le.mpr ht)

theorem differentiable_freeRadialProfile (b Z : ℝ) (hZ : 0 < Z)
    (hH : regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)) ≠ 0)
    (hD : deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ))=0) :
    Differentiable ℝ (freeRadialProfile b Z) := by
  intro r
  rcases lt_trichotomy r (freeProfileRadius Z) with hr | rfl | hr
  · exact (hasDerivAt_freeRadialProfile_inside b Z r hr).differentiableAt
  · exact (hasDerivAt_freeRadialProfile_at_radius b Z hZ hH hD).differentiableAt
  · exact (hasDerivAt_freeRadialProfile_outside b Z r hZ hr).differentiableAt

theorem freeRadialProfile_nonzero_on_disk
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ))
    (r : ℝ) (hr : 0 ≤ r) :
    freeRadialProfile ((ProfileCertificate.centerB : ℝ)+w.val.re)
      ((ProfileCertificate.centerZ : ℝ)+w.val.im) r ≠ 0 := by
  let b : ℝ := (ProfileCertificate.centerB : ℝ)+w.val.re
  let Z : ℝ := (ProfileCertificate.centerZ : ℝ)+w.val.im
  have hzcoord := (ProfileCertificate.disk_coordinates w).2
  have hZ : 0 < Z := by
    have h := (abs_le.mp hzcoord).1
    dsimp [Z]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at h ⊢
    linarith
  change freeRadialProfile b Z r ≠ 0
  unfold freeRadialProfile
  split_ifs with hi
  · exact one_ne_zero
  · apply div_ne_zero
    · apply (ProfileCertificate.disk_free_exterior w (r^2/4) ?_).1
      have hR := freeProfileRadius_pos hZ
      have hsq := freeProfileRadius_sq hZ.le
      have hri := not_le.mp hi
      nlinarith
    · exact (ProfileCertificate.disk_free_exterior w Z le_rfl).1

end DefocusingNLS

end OAI

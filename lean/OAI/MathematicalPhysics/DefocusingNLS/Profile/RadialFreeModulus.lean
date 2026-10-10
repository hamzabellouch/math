import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeDecay
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowJet

namespace OAI

/-! Modulus monotonicity and the exact normalization factor for the outgoing free H solution. -/

open Set
namespace DefocusingNLS

theorem complex_normSq_log_derivative (F : ℝ → ℂ) (r : ℝ) (f' : ℂ)
    (hd : HasDerivAt F f' r) (hn : F r ≠ 0) :
    HasDerivAt (fun t => Complex.normSq (F t))
      (2*Complex.normSq (F r)*(f'/F r).re) r := by
  apply (hasDerivAt_complex_normSq hd).congr_deriv
  have he : star (F r)*f' = ((‖F r‖^2 : ℝ) : ℂ)*(f'/F r) := by
    calc
      _ = (star (F r)*F r)*(f'/F r) := by field_simp [hn]
      _ = _ := by rw [Complex.star_def,Complex.conj_mul']; push_cast; rfl
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.normSq_eq_norm_sq]
  ring

theorem radialFreeRaw_norm_antitone
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ)) :
    AntitoneOn (fun r => ‖radialFreeRaw ((ProfileCertificate.centerB : ℝ)+w.val.re) r‖)
      (Ici innerBoundaryRadius) := by
  let b := (ProfileCertificate.centerB : ℝ)+w.val.re
  let Z := (ProfileCertificate.centerZ : ℝ)+w.val.im
  have hz := (ProfileCertificate.disk_coordinates w).2
  have hZ : |Z-(ProfileCertificate.centerZ : ℝ)| ≤ (1/100000000 : ℝ) := by
    simpa [Z,ProfileCertificate.radius] using hz
  obtain ⟨hR,_,hshell⟩ := radial_boundary_shell_geometry Z hZ
  have hZ0 : 0 < Z := by
    have hh := (abs_le.mp hz).1
    dsimp [Z]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at hh ⊢
    linarith
  have hsq := freeProfileRadius_sq hZ0.le
  have hRS : freeProfileRadius Z ≤ innerBoundaryRadius := by
    dsimp [freeProfileRadius]
    linarith [hshell.1]
  have hraw (r : ℝ) (hr : innerBoundaryRadius ≤ r) : radialFreeRaw b r ≠ 0 := by
    apply (ProfileCertificate.disk_free_exterior w (r^2/4) ?_).1
    have := hRS.trans hr
    dsimp [freeProfileRadius] at hsq this
    nlinarith
  have hd (r : ℝ) (hr : innerBoundaryRadius ≤ r) :
      HasDerivAt (fun t => Complex.normSq (radialFreeRaw b t))
        (2*Complex.normSq (radialFreeRaw b r)*(radialFreeLog b r).re) r := by
    have hh := radialFreeRaw_hasDerivAt b r (by linarith [innerBoundaryRadius_bounds.1])
    have hh' : HasDerivAt (radialFreeRaw b) (deriv (radialFreeRaw b) r) r :=
      hh.deriv ▸ hh
    exact complex_normSq_log_derivative _ r _ hh' (hraw r hr)
  have hc : ContinuousOn (fun t => Complex.normSq (radialFreeRaw b t))
      (Ici innerBoundaryRadius) := fun r hr => (hd r hr).continuousAt.continuousWithinAt
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici innerBoundaryRadius) hc
    (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
    (fun r hr => mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
      (radialFreeLog_nonpos_on_disk w r (interior_subset hr)))
  intro r hr s hs hrs
  have h := hanti hr hs hrs
  change Complex.normSq (radialFreeRaw b s) ≤ Complex.normSq (radialFreeRaw b r) at h
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at h
  change ‖radialFreeRaw b s‖ ≤ ‖radialFreeRaw b r‖
  nlinarith [norm_nonneg (radialFreeRaw b r),norm_nonneg (radialFreeRaw b s)]

theorem radialFreeSlow_cpow_norm (b t : ℝ) :
    ‖(radialFreeSlowArgument t)^(-Complex.I*(b : ℂ))‖ =
      1/Real.exp (b*Real.pi/2) := by
  rw [Complex.norm_cpow_of_ne_zero (radialFreeSlowArgument_ne_zero t)]
  have ha : (radialFreeSlowArgument t).arg = -(Real.pi/2) := by
    exact (Complex.arg_mul_real (div_pos (Real.exp_pos _) (by norm_num))
      (-Complex.I)).trans Complex.arg_neg_I
  rw [ha]
  simp only [neg_mul,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    mul_zero,one_mul,zero_add,sub_zero,neg_zero,Real.rpow_zero]
  congr 2
  ring

theorem radialFreeSlowValue_norm (b t : ℝ) (m : ℂ) :
    ‖radialFreeSlowValue (-Complex.I*(b : ℂ)) m t‖ =
      (‖m‖/Real.exp (b*Real.pi/2))*‖radialFreeRaw b (Real.exp t)‖ := by
  have he : (Real.exp t)^2=Real.exp (2*t) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  change ‖m*((radialFreeSlowArgument t)^(-Complex.I*(b : ℂ))*
    regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (radialFreeSlowArgument t))‖ = _
  rw [norm_mul,norm_mul,radialFreeSlow_cpow_norm]
  have hh : radialFreeRaw b (Real.exp t)=
      regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (radialFreeSlowArgument t) := by
    dsimp [radialFreeRaw,freeRadialArgument,radialFreeSlowArgument]
    rw [he]
  rw [hh]
  ring

theorem radialFreeSlowValue_norm_antitone
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ)) (m : ℂ) :
    AntitoneOn
      (fun t => ‖radialFreeSlowValue
        (-Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ)) m t‖)
      (Ici (Real.log innerBoundaryRadius)) := by
  intro s hs t ht hst
  change ‖radialFreeSlowValue (-Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ)) m t‖ ≤
    ‖radialFreeSlowValue (-Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ)) m s‖
  rw [radialFreeSlowValue_norm,radialFreeSlowValue_norm]
  apply mul_le_mul_of_nonneg_left
  · apply radialFreeRaw_norm_antitone w
    · change innerBoundaryRadius ≤ Real.exp s
      calc
        innerBoundaryRadius = Real.exp (Real.log innerBoundaryRadius) :=
          (Real.exp_log (by linarith [innerBoundaryRadius_bounds.1])).symm
        _ ≤ Real.exp s := Real.exp_le_exp.mpr hs
    · change innerBoundaryRadius ≤ Real.exp t
      calc
        innerBoundaryRadius = Real.exp (Real.log innerBoundaryRadius) :=
          (Real.exp_log (by linarith [innerBoundaryRadius_bounds.1])).symm
        _ ≤ Real.exp t := Real.exp_le_exp.mpr ht
    · exact Real.exp_le_exp.mpr hst
  · exact div_nonneg (norm_nonneg _) (Real.exp_pos _).le

end DefocusingNLS

end OAI

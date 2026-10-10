import OAI.MathematicalPhysics.DefocusingNLS.Profile.NormalizedSlowEquation

namespace OAI

/-! The actual H solution in the logarithmic slow exterior coordinates. -/

namespace DefocusingNLS

noncomputable def radialFreeSlowArgument (t : ℝ) : ℂ :=
  -Complex.I*(Real.exp (2*t)/4 : ℝ)

noncomputable def radialFreeSlowValue (q m : ℂ) (t : ℝ) : ℂ :=
  m*normalizedSlowSolution q 6 (radialFreeSlowArgument t)

noncomputable def radialFreeSlowVelocity (q m : ℂ) (t : ℝ) : ℂ :=
  m*(2*radialFreeSlowArgument t*normalizedSlowFirst q 6 (radialFreeSlowArgument t))

theorem radialFreeSlowArgument_mem_slit (t : ℝ) :
    radialFreeSlowArgument t ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  right
  simp only [radialFreeSlowArgument,neg_mul,Complex.neg_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
  exact neg_ne_zero.mpr (ne_of_gt (div_pos (Real.exp_pos _) (by norm_num)))

theorem radialFreeSlowArgument_re (t : ℝ) : (radialFreeSlowArgument t).re=0 := by
  simp only [radialFreeSlowArgument,neg_mul,Complex.neg_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_self,neg_zero]

theorem radialFreeSlowArgument_ne_zero (t : ℝ) : radialFreeSlowArgument t ≠ 0 :=
  Complex.slitPlane_ne_zero (radialFreeSlowArgument_mem_slit t)

theorem hasDerivAt_radialFreeSlowArgument (t : ℝ) :
    HasDerivAt radialFreeSlowArgument (2*radialFreeSlowArgument t) t := by
  have he := ((((hasDerivAt_id t).const_mul 2).exp).div_const 4).ofReal_comp.const_mul (-Complex.I)
  convert he using 1
  · rfl
  · simp only [radialFreeSlowArgument,id_eq,mul_one]
    push_cast
    ring

theorem hasDerivAt_radialFreeSlowValue (q m : ℂ) (hq : -1 < q.re) (t : ℝ) :
    HasDerivAt (radialFreeSlowValue q m) (radialFreeSlowVelocity q m t) t := by
  have h := (hasDerivAt_normalizedSlowFirst_value q 6 (radialFreeSlowArgument t) hq
    (radialFreeSlowArgument_mem_slit t)).scomp t (hasDerivAt_radialFreeSlowArgument t)
  convert h.const_mul m using 1
  · rfl
  · dsimp only [radialFreeSlowVelocity]
    ring

theorem hasDerivAt_radialFreeSlowVelocity (q m : ℂ) (hq : -1 < q.re) (t : ℝ) :
    HasDerivAt (radialFreeSlowVelocity q m)
      (-(10-4*q+Complex.I*(Real.exp (2*t)/2 : ℝ))*radialFreeSlowVelocity q m t-
        4*q*(q-5)*radialFreeSlowValue q m t) t := by
  have hx := hasDerivAt_radialFreeSlowArgument t
  have hF := (hasDerivAt_normalizedSlowFirst q 6 (radialFreeSlowArgument t) hq
    (radialFreeSlowArgument_mem_slit t)).scomp t hx
  have hFd : HasDerivAt (fun s => normalizedSlowFirst q 6 (radialFreeSlowArgument s))
      (deriv (normalizedSlowFirst q 6) (radialFreeSlowArgument t)*(2*radialFreeSlowArgument t)) t := by
    convert hF using 1
    · rfl
    · rw [(hasDerivAt_normalizedSlowFirst q 6 (radialFreeSlowArgument t) hq
        (radialFreeSlowArgument_mem_slit t)).deriv]
      simp only [smul_eq_mul]
      ring
  have h := ((hx.const_mul 2).mul hFd).const_mul m
  apply h.congr_deriv
  have hK := normalizedSlowSolution_equation q 6 (radialFreeSlowArgument t) hq
    (by rw [radialFreeSlowArgument_re]) (radialFreeSlowArgument_ne_zero t)
  have hX : Complex.I*(Real.exp (2*t)/2 : ℝ) = -2*radialFreeSlowArgument t := by
    simp only [radialFreeSlowArgument]
    push_cast
    ring
  rw [hX]
  dsimp only [radialFreeSlowVelocity,radialFreeSlowValue]
  linear_combination 4*m*hK

end DefocusingNLS

end OAI

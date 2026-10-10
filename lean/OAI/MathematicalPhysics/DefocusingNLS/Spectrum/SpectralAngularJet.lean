import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularEquation

namespace OAI

/-! Restoring the angular factor in a regular radial spectral column. -/

namespace DefocusingNLS

noncomputable def spectralAngularJet (ell : ℕ) (Y : ℝ → ℂ × ℂ) (r : ℝ) : ℂ × ℂ :=
  ((r : ℂ)^ell*(Y r).1,
    (r : ℂ)^ell*((ell : ℂ)/(r : ℂ)*(Y r).1+(Y r).2))

theorem spectralAngularPower_hasDerivAt (ell : ℕ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => (s : ℂ)^ell) ((r : ℂ)^ell*(ell : ℂ)/(r : ℂ)) r := by
  cases ell with
  | zero => simpa using hasDerivAt_const r (1 : ℂ)
  | succ ell =>
    convert! ((hasDerivAt_id r).ofReal_comp.pow (ell+1)) using 1
    simp only [Nat.add_sub_cancel,id_eq,Complex.ofReal_one,mul_one]
    rw [pow_succ]
    field_simp [Complex.ofReal_ne_zero.mpr hr]

theorem spectralAngularJet_hasDerivAt (ell : ℕ) (h C F : ℂ) (Y : ℝ → ℂ × ℂ)
    (r : ℝ) (hr : r ≠ 0)
    (hY : HasDerivAt Y ((Y r).2,
      -(((2*ell+11 : ℕ) : ℂ)/(r : ℂ)+h*Complex.I*(r : ℂ)/2)*(Y r).2-C*(Y r).1+F) r) :
    HasDerivAt (spectralAngularJet ell Y)
      ((spectralAngularJet ell Y r).2,
       -(11/(r : ℂ)+h*Complex.I*(r : ℂ)/2)*(spectralAngularJet ell Y r).2-
         (C-h*Complex.I*(ell : ℂ)/2-((ell*(ell+10) : ℕ) : ℂ)/(r : ℂ)^2)*
           (spectralAngularJet ell Y r).1+(r : ℂ)^ell*F) r := by
  have hp := spectralAngularPower_hasDerivAt ell r hr
  have hc : HasDerivAt (fun s : ℝ => (ell : ℂ)/(s : ℂ)) (-(ell : ℂ)/(r : ℂ)^2) r := by
    convert! (((hasDerivAt_id r).ofReal_comp.inv (Complex.ofReal_ne_zero.mpr hr)).const_mul
      (ell : ℂ)) using 1
    simp only [id_eq,Complex.ofReal_one]
    ring
  have hv : HasDerivAt (fun s : ℝ => (s : ℂ)^ell*(Y s).1)
      (spectralAngularJet ell Y r).2 r := by
    apply (hp.mul hY.fst).congr_deriv
    unfold spectralAngularJet
    ring
  have hd := (hv.prodMk (hp.mul ((hc.mul hY.fst).add hY.snd)))
  apply hd.congr_deriv
  apply Prod.ext
  · rfl
  · unfold spectralAngularJet
    simp only [Pi.mul_apply,Pi.add_apply]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr]
    ring

end DefocusingNLS

end OAI

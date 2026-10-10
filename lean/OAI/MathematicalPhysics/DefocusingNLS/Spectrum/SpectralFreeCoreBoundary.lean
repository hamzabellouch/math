import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSecondBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEndpointMultiplicity

namespace OAI

/-! The constrained free core conditions give exactly the certified H determinant. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

/-- The free core has zero first real channel and a regular harmonic second channel. -/
noncomputable def spectralFreeCoreBoundary (ell : ℕ) (r : ℝ) (U : E₄) : Fin 2 → ℂ :=
  ![U.1.1+U.2.1,U.1.2-U.2.2-(ell : ℂ)/(r : ℂ)*(U.1.1-U.2.1)]

theorem spectralFreeCoreBoundary_determinant (ell : ℕ) (r : ℝ)
    (x a b : ℂ) (u v : Fin 2 → ℂ) :
    matchingColumnDeterminant
      (spectralFreeCoreBoundary ell r
        ((a*u 0,a/(r : ℂ)*((ell : ℂ)*u 0-2*x*u 1)),0))
      (spectralFreeCoreBoundary ell r
        (0,(b*v 0,b/(r : ℂ)*((ell : ℂ)*v 0+2*x*v 1))))=
      (-2*x*a*b/(r : ℂ))*matchingColumnDeterminant u v := by
  simp only [matchingColumnDeterminant,spectralFreeCoreBoundary,
    Matrix.cons_val_zero,Matrix.cons_val_one,Prod.fst_zero,Prod.snd_zero]
  ring

theorem spectralFreeCoreBoundary_H_zero_iff (ell : ℕ) (qp qm : ℂ)
    (hqp : -1 < qp.re) (hqm : -1 < qm.re) (r : ℝ) (hr : 0 < r) :
    let U := spectralPhysicalJet ((ell : ℂ)-2*qp) (spectralFreeSlowJet qp (ell+6)) r
    let V := spectralPhysicalJet ((ell : ℂ)-2*qm)
      (fun t => (spectralFreeSecondColumn ell qm t).2) r
    let x := radialFreeSlowArgument (Real.log r)
    matchingColumnDeterminant (spectralFreeCoreBoundary ell r (U,0))
      (spectralFreeCoreBoundary ell r (0,V))=0 ↔
      matchingColumnDeterminant (slowBoundaryColumn qp (ell+6) (-x))
        (slowBoundaryColumn qm (ell+6) x)=0 := by
  dsimp only
  obtain ⟨ha,hu⟩ := spectralFreeAngularPhysical_eq_boundaryColumn ell qp hqp r
  obtain ⟨hb,hv⟩ := spectralFreeSecondPhysical_eq_boundaryColumn ell qm hqm r
  rw [hu,hv,spectralFreeCoreBoundary_determinant]
  have hfac : -2*radialFreeSlowArgument (Real.log r)*
      (Complex.exp (((ell : ℂ)-2*qp)*(Real.log r : ℂ))*
        radialFreeSlowArgument (Real.log r)^qp)*
      star (Complex.exp (((ell : ℂ)-2*star qm)*(Real.log r : ℂ))*
        radialFreeSlowArgument (Real.log r)^star qm)/(r : ℂ) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (radialFreeSlowArgument_ne_zero _)) ha) hb) (Complex.ofReal_ne_zero.mpr hr.ne')
  exact mul_eq_zero.trans (or_iff_right hfac)

theorem radialFreeSlowArgument_log (r : ℝ) (hr : 0 < r) :
    radialFreeSlowArgument (Real.log r)=-Complex.I*(r^2/4 : ℝ) := by
  have he : Real.exp (2*Real.log r)=r^2 := by
    rw [two_mul,Real.exp_add,Real.exp_log hr]
    ring
  rw [radialFreeSlowArgument,he]

theorem spectralFreeCoreBoundary_zero_iff_spectralSlowDeterminant
    (ell : ℕ) (b r : ℝ) (lam : ℂ) (hr : 0 < r)
    (hlam : -(1/32 : ℝ) ≤ lam.re) :
    let qp := spectralQ ell 1 b lam
    let qm := spectralQ ell (-1) b lam
    let U := spectralPhysicalJet ((ell : ℂ)-2*qp) (spectralFreeSlowJet qp (ell+6)) r
    let V := spectralPhysicalJet ((ell : ℂ)-2*qm)
      (fun t => (spectralFreeSecondColumn ell qm t).2) r
    matchingColumnDeterminant (spectralFreeCoreBoundary ell r (U,0))
      (spectralFreeCoreBoundary ell r (0,V))=0 ↔
        spectralSlowDeterminant ell b (r^2/4) lam=0 := by
  have hq (h : ℝ) : -1 < (spectralQ ell h b lam).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have he := spectralFreeCoreBoundary_H_zero_iff ell (spectralQ ell 1 b lam)
    (spectralQ ell (-1) b lam) (hq 1) (hq (-1)) r hr
  simpa only [radialFreeSlowArgument_log r hr,neg_mul,neg_neg,spectralSlowDeterminant] using he

end DefocusingNLS

end OAI

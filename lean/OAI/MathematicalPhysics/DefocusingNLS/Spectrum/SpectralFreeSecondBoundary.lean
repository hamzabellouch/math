import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSlowBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSecondColumn
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowConjugation

namespace OAI

/-! The second physical free column has the opposite imaginary H argument. -/

namespace DefocusingNLS

theorem spectralPhysicalJet_star (ν : ℂ) (Y : ℝ → ℂ × ℂ) (r : ℝ) :
    spectralPhysicalJet (star ν) (fun t => star (Y t)) r=star (spectralPhysicalJet ν Y r) := by
  apply Prod.ext <;>
    simp [spectralPhysicalJet,Prod.star_def,star_add,star_mul,star_div₀,
      ← Complex.exp_conj]
  all_goals ring

theorem radialFreeSlowArgument_star (t : ℝ) :
    star (radialFreeSlowArgument t)=-radialFreeSlowArgument t := by
  apply Complex.ext
  · simp [radialFreeSlowArgument_re]
  · simp

theorem spectralFreeSecondPhysical_eq_boundaryColumn (ell : ℕ) (q : ℂ)
    (hq : -1 < q.re) (r : ℝ) :
    let x := radialFreeSlowArgument (Real.log r)
    let a := star (Complex.exp (((ell : ℂ)-2*star q)*(Real.log r : ℂ))*x^(star q))
    let u := slowBoundaryColumn q (ell+6) x
    a ≠ 0 ∧
      spectralPhysicalJet ((ell : ℂ)-2*q) (fun t => (spectralFreeSecondColumn ell q t).2) r=
        (a*u 0,a/(r : ℂ)*((ell : ℂ)*u 0+2*x*u 1)) := by
  dsimp only
  let x := radialFreeSlowArgument (Real.log r)
  let A := Complex.exp (((ell : ℂ)-2*star q)*(Real.log r : ℂ))*x^(star q)
  let u := slowBoundaryColumn (star q) (ell+6) (-x)
  let v := slowBoundaryColumn q (ell+6) x
  have hq' : -1 < (star q).re := by simpa only [Complex.star_def,Complex.conj_re] using hq
  have hh := spectralFreeAngularPhysical_eq_boundaryColumn ell (star q) hq' r
  have hxs : star x=-x := radialFreeSlowArgument_star _
  have hu := slowBoundaryColumn_star (star q) (ell+6) (-x)
    (by simpa only [neg_neg] using radialFreeSlowArgument_mem_slit (Real.log r))
  have hpar : star ((ell : ℂ)-2*star q)=(ell : ℂ)-2*q := by
    simp [star_sub,star_mul]
    ring
  refine ⟨star_ne_zero.mpr hh.1,?_⟩
  have hu' : star u=v := by
    simpa only [star_star,star_neg,hxs,neg_neg] using hu
  have h0 := congrFun hu' 0
  have h1 := congrFun hu' 1
  change star (u 0)=v 0 at h0
  change star (u 1)=v 1 at h1
  have hrstar : star (r : ℂ)=(r : ℂ) := Complex.conj_ofReal r
  calc
    _ = star (spectralPhysicalJet ((ell : ℂ)-2*star q)
        (spectralFreeSlowJet (star q) (ell+6)) r) := by
      rw [← spectralPhysicalJet_star,hpar]
      rfl
    _ = star (A*u 0,A/(r : ℂ)*((ell : ℂ)*u 0-2*x*u 1)) := congrArg star hh.2
    _ = _ := by
      apply Prod.ext
      · change star (A*u 0)=star A*v 0
        rw [star_mul,h0]
        ring
      · change star (A/(r : ℂ)*((ell : ℂ)*u 0-2*x*u 1))=
          star A/(r : ℂ)*((ell : ℂ)*v 0+2*x*v 1)
        simp only [star_mul,star_div₀,star_sub,star_natCast,star_ofNat,h0,h1,hxs,hrstar]
        ring

end DefocusingNLS

end OAI

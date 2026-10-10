import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSlowJet
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.AnalyticMatchingColumn

namespace OAI

/-! The physical free column and the H/H' column used by the certified determinant. -/

namespace DefocusingNLS

theorem spectralFreeAngularPhysical_eq_H_jet (ell : ℕ) (q : ℂ) (r : ℝ) :
    let x := radialFreeSlowArgument (Real.log r)
    let a := Complex.exp (((ell : ℂ)-2*q)*(Real.log r : ℂ))*x^q
    spectralPhysicalJet ((ell : ℂ)-2*q) (spectralFreeSlowJet q (ell+6)) r=
      (a*regularizedSlowSolution q (ell+6) x,
       a/(r : ℂ)*((ell : ℂ)*regularizedSlowSolution q (ell+6) x+
         2*x*deriv (regularizedSlowSolution q (ell+6)) x)) := by
  dsimp only
  let x := radialFreeSlowArgument (Real.log r)
  have hx : x ≠ 0 := radialFreeSlowArgument_ne_zero _
  have he : x^(q-1)*x=x^q := by
    calc
      _ = x^(q-1)*x^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = x^((q-1)+1) := (Complex.cpow_add _ _ hx).symm
      _ = _ := by congr 1; ring
  apply Prod.ext
  · dsimp only [spectralPhysicalJet,spectralFreeSlowJet,normalizedSlowSolution]
    ring
  · change Complex.exp (((ell : ℂ)-2*q)*(Real.log r : ℂ))/(r : ℂ)*
        (((ell : ℂ)-2*q)*(x^q*regularizedSlowSolution q (ell+6) x)+
          2*x*(q*x^(q-1)*regularizedSlowSolution q (ell+6) x+
            x^q*deriv (regularizedSlowSolution q (ell+6)) x)) = _
    linear_combination 2*Complex.exp (((ell : ℂ)-2*q)*(Real.log r : ℂ))/(r : ℂ)*
      q*regularizedSlowSolution q (ell+6) x*he

theorem spectralFreeAngularPhysical_eq_boundaryColumn (ell : ℕ) (q : ℂ)
    (hq : -1 < q.re) (r : ℝ) :
    let x := radialFreeSlowArgument (Real.log r)
    let a := Complex.exp (((ell : ℂ)-2*q)*(Real.log r : ℂ))*x^q
    let u := slowBoundaryColumn q (ell+6) (-x)
    a ≠ 0 ∧
      spectralPhysicalJet ((ell : ℂ)-2*q) (spectralFreeSlowJet q (ell+6)) r=
        (a*u 0,a/(r : ℂ)*((ell : ℂ)*u 0-2*x*u 1)) := by
  dsimp only
  let x := radialFreeSlowArgument (Real.log r)
  have hx : x ≠ 0 := radialFreeSlowArgument_ne_zero _
  have hrx : x.re=0 := radialFreeSlowArgument_re _
  have hix : x.im ≠ 0 := by
    intro h
    exact hx (Complex.ext hrx h)
  have hu := slowBoundaryColumn_eq_jet q (ell+6) (-x) hq (by simp [hrx])
    (by simpa only [Complex.neg_im,neg_ne_zero] using hix)
  change _ ≠ 0 ∧ _
  constructor
  · exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.cpow_ne_zero_iff.mpr (Or.inl hx))
  · rw [spectralFreeAngularPhysical_eq_H_jet]
    rw [hu]
    simp only [neg_neg,Matrix.cons_val_zero,Matrix.cons_val_one]
    apply Prod.ext
    · rfl
    · ring

end DefocusingNLS

end OAI

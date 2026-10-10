import OAI.Probability.InvariantIsing.Cavity.CavitySchurLogDeterminant

namespace OAI

/-! The scalar derivative in `cav:determinant-derivative` after exact
finite multiplicity evaluation of the matrix determinant. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavitySpectralLogDet {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (x : ℝ) : ℝ :=
  Real.log x + ∑ a, rho a * Real.log (finiteInverse rho lam hrho hsum x - lam a)

theorem hasDerivAt_cavitySpectralLogDet {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (cavitySpectralLogDet rho lam hrho hsum)
      (x * deriv (finiteR rho lam hrho hsum) x) x := by
  let b := finiteInverse rho lam hrho hsum x
  let v := -1 / finiteSecondResolvent rho lam b
  have hs := finiteInverse_spec rho lam hrho hsum hx
  have hv : HasDerivAt (finiteInverse rho lam hrho hsum) v x :=
    (hasStrictDerivAt_finiteInverse rho lam hrho hsum hx).hasDerivAt
  have hterm (a : Fin m) : HasDerivAt
      (fun z => rho a * Real.log (finiteInverse rho lam hrho hsum z - lam a))
      (rho a * (v / (b - lam a))) x := by
    exact ((hv.sub_const (lam a)).log (ne_of_gt (sub_pos.mpr (hs.1 a)))).const_mul (rho a)
  have hsumderiv := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hterm a)
  have hlog := (Real.hasDerivAt_log hx.ne').add hsumderiv
  have hsumvalue : (∑ a, rho a * (v / (b - lam a))) = v * x := by
    calc
      _ = v * finiteResolvent rho lam b := by
        rw [finiteResolvent, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = v * x := by rw [hs.2]
  have hr := (hasStrictDerivAt_finiteR rho lam hrho hsum hx).hasDerivAt.deriv
  have he : x⁻¹ + (∑ a, rho a * (v / (b - lam a))) =
      x * deriv (finiteR rho lam hrho hsum) x := by
    rw [hsumvalue, hr]
    change x⁻¹ + v * x = x * (v + 1 / x ^ 2)
    field_simp [hx.ne']
    ring
  convert! hlog using 1
  exact he.symm

end InvariantIsing

end

end OAI

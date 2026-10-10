import OAI.AlgebraicGeometry.AbhyankarSathaye.Fiber

namespace OAI

/-!
# Explicit coordinates on the zero fiber

The inverse isomorphism sends `X`, `Y`, and `T` to `x + s³`, `y - s²`,
and `α * u + β * (v + u * w)`. The forward isomorphism is given by the
polynomials `freeH`, `freeU`, `freeV`, and `freeW`, with variables ordered `X, Y, T`.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial Presentation

def fiberParameter : R := parameter (Alpha x s) (Beta x y s) u v w

theorem fiberEquiv_symm_X0 : fiberEquiv.symm (X 0) = dmap shiftX := by
  change toOriginal (Lifting.backward hB xB yB sB (Alpha xB sB) (Beta xB yB sB)
    (Polynomial.map (Plane.backward ℂ).toRingHom (flattenPlane.symm (X 0)))) = _
  rw [flattenPlane_symm_X0, Polynomial.map_C]
  have he : (Plane.backward ℂ).toRingHom (X 0) = xB+sB^3 := by simp [Plane.backward]
  rw [he]
  simp only [Lifting.backward, Polynomial.aeval_C]
  change toOriginal (lcoef (xB+sB^3)) = _
  simp [auxValues, shiftX]

theorem fiberEquiv_symm_X1 : fiberEquiv.symm (X 1) = dmap shiftY := by
  change toOriginal (Lifting.backward hB xB yB sB (Alpha xB sB) (Beta xB yB sB)
    (Polynomial.map (Plane.backward ℂ).toRingHom (flattenPlane.symm (X 1)))) = _
  rw [flattenPlane_symm_X1, Polynomial.map_C]
  have he : (Plane.backward ℂ).toRingHom (X 1) = yB-sB^2 := by simp [Plane.backward]
  rw [he]
  simp only [Lifting.backward, Polynomial.aeval_C]
  change toOriginal (lcoef (yB-sB^2)) = _
  simp [auxValues, shiftY]

theorem fiberEquiv_symm_X2 : fiberEquiv.symm (X 2) = dmap fiberParameter := by
  change toOriginal (Lifting.backward hB xB yB sB (Alpha xB sB) (Beta xB yB sB)
    (Polynomial.map (Plane.backward ℂ).toRingHom (flattenPlane.symm (X 2)))) = _
  rw [flattenPlane_symm_X2, Polynomial.map_X]
  simp only [Lifting.backward, Polynomial.aeval_X]
  change toOriginal (parameter (lcoef (Alpha xB sB)) (lcoef (Beta xB yB sB))
    (lvar 0) (lvar 1) (lvar 2)) = _
  simp [fiberParameter, auxValues, liftValues]

def freeS : MvPolynomial (Fin 3) ℂ := X 0^2+X 1^3
def freeX : MvPolynomial (Fin 3) ℂ := X 0-freeS^3
def freeY : MvPolynomial (Fin 3) ℂ := X 1+freeS^2
def freeH : MvPolynomial (Fin 3) ℂ := 1+P freeX freeY freeS
def freeAlpha : MvPolynomial (Fin 3) ℂ := Alpha freeX freeS
def freeBeta : MvPolynomial (Fin 3) ℂ := Beta freeX freeY freeS
def freeU : MvPolynomial (Fin 3) ℂ := inverseU freeH freeX freeBeta (X 2)
def freeG : MvPolynomial (Fin 3) ℂ := inverseG freeX freeY freeAlpha (X 2)
def freeW : MvPolynomial (Fin 3) ℂ := inverseW freeH freeY freeS freeAlpha freeBeta freeU freeG
def freeV : MvPolynomial (Fin 3) ℂ := inverseV freeU freeG freeW

@[simp] theorem symm_freeS : fiberEquiv.symm freeS = dmap s := by
  have ha := congrArg dmap ambient
  simp only [map_add, map_pow, map_mul, map_one, dmap_F, add_zero, mul_one] at ha
  simpa [freeS, fiberEquiv_symm_X0, fiberEquiv_symm_X1] using ha

@[simp] theorem symm_freeX : fiberEquiv.symm freeX = dmap x := by
  simp [freeX, fiberEquiv_symm_X0, shiftX]

@[simp] theorem symm_freeY : fiberEquiv.symm freeY = dmap y := by
  simp [freeY, fiberEquiv_symm_X1, shiftY]

@[simp] theorem symm_freeH : fiberEquiv.symm freeH = dmap h := by
  have hf : dmap h-dmap p-1 = 0 := by simpa [F] using dmap_F
  have hh : 1+dmap p = dmap h := by
    calc
      _ = dmap h-(dmap h-dmap p-1) := by ring
      _ = dmap h := by rw [hf, sub_zero]
  simpa [freeH, p] using hh

@[simp] theorem symm_freeAlpha : fiberEquiv.symm freeAlpha = dmap (Alpha x s) := by
  simp [freeAlpha]
@[simp] theorem symm_freeBeta : fiberEquiv.symm freeBeta = dmap (Beta x y s) := by
  simp [freeBeta]

theorem inverse_formulas_in_quotient : fiberEquiv.symm freeU = dmap u ∧
    fiberEquiv.symm freeV = dmap v ∧ fiberEquiv.symm freeW = dmap w := by
  have hc : x^2+y^3-s*h = 0 := by rw [cusp]; ring
  have hh : h-1-P x y s = F := by unfold F p; ring
  have hb : dmap (Alpha x s)*dmap h+dmap (Beta x y s)*dmap y = 1 := by
    have he := congrArg dmap (bezout_certificate h x y s)
    rw [hc, hh] at he
    simpa [p, dmap_F, ← sub_eq_zero] using he
  have hx : (dmap u)^3+dmap h*dmap v = dmap x := by simp [x]
  have hy : -(dmap u)^2+dmap h*dmap w = dmap y := by simp [y]
  have hs : S (dmap h) (dmap u) (dmap v) (dmap w) = dmap s := by simp [s]
  have hr := original_reconstruction (dmap h) (dmap x) (dmap y) (dmap s)
    (dmap (Alpha x s)) (dmap (Beta x y s)) (dmap u) (dmap v) (dmap w) hb hx hy hs
  simpa [freeU, freeV, freeW, freeG, fiberEquiv_symm_X2, fiberParameter] using hr

theorem explicit_inverse_formulas :
    fiberEquiv (dmap h) = freeH ∧ fiberEquiv (dmap u) = freeU ∧
    fiberEquiv (dmap v) = freeV ∧ fiberEquiv (dmap w) = freeW := by
  obtain ⟨hu, hv, hw⟩ := inverse_formulas_in_quotient
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (fiberEquiv.apply_symm_apply freeH) ▸ congrArg fiberEquiv symm_freeH.symm
  · exact (fiberEquiv.apply_symm_apply freeU) ▸ congrArg fiberEquiv hu.symm
  · exact (fiberEquiv.apply_symm_apply freeV) ▸ congrArg fiberEquiv hv.symm
  · exact (fiberEquiv.apply_symm_apply freeW) ▸ congrArg fiberEquiv hw.symm

end AbhyankarSathaye

end

end OAI

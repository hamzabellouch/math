import OAI.LinearAlgebra.CirculantHadamard.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

namespace OAI

universe uG uR

namespace CirculantHadamard
namespace BinaryCoefficients

def halfSum (x y : ℤ) : ℤ := (x + y) / 2

def halfDiff (x y : ℤ) : ℤ := (x - y) / 2

def signOffset (x : ℤ) : ℤ := (x - 1) / 2

theorem two_halfSum {x y : ℤ} (hx : IsSign x) (hy : IsSign y) :
    2 * halfSum x y = x + y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [halfSum]

theorem two_halfDiff {x y : ℤ} (hx : IsSign x) (hy : IsSign y) :
    2 * halfDiff x y = x - y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [halfDiff]

theorem halfDiff_eq {x y : ℤ} (hx : IsSign x) (hy : IsSign y) :
    halfDiff x y = halfSum x y - y := by
  linarith [two_halfSum hx hy, two_halfDiff hx hy]

theorem two_signOffset {x : ℤ} (hx : IsSign x) :
    2 * signOffset x = x - 1 := by
  rcases hx with rfl | rfl <;> norm_num [signOffset]

theorem sign_eq_one_add {x : ℤ} (hx : IsSign x) :
    x = 1 + 2 * signOffset x := by
  linarith [two_signOffset hx]

variable {G : Type uG}

/-- The canonical coefficient map, with no change to the index. -/
noncomputable def castCoeffs {R : Type uR} [Ring R] (f : G →₀ ℤ) : G →₀ R :=
  Finsupp.mapRange (fun z : ℤ => (z : R)) (by simp) f

@[simp] theorem castCoeffs_apply {R : Type uR} [Ring R] (f : G →₀ ℤ) (x : G) :
    castCoeffs (R := R) f x = (f x : R) := rfl

noncomputable def complexify (f : G →₀ ℤ) : G →₀ ℂ := castCoeffs f

@[simp] theorem complexify_apply (f : G →₀ ℤ) (x : G) :
    complexify f x = (f x : ℂ) := rfl

theorem complexify_add (f h : G →₀ ℤ) :
    complexify (f + h) = complexify f + complexify h := by
  ext x
  simp

theorem complexify_sub (f h : G →₀ ℤ) :
    complexify (f - h) = complexify f - complexify h := by
  ext x
  simp

theorem complexify_int_smul (z : ℤ) (f : G →₀ ℤ) :
    complexify (z • f) = (z : ℂ) • complexify f := by
  ext x
  simp [Finsupp.smul_apply, smul_eq_mul]

/-- Integer real and imaginary parts interpreted in any coefficient ring.
The linear identities do not require an equation such as `i^2 = -1`. -/
noncomputable def liftPair {R : Type uR} [CommRing R] (i : R) (f h : G →₀ ℤ) : G →₀ R :=
  castCoeffs f + i • castCoeffs h

variable [Finite G]

noncomputable def ofCoeffs {R : Type uR} [Zero R] (f : G → R) : G →₀ R :=
  Finsupp.equivFunOnFinite.symm f

@[simp] theorem ofCoeffs_apply {R : Type uR} [Zero R] (f : G → R) (x : G) :
    ofCoeffs f x = f x := rfl

/-- Literal sign hypotheses for the four blocks, without a norm premise. -/
def Signs (H : Fin 4 → (G →₀ ℤ)) : Prop := ∀ j x, IsSign (H j x)

noncomputable def a (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfSum (H 0 x) (H 2 x)

noncomputable def b (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfSum (H 1 x) (H 3 x)

noncomputable def c (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ := a H + b H

noncomputable def d (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ := a H - b H

noncomputable def gReal (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfDiff (H 0 x) (H 2 x)

noncomputable def gImag (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfDiff (H 1 x) (H 3 x)

noncomputable def gOver {R : Type uR} [CommRing R] (i : R)
    (H : Fin 4 → (G →₀ ℤ)) : G →₀ R := liftPair i (gReal H) (gImag H)

noncomputable def g (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℂ := gOver Complex.I H

noncomputable def UReal (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => signOffset (H 2 x)

noncomputable def UImag (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => signOffset (H 3 x)

noncomputable def UOver {R : Type uR} [CommRing R] (i : R)
    (H : Fin 4 → (G →₀ ℤ)) : G →₀ R := liftPair i (UReal H) (UImag H)

noncomputable def U (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℂ := UOver Complex.I H

/-- This is the sum of all group elements (every coefficient is one),
not the scalar one in a convolution ring. -/
noncomputable def JOver (R : Type uR) [CommRing R] : G →₀ R := ofCoeffs fun _ => 1

@[simp] theorem JOver_apply {R : Type uR} [CommRing R] (x : G) :
    (JOver R : G →₀ R) x = 1 := rfl

noncomputable def J : G →₀ ℂ := JOver ℂ

@[simp] theorem J_apply (x : G) : (J : G →₀ ℂ) x = 1 := rfl

theorem two_a {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • a H = H 0 + H 2 := by
  ext x
  change 2 * halfSum (H 0 x) (H 2 x) = H 0 x + H 2 x
  exact two_halfSum (hH 0 x) (hH 2 x)

theorem two_b {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • b H = H 1 + H 3 := by
  ext x
  change 2 * halfSum (H 1 x) (H 3 x) = H 1 x + H 3 x
  exact two_halfSum (hH 1 x) (hH 3 x)

theorem two_c {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • c H = H 0 + H 1 + H 2 + H 3 := by
  rw [c, smul_add, two_a hH, two_b hH]
  abel

theorem two_d {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • d H = H 0 - H 1 + H 2 - H 3 := by
  rw [d, smul_sub, two_a hH, two_b hH]
  abel

theorem gOver_eq_ab {R : Type uR} [CommRing R] (i : R)
    {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    gOver i H = castCoeffs (a H) + i • castCoeffs (b H) -
      castCoeffs (H 2) - i • castCoeffs (H 3) := by
  ext x
  simp only [gOver, liftPair, gReal, gImag, a, b, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, castCoeffs_apply, ofCoeffs_apply, smul_eq_mul]
  rw [halfDiff_eq (hH 0 x) (hH 2 x), halfDiff_eq (hH 1 x) (hH 3 x)]
  push_cast
  ring

theorem two_gOver {R : Type uR} [CommRing R] (i : R)
    {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : R) • gOver i H = castCoeffs (H 0) + i • castCoeffs (H 1) -
      castCoeffs (H 2) - i • castCoeffs (H 3) := by
  ext x
  have h0 := congrArg (fun z : ℤ => (z : R)) (two_halfDiff (hH 0 x) (hH 2 x))
  have h1 := congrArg (fun z : ℤ => (z : R)) (two_halfDiff (hH 1 x) (hH 3 x))
  push_cast at h0 h1
  simp only [gOver, liftPair, gReal, gImag, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, castCoeffs_apply, ofCoeffs_apply, smul_eq_mul]
  calc
    _ = 2 * (halfDiff (H 0 x) (H 2 x) : R) +
        i * (2 * (halfDiff (H 1 x) (H 3 x) : R)) := by ring
    _ = _ := by rw [h0, h1]; ring

/-- The binary identity with an explicitly constructed integral-pair `U`. -/
theorem binary_identity_over {R : Type uR} [CommRing R] (i : R)
    {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    castCoeffs (H 2) + i • castCoeffs (H 3) =
      (1 + i) • (JOver R : G →₀ R) + (2 : R) • UOver i H := by
  ext x
  have h2 := congrArg (fun z : ℤ => (z : R)) (sign_eq_one_add (hH 2 x))
  have h3 := congrArg (fun z : ℤ => (z : R)) (sign_eq_one_add (hH 3 x))
  push_cast at h2 h3
  simp only [UOver, liftPair, UReal, UImag, Finsupp.add_apply, Finsupp.smul_apply,
    castCoeffs_apply, ofCoeffs_apply, JOver_apply, smul_eq_mul]
  rw [h2, h3]
  ring

theorem g_eq_ab {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    g H = complexify (a H) + Complex.I • complexify (b H) -
      complexify (H 2) - Complex.I • complexify (H 3) :=
  gOver_eq_ab Complex.I hH

theorem two_g {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℂ) • g H = complexify (H 0) + Complex.I • complexify (H 1) -
      complexify (H 2) - Complex.I • complexify (H 3) :=
  two_gOver Complex.I hH

theorem binary_identity {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    complexify (H 2) + Complex.I • complexify (H 3) =
      (1 + Complex.I) • (J : G →₀ ℂ) + (2 : ℂ) • U H :=
  binary_identity_over Complex.I hH

end BinaryCoefficients
end CirculantHadamard

end OAI

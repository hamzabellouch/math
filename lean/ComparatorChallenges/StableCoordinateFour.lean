import Mathlib

namespace OAI

namespace StableCoordinate

open MvPolynomial

abbrev R (n : ℕ) := MvPolynomial (Fin n) ℂ

noncomputable def Q : R 4 :=
  X 1 ^ 2 - X 3 ^ 2 + X 0 * X 2

noncomputable def f : R 4 :=
  X 0 - 2 * Q * (Q * (X 1 + X 3) + X 0 * X 3)

def IsCoordinate {n : ℕ} (hn : 0 < n) (g : R n) : Prop :=
  ∃ φ : R n ≃ₐ[ℂ] R n, φ g = X ⟨0, hn⟩

noncomputable def stabilize : R 4 →ₐ[ℂ] R 5 :=
  rename (Fin.castSucc : Fin 4 → Fin 5)

def IsOneStableCoordinate (g : R 4) : Prop :=
  ∃ φ : R 5 ≃ₐ[ℂ] R 5, φ (stabilize g) = X 0

noncomputable def fiberIdeal (t : ℂ) : Ideal (R 4) :=
  Ideal.span ({f - C t} : Set (R 4))

abbrev FiberRing (t : ℂ) := R 4 ⧸ fiberIdeal t

def IsAffineThreeSpaceFiber (t : ℂ) : Prop :=
  Nonempty (FiberRing t ≃ₐ[ℂ] R 3)

def IsRectifiableFiber (t : ℂ) : Prop :=
  ∃ φ : R 4 ≃ₐ[ℂ] R 4,
    Ideal.map φ.toRingHom (fiberIdeal t) = Ideal.span ({X 0} : Set (R 4))

def PolynomialPackage : Prop :=
  f.totalDegree = 5 ∧
  IsOneStableCoordinate f ∧
  ¬ IsCoordinate (by decide : 0 < 4) f

def FiberPackage : Prop :=
  ∀ t : ℂ, IsAffineThreeSpaceFiber t ∧ ¬ IsRectifiableFiber t

def PrincipalPackage : Prop := PolynomialPackage ∧ FiberPackage

/-- The explicit degree-five stable noncoordinate and its nonrectifiable affine-space fibers. -/
theorem principal_package : PrincipalPackage := by
  sorry

end StableCoordinate

end OAI

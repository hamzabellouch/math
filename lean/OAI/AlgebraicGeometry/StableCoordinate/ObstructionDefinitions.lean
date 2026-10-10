import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Derivation.Basic

namespace OAI

/-!
# Exact rings in the noncoordinate obstruction

These transparent definitions fix the independent variables and relations in
Sections 2–5 of the paper. The relations define the quadric and determinant
rings used to obstruct polynomial coordinateness.
-/

namespace StableCoordinate.Obstruction

open MvPolynomial

abbrev P (k : Type*) [CommRing k] (n : ℕ) := MvPolynomial (Fin n) k

variable (k : Type*) [CommRing k]

/-- The source's determinant invariant in `k[p,s,u,F,J]`. -/
noncomputable def xP : P k 5 := X 1 ^ 2 - X 2 ^ 2 + X 0 * X 3

/-- Highest weighted part of the source hypersurface equation. -/
noncomputable def Hstar : P k 5 :=
  xP k ^ 2 * X 3 - (1 + 2 * X 1 * xP k) * X 4 - X 0 * X 4 ^ 2

noncomputable def H : P k 5 := Hstar k - X 2
noncomputable def idealA : Ideal (P k 5) := Ideal.span {H k}
noncomputable def idealG : Ideal (P k 5) := Ideal.span {Hstar k}
abbrev A := P k 5 ⧸ idealA k
abbrev G := P k 5 ⧸ idealG k

/-- Generator images of the original polynomial presentation. -/
noncomputable def aX (i : Fin 5) : A k := Ideal.Quotient.mk (idealA k) (X i)
/-- Generator images of the weighted degeneration presentation. -/
noncomputable def gX (i : Fin 5) : G k := Ideal.Quotient.mk (idealG k) (X i)

noncomputable def quadricRelation : P k 4 := X 0 * X 1 - X 2 * (X 2 + 1)
noncomputable def idealB : Ideal (P k 4) := Ideal.span {quadricRelation k}
abbrev B := P k 4 ⧸ idealB k
/-- Quadric variables `x,y,z,u`, in this order. -/
noncomputable def bX (i : Fin 4) : B k := Ideal.Quotient.mk (idealB k) (X i)

noncomputable def determinantRelation : P k 5 := X 0 * X 3 - X 2 * X 1 - 1
noncomputable def idealC : Ideal (P k 5) := Ideal.span {determinantRelation k}
abbrev C := P k 5 ⧸ idealC k
/-- Determinant-ring variables `a,d,b,c,u`, in this order. -/
noncomputable def cX (i : Fin 5) : C k := Ideal.Quotient.mk (idealC k) (X i)

noncomputable def sB : B k := bX k 1 - bX k 0 * (bX k 0 + bX k 3 ^ 2)
noncomputable def f0 : B k := bX k 0 - sB k ^ 2 + bX k 3 ^ 2
noncomputable def g0 : B k := bX k 2 - sB k * bX k 0
noncomputable def I : Ideal (B k) := Ideal.span {f0 k, g0 k}
noncomputable def v : C k := cX k 0 ^ 3 * cX k 2 + cX k 0 ^ 2 * cX k 4 ^ 2 - cX k 1 ^ 2

/-- The exact negative integer weights on the presentation variables. -/
def presentationWeight : Fin 5 → ℤ := ![-1, 0, 0, 1, 1]
/-- Fiber weights on `a,d,b,c,u`; these encode fiber scaling. -/
def fiberWeight : Fin 5 → ℤ := ![1, 1, -1, -1, 0]
/-- The second, auxiliary grading used only in the rigidity argument. -/
def auxiliaryWeight : Fin 5 → ℤ := ![0, 1, -1, 0, 1]

@[simp] theorem mk_H : Ideal.Quotient.mk (idealA k) (H k) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton (H k))

@[simp] theorem mk_Hstar : Ideal.Quotient.mk (idealG k) (Hstar k) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton (Hstar k))

theorem b_relation : bX k 0 * bX k 1 - bX k 2 * (bX k 2 + 1) = 0 := by
  have h : Ideal.Quotient.mk (idealB k) (quadricRelation k) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton (quadricRelation k))
  simpa [quadricRelation, bX] using h

theorem c_relation : cX k 0 * cX k 3 - cX k 2 * cX k 1 - 1 = 0 := by
  have h : Ideal.Quotient.mk (idealC k) (determinantRelation k) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton (determinantRelation k))
  simpa [determinantRelation, cX] using h

end StableCoordinate.Obstruction

end OAI

import OAI.AlgebraicGeometry.AbhyankarSathaye.Quotient
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# A polynomial presentation of the affine plane

The relations `h = 1 + P x y s` and `x² + y³ = h * s` give a polynomial
algebra with coordinates `x + s³` and `y - s²`. The auxiliary variables are
ordered as `h, x, y, s`.
-/

noncomputable section
namespace AbhyankarSathaye.Plane
open MvPolynomial

variable (K : Type*) [CommRing K]

def relH : MvPolynomial (Fin 4) K := X 0-1-P (X 1) (X 2) (X 3)
def relCusp : MvPolynomial (Fin 4) K := X 1^2+X 2^3-X 3*X 0
def ideal : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {relH K, relCusp K}
abbrev Q := MvPolynomial (Fin 4) K ⧸ ideal K
def qmap : MvPolynomial (Fin 4) K →ₐ[K] Q K := Ideal.Quotient.mkₐ K (ideal K)
def qvar (i : Fin 4) : Q K := qmap K (X i)

theorem relation_h : qvar K 0 = 1+P (qvar K 1) (qvar K 2) (qvar K 3) := by
  have hz : qmap K (relH K) = 0 := quotient_pair_left (relH K) (relCusp K)
  have hh : qvar K 0-1-P (qvar K 1) (qvar K 2) (qvar K 3) = 0 := by
    simpa [relH, qvar] using hz
  calc
    _ = (qvar K 0-1-P (qvar K 1) (qvar K 2) (qvar K 3))+
        (1+P (qvar K 1) (qvar K 2) (qvar K 3)) := by ring
    _ = _ := by rw [hh, zero_add]

theorem relation_cusp : (qvar K 1)^2+(qvar K 2)^3 = qvar K 0*qvar K 3 := by
  have hz : qmap K (relCusp K) = 0 := quotient_pair_right (relH K) (relCusp K)
  have hh : (qvar K 1)^2+(qvar K 2)^3-qvar K 3*qvar K 0 = 0 := by
    simpa [relCusp, qvar] using hz
  simpa [mul_comm] using sub_eq_zero.mp hh

theorem shift_s : (qvar K 1+(qvar K 3)^3)^2+(qvar K 2-(qvar K 3)^2)^3 = qvar K 3 := by
  rw [shift_universal, relation_cusp, relation_h]
  ring

theorem bezout : Alpha (qvar K 1) (qvar K 3)*qvar K 0+
    Beta (qvar K 1) (qvar K 2) (qvar K 3)*qvar K 2 = 1 := by
  have he := bezout_certificate (qvar K 0) (qvar K 1) (qvar K 2) (qvar K 3)
  have hh : qvar K 0-1-P (qvar K 1) (qvar K 2) (qvar K 3) = 0 := by
    rw [relation_h]; ring
  have hc : (qvar K 1)^2+(qvar K 2)^3-qvar K 3*qvar K 0 = 0 := by
    rw [relation_cusp]; ring
  rw [hh, hc, mul_zero, mul_zero, sub_zero] at he
  exact sub_eq_zero.mp he

def planeS : MvPolynomial (Fin 2) K := X 0^2+X 1^3
def planeX : MvPolynomial (Fin 2) K := X 0-(planeS K)^3
def planeY : MvPolynomial (Fin 2) K := X 1+(planeS K)^2
def planeH : MvPolynomial (Fin 2) K := 1+P (planeX K) (planeY K) (planeS K)
def values : Fin 4 → MvPolynomial (Fin 2) K :=
  ![planeH K, planeX K, planeY K, planeS K]

theorem plane_cusp : (planeX K)^2+(planeY K)^3 = planeH K*planeS K := by
  have he := shift_universal (planeX K) (planeY K) (planeS K)
  have hx : planeX K+(planeS K)^3 = X 0 := by unfold planeX; ring
  have hy : planeY K-(planeS K)^2 = X 1 := by unfold planeY; ring
  rw [hx, hy] at he
  change planeS K = (planeX K)^2+(planeY K)^3-planeS K*P (planeX K) (planeY K) (planeS K) at he
  calc
    _ = (planeS K)+planeS K*P (planeX K) (planeY K) (planeS K) := by
      exact (eq_sub_iff_add_eq.mp he).symm
    _ = _ := by unfold planeH; ring

def forward : Q K →ₐ[K] MvPolynomial (Fin 2) K :=
  lift_pair (relH K) (relCusp K) (aeval (values K))
    (by simp [relH, values, planeH])
    (by simp [relCusp, values, plane_cusp, mul_comm])

@[simp] theorem forward_qvar (i : Fin 4) : forward K (qvar K i) = values K i := by
  change aeval (values K) (X i) = values K i
  exact aeval_X _ _

def backward : MvPolynomial (Fin 2) K →ₐ[K] Q K :=
  aeval ![qvar K 1+(qvar K 3)^3, qvar K 2-(qvar K 3)^2]

@[simp] theorem backward_planeS : backward K (planeS K) = qvar K 3 := by
  simpa [backward, planeS] using shift_s K

@[simp] theorem backward_planeX : backward K (planeX K) = qvar K 1 := by
  simp only [planeX, map_sub, map_pow, backward_planeS]
  simp [backward]

@[simp] theorem backward_planeY : backward K (planeY K) = qvar K 2 := by
  simp only [planeY, map_add, map_pow, backward_planeS]
  simp [backward]

@[simp] theorem backward_planeH : backward K (planeH K) = qvar K 0 := by
  simpa [planeH] using (relation_h K).symm

theorem forward_backward : (forward K).comp (backward K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [backward, values, planeX, planeY]

theorem backward_forward : (backward K).comp (forward K) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change backward K (forward K (qvar K i)) = qvar K i
  rw [forward_qvar]
  fin_cases i <;> simp [values]

def equivalence : Q K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  AlgEquiv.ofAlgHom (forward K) (backward K) (forward_backward K) (backward_forward K)

end AbhyankarSathaye.Plane

end

end OAI
